#!/usr/bin/env bash
# Fetches the legacy EthereumTests suite used by `CONFORM_SUITE=legacy`:
#   - `BlockchainTests/` of ethereum/tests, and
#   - `Cancun/BlockchainTests/` of ethereum/legacytests,
# each at a pinned commit, laid out as the former `EthereumTests` submodule:
#   <target>/BlockchainTests/
#   <target>/LegacyTests/Cancun/BlockchainTests/
# Only those directories are downloaded. Git checks the content against the
# pinned commit hashes. Prints the target directory.
set -euo pipefail

if [[ $# -ne 0 ]]; then
  printf 'usage: %s\n' "$0" >&2
  exit 2
fi

tests_repo='https://github.com/ethereum/tests.git'
tests_commit='c67e485ff8b5be9abc8ad15345ec21aa22e290d9'
legacy_repo='https://github.com/ethereum/legacytests.git'
legacy_commit='1f581b8ccdc4c63acf5f2c5c1b155c690c32a8eb'

cache_root="${LEGACY_CACHE_DIR:-.cache/legacy-tests}"
target="${cache_root}/${tests_commit:0:12}-${legacy_commit:0:12}"

if [[ -f "${target}/.complete" ]]; then
  printf '%s\n' "${target}"
  exit 0
fi
if [[ -e "${target}" ]]; then
  printf 'incomplete target exists; move it aside and retry: %s\n' "${target}" >&2
  exit 1
fi

mkdir -p "${cache_root}"
work="$(mktemp -d "${cache_root}/fetch.XXXXXX")"
trap 'rm -rf "${work}"' EXIT

# fetch_directory <repo> <commit> <directory> <destination>
fetch_directory() {
  local repo="$1" commit="$2" directory="$3" destination="$4"
  local clone="${work}/clone"
  rm -rf "${clone}"
  git init --quiet "${clone}"
  git -C "${clone}" remote add origin "${repo}"
  git -C "${clone}" sparse-checkout set "${directory}"
  git -C "${clone}" fetch --quiet --depth 1 --filter=blob:none origin "${commit}"
  git -C "${clone}" -c advice.detachedHead=false checkout --quiet FETCH_HEAD
  local actual
  actual="$(git -C "${clone}" rev-parse HEAD)"
  if [[ "${actual}" != "${commit}" ]]; then
    printf 'commit mismatch for %s\nexpected: %s\nactual:   %s\n' \
      "${repo}" "${commit}" "${actual}" >&2
    exit 1
  fi
  mkdir -p "$(dirname "${destination}")"
  mv "${clone}/${directory}" "${destination}"
  rm -rf "${clone}"
}

staging="${work}/staging"
fetch_directory "${tests_repo}" "${tests_commit}" BlockchainTests \
  "${staging}/BlockchainTests"
fetch_directory "${legacy_repo}" "${legacy_commit}" Cancun/BlockchainTests \
  "${staging}/LegacyTests/Cancun/BlockchainTests"
cat > "${staging}/.complete" <<EOF
ethereum/tests ${tests_commit}
ethereum/legacytests ${legacy_commit}
EOF
mv "${staging}" "${target}"

printf '%s\n' "${target}"
