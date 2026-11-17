let
  nixpkgs = fetchTarball "https://github.com/NixOS/nixpkgs/tarball/nixos-24.11";
  pkgs = import nixpkgs { config = {}; overlays = []; };
in

pkgs.mkShell {
  packages = with pkgs; [
    elan
    python312Packages.coincurve
    python312Packages.typing-extensions
    python312Packages.pycryptodome
    python312Packages.eth-typing
    python312Packages.py-ecc
    python312Packages.cryptography
    pkgs.openssl
  ];
  shellHook = ''
    export LD_LIBRARY_PATH=${pkgs.openssl.out}/lib:$LD_LIBRARY_PATH
  '';
}
