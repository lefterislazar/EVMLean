import Ethereum.Exception

/-!
# Expected exceptions

Whether the exception with which the model rejects a block is one that the
fixture expects. The model's exceptions print as the names that the fixtures
use, such as `TransactionException.INSUFFICIENT_ACCOUNT_FUNDS`.
-/

namespace Ethereum

namespace Conform

/--
The older fixtures filled by retesteth use `TR_*` and short labels for the
same condition as the `TransactionException.*` / `BlockException.*` names.
A reported exception is accepted when the fixture lists either form.
-/
def retestethExceptionNames (reported : String) : List String :=
  match reported with
  -- The execution specs raise one error for both intrinsic gas bounds
  -- (EIP-7623); some fixtures name it after the regular bound.
  | "TransactionException.INTRINSIC_GAS_BELOW_FLOOR_GAS_COST" =>
      ["TransactionException.INTRINSIC_GAS_TOO_LOW"]
  | "TransactionException.INTRINSIC_GAS_TOO_LOW" =>
      ["TR_IntrinsicGas", "IntrinsicGas", "TR_NoFundsOrGas"]
  | "TransactionException.INSUFFICIENT_ACCOUNT_FUNDS" =>
      ["TR_NoFunds", "TR_NoFundsX", "TR_NoFundsOrGas", "SenderNotEOAorNoCASH",
        "TR_FeeCapLessThanBlocksORNoFunds"]
  | "TransactionException.INSUFFICIENT_MAX_FEE_PER_GAS" =>
      ["TR_FeeCapLessThanBlocks", "TR_FeeCapLessThanBlocksORGasLimitReached",
        "TR_FeeCapLessThanBlocksORNoFunds"]
  | "TransactionException.GAS_ALLOWANCE_EXCEEDED" =>
      ["TR_GasLimitReached", "TR_FeeCapLessThanBlocksORGasLimitReached"]
  | "TransactionException.NONCE_IS_MAX" => ["TR_NonceHasMaxValue"]
  | "TransactionException.NONCE_MISMATCH_TOO_HIGH" => ["TR_NonceTooHigh"]
  | "TransactionException.NONCE_MISMATCH_TOO_LOW" => ["TR_NonceTooLow"]
  | "TransactionException.PRIORITY_GREATER_THAN_MAX_FEE_PER_GAS" => ["TR_TipGtFeeCap"]
  | "TransactionException.INITCODE_SIZE_EXCEEDED" => ["TR_InitCodeLimitExceeded"]
  | "TransactionException.TYPE_3_TX_ZERO_BLOBS" => ["TR_EMPTYBLOB"]
  | "TransactionException.TYPE_3_TX_CONTRACT_CREATION" => ["TR_BLOBCREATE"]
  | "TransactionException.TYPE_3_TX_INVALID_BLOB_VERSIONED_HASH" => ["TR_BLOBVERSION_INVALID"]
  | "TransactionException.TYPE_3_TX_BLOB_COUNT_EXCEEDED" => ["TR_BLOBLIST_OVERSIZE"]
  | "TransactionException.SENDER_NOT_EOA" => ["SenderNotEOA", "SenderNotEOAorNoCASH"]
  | "TransactionException.RLP_INVALID_VALUE" => ["TR_RLP_WRONGVALUE"]
  | "BlockException.IMPORT_IMPOSSIBLE_UNCLES_OVER_PARIS" => ["PostParisUncleHashIsNotEmpty"]
  | "BlockException.INVALID_GASLIMIT" => ["InvalidGasLimit", "InvalidGasLimit2"]
  | "BlockException.GASLIMIT_TOO_BIG" => ["InvalidGasLimit"]
  | "BlockException.INVALID_BLOCK_TIMESTAMP_OLDER_THAN_PARENT" => ["InvalidTimestampOlderParent"]
  | "BlockException.EXTRA_DATA_TOO_BIG" => ["ExtraDataTooBig"]
  | "BlockException.INVALID_WITHDRAWALS_ROOT" => ["InvalidWithdrawals"]
  | "BlockException.INVALID_BLOCK_NUMBER" => ["InvalidNumber"]
  | "BlockException.INVALID_STATE_ROOT" => ["InvalidStateRoot"]
  | "BlockException.INVALID_BASEFEE_PER_GAS" => ["1559BlockImportImpossible_BaseFeeWrong"]
  | "BlockException.GAS_USED_OVERFLOW" => ["TooMuchGasUsed"]
  | "BlockException.INVALID_RECEIPTS_ROOT" => ["InvalidReceiptsStateRoot"]
  | "BlockException.INVALID_TRANSACTIONS_ROOT" => ["InvalidTransactionsRoot"]
  | "BlockException.UNKNOWN_PARENT" => ["UnknownParent"]
  | "BlockException.UNKNOWN_PARENT_ZERO" => ["UnknownParent2"]
  | "BlockException.INVALID_LOG_BLOOM" => ["InvalidLogBloom"]
  | "BlockException.IMPORT_IMPOSSIBLE_DIFFICULTY_OVER_PARIS" => ["PostParisDifficultyIsNot0"]
  | "BlockException.INVALID_GAS_USED" => ["InvalidGasUsed"]
  | "BlockException.RLP_STRUCTURES_ENCODING" => ["RLP_ExpectedAsList"]
  | _ => []

/--
Before Osaka, a transaction with more blobs than the block maximum breaks both
caps: the per-transaction blob count and the block blob-gas allowance.
Validation reports the count error first. When the fixture instead names the block allowance, report that name.
The two errors stay distinct for every other case, including several transactions
whose blob counts are each at most six but sum past the block cap.
-/
def selectReportedException (expected : List String) (e : EVM.Exception) : EVM.Exception :=
  match e with
  | .TransactionException .TYPE_3_TX_BLOB_COUNT_EXCEEDED =>
    if expected.contains "TransactionException.TYPE_3_TX_MAX_BLOB_GAS_ALLOWANCE_EXCEEDED" then
      .TransactionException .TYPE_3_TX_MAX_BLOB_GAS_ALLOWANCE_EXCEEDED
    else
      e
  | _ => e

/-- Whether `e` is one of the `expected` exceptions, under either name. -/
def acceptsExpectedException (expected : List String) (e : EVM.Exception) : Bool :=
  let reported := (repr e).pretty
  expected.contains reported || (retestethExceptionNames reported).any expected.contains

end Conform

end Ethereum
