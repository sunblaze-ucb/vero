import EIP20V2.Impl.EIP20Token
import EIP20V2.Impl.EIP20TokenCorrect
import EIP20V2.Impl.EIP20TokenTests

/-!
# EIP20V2.Bundle

Per-package implementation bundle for the `EIP20V2` package. Collects all
scored API signatures into one structure.

DO NOT MODIFY - benchmark infrastructure.
-/

structure EIP20V2Bundle where
  init : EIP20V2.InitSig
  try_transfer : EIP20V2.TryTransferSig
  try_transfer_from : EIP20V2.TryTransferFromSig
  try_approve : EIP20V2.TryApproveSig
  receive : EIP20V2.ReceiveSig
