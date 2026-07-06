import EscrowV2.Impl.Escrow

/-!
# EscrowV2.Bundle

Implementation bundle for the scoped Escrow v2 benchmark.
-/

structure EscrowV2Bundle where
  init : Escrow.InitSig
  receive : Escrow.ReceiveSig
