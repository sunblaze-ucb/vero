import PiggybankV2.Impl.ConcertShim
import PiggybankV2.Impl.PiggyBank

/-!
# PiggybankV2.Bundle

Per-package implementation bundle for the `PiggybankV2` root package.
Collects all PiggyBank API signatures into one structure.

DO NOT MODIFY -- benchmark infrastructure.
-/

structure PiggybankV2Bundle where
  insert : PiggybankV2.InsertSig
  smash : PiggybankV2.SmashSig
  init : PiggybankV2.InitSig
  receive : PiggybankV2.ReceiveSig
