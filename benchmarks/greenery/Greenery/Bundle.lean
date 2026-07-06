import Greenery.Impl.Fsm
import Greenery.Impl.Algebra

/-!
# Greenery.Bundle

Per-package implementation bundle for the `Greenery` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure GreeneryBundle where
  accepts       : Greenery.AcceptsSig
  reversed      : Greenery.ReversedSig
  reduce        : Greenery.ReduceSig
  fsmUnion      : Greenery.FsmUnionSig
  fsmInter      : Greenery.FsmInterSig
  everythingbut : Greenery.EverythingButSig
  equivalent    : Greenery.EquivalentSig
