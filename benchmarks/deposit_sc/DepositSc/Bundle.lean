import DepositSc.Impl.Bits
import DepositSc.Impl.Tree
import DepositSc.Impl.Merkle
import DepositSc.Impl.Contract

/-!
# DepositSc.Bundle

Per-package implementation bundle for the `DepositSc` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure DepositScBundle where
  -- Bit primitives
  power2                               : DepositSc.Power2Sig
  bitListToNat                         : DepositSc.BitListToNatSig
  natToBitList                         : DepositSc.NatToBitListSig
  nextPath                             : DepositSc.NextPathSig
  zipCond                              : DepositSc.ZipCondSig
  defaultValue                         : DepositSc.DefaultValueSig
  zeroes                               : DepositSc.ZeroesSig
  -- Tree navigation
  nodeAt                               : DepositSc.NodeAtSig
  siblingAt                            : DepositSc.SiblingAtSig
  siblingValueAt                       : DepositSc.SiblingValueAtSig
  height                               : DepositSc.HeightSig
  nodesIn                              : DepositSc.NodesInSig
  leavesIn                             : DepositSc.LeavesInSig
  -- Merkle construction + incremental algorithm
  buildMerkle                          : DepositSc.BuildMerkleSig
  computeRootLeftRightUpWithIndex      : DepositSc.ComputeRootWithIndexSig
  computeLeftSiblingsOnNextpathWithIndex
                                       : DepositSc.ComputeLeftSiblingsWithIndexSig
  -- Path-based (non-index) analogues: Dafny's GenericComputation /
  -- ComputeRootPath / NextPathInCompleteTreesLemmas modules.
  computeRootPath                      : DepositSc.ComputeRootPathSig
  computeRootLeftRightUp               : DepositSc.ComputeRootLeftRightUpSig
  computeLeftSiblingOnNextPathFromLeftRight
                                       : DepositSc.ComputeLeftSiblingOnNextPathFromLeftRightSig
  -- Contract API
  mkDeposit                            : DepositSc.MkDepositSig
  deposit                              : DepositSc.DepositSig
  getDepositRoot                       : DepositSc.GetDepositRootSig
