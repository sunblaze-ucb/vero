import DafnyVMC.Impl.Monad
import DafnyVMC.Impl.Pos
import DafnyVMC.Impl.FisherYatesModel

/-!
# DafnyVMC.Test

`#guard` conformance tests for the computable reference implementations.

- Monad combinators (`return'`, `bind`, `coin`) are computable and tested here.
- `swap` is computable and tested here.
- `shuffle` and `shuffleCurried` are `noncomputable` (they depend on the
  axiomatised `sample` via `intervalSample`) and **cannot** be tested with
  `#guard`. Their correctness is a proof-mode task (see `Spec/`).

DO NOT MODIFY — infrastructure.
-/

-- ── Monad combinators ────────────────────────────────────────────────

-- return' wraps a value and leaves the bitstream unchanged.
#guard ((return' 42 : Hurd Nat) (fun _ => true)).value == 42

-- return' leaves the bitstream entirely intact.
#guard ((return' 7 : Hurd Nat) (fun n => n % 2 == 0)).rest 3 == (3 % 2 == 0)

-- coin reads the first bit; all-true stream yields true.
#guard (coin (fun _ => true)).value == true

-- coin reads the first bit; all-false stream yields false.
#guard (coin (fun _ => false)).value == false

-- bind sequences two computations: return' 5 then increment.
#guard (bind (return' 5 : Hurd Nat) (fun n => return' (n + 1)) (fun _ => true)).value == 6

-- ── Fisher-Yates swap (computable) ──────────────────────────────────

-- swap exchanges elements at positions 0 and 2.
#guard swap [1, 2, 3] 0 2 == [3, 2, 1]

-- Swapping an element with itself is a no-op.
#guard swap [1, 2, 3] 1 1 == [1, 2, 3]

-- ── Pos ─────────────────────────────────────────────────────────────

-- A Pos literal carries the expected underlying Nat value.
#guard (⟨3, by norm_num⟩ : Pos).val == 3
