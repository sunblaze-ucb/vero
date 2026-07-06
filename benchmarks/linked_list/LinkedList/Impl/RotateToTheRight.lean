-- !benchmark @start imports
-- !benchmark @end imports

/-!
# LinkedList.Impl.RotateToTheRight

Rotate a linked list to the right by k places. `insertNode` appends an
integer to the list; `rotateToTheRight` rotates the list so that the
last `(places % length)` elements move to the front.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Types (fixed vocabulary) ─────────────────────────────────────
/-- A linked list for rotation, modelled as `List Int`. -/
abbrev Rotate.LinkedList := List Int

namespace Rotate

-- ── API signatures (fixed vocabulary) ────────────────────────────
abbrev InsertNodeSig       := List Int → Int → List Int
abbrev RotateToTheRightSig := List Int → Nat → List Int

end Rotate

-- ── Implementations (LLM task) ───────────────────────────────────

-- !benchmark @start code_aux def=rotate_insertNode
-- !benchmark @end code_aux def=rotate_insertNode

def Rotate.insertNode : Rotate.InsertNodeSig :=
-- !benchmark @start code def=rotate_insertNode
  fun l data => l ++ [data]
-- !benchmark @end code def=rotate_insertNode

-- !benchmark @start code_aux def=rotate_rotateToTheRight
-- !benchmark @end code_aux def=rotate_rotateToTheRight

def Rotate.rotateToTheRight : Rotate.RotateToTheRightSig :=
-- !benchmark @start code def=rotate_rotateToTheRight
  fun l places =>
    let n := l.length
    if n == 0 then l
    else
      let k := places % n
      if k == 0 then l
      else
        -- last k elements move to front
        l.drop (n - k) ++ l.take (n - k)
-- !benchmark @end code def=rotate_rotateToTheRight
