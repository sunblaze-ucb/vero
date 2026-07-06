/-!
# Json.Impl.Utils.Cursors

Cursor vocabulary translated from `JSON.Utils.Cursors`.

DO NOT MODIFY types - these are the fixed vocabulary.
-/

namespace JSON

-- Types (no markers - fixed vocabulary)

structure Cursor_ where
  s : List UInt8
  beg : UInt32
  point : UInt32
  end_ : UInt32
  deriving Repr, DecidableEq, BEq

abbrev Cursor := Cursor_

abbrev FreshCursor := Cursor_

structure Split (T : Type) where
  t : T
  cs : FreshCursor

inductive CursorError (R : Type) where
  | eof
  | expectingByte (expected : UInt8) (b : Option UInt8)
  | expectingAnyByte (expected_sq : List UInt8) (b : Option UInt8)
  | otherError (err : R)
  deriving Repr

abbrev CursorResult (R : Type) := Except (CursorError R) Cursor

-- Spec helpers (no markers - fixed vocabulary)

def cursor__Valid? (cs : Cursor_) : Prop :=
  cs.beg.toNat ≤ cs.point.toNat ∧ cs.point.toNat ≤ cs.end_.toNat ∧
    cs.end_.toNat ≤ cs.s.length ∧ cs.s.length < 2 ^ 32

end JSON
