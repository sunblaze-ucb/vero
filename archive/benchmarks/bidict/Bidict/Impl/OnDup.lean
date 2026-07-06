-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Bidict.Impl.OnDup

On-duplication action types controlling how the mutable bidict handles
duplicate key or value insertions. Curator-given vocabulary — do not modify.

DO NOT MODIFY types — fixed vocabulary.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

/-- Action to take when a duplicate is encountered during insertion. -/
inductive OnDupAction where
  | raise
  | dropOld
  | dropNew
  deriving BEq, Repr

/-- Combined on-duplication policy: separate actions for key and value duplication. -/
structure OnDup : Type where
  key : OnDupAction
  val : OnDupAction
  deriving BEq, Repr
