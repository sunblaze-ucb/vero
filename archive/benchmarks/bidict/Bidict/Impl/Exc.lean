-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Bidict.Impl.Exc

Exception / error types for the bidict benchmark. `DuplicationError` is
the curator-given vocabulary for duplication-related failures raised by
mutable bidict operations.

DO NOT MODIFY types — fixed vocabulary.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

/-- Error variants for duplicate key or value insertions. -/
inductive DuplicationError
  | duplicateKeyError
  | duplicateValueError
  | duplicateKeyAndValueError
  deriving BEq, Repr
