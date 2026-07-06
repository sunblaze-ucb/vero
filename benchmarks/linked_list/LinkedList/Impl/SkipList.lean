-- !benchmark @start imports
-- !benchmark @end imports

/-!
# LinkedList.Impl.SkipList

Skip list modelled as sorted association list `List (κ × ν)`.
@review human: probabilistic structure replaced by deterministic sorted list.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

abbrev SkipL.SkipList (κ ν : Type) := List (κ × ν)

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace SkipL

variable {κ ν : Type} [Ord κ]

abbrev InsertSig := List (κ × ν) → κ → ν → List (κ × ν)
abbrev DeleteSig := List (κ × ν) → κ → List (κ × ν)
abbrev FindSig   := List (κ × ν) → κ → Option ν

-- !benchmark @start code_aux def=skipl_insert
-- Sorted insert: insert (k, v) replacing existing key if present.
private def sortedInsert (k : κ) (v : ν) : List (κ × ν) → List (κ × ν)
  | [] => [(k, v)]
  | (k', v') :: rest =>
    match compare k k' with
    | .lt => (k, v) :: (k', v') :: rest
    | .eq => (k, v) :: rest
    | .gt => (k', v') :: sortedInsert k v rest
-- !benchmark @end code_aux def=skipl_insert

def insert : List (κ × ν) → κ → ν → List (κ × ν) :=
-- !benchmark @start code def=skipl_insert
  fun s k v => sortedInsert k v s
-- !benchmark @end code def=skipl_insert

-- !benchmark @start code_aux def=skipl_delete
-- !benchmark @end code_aux def=skipl_delete

def delete : List (κ × ν) → κ → List (κ × ν) :=
-- !benchmark @start code def=skipl_delete
  fun s k => s.filter fun pair => compare k pair.1 != Ordering.eq
-- !benchmark @end code def=skipl_delete

-- !benchmark @start code_aux def=skipl_find
-- !benchmark @end code_aux def=skipl_find

def find : List (κ × ν) → κ → Option ν :=
-- !benchmark @start code def=skipl_find
  fun s k =>
    (s.find? fun pair => compare k pair.1 == Ordering.eq).map Prod.snd
-- !benchmark @end code def=skipl_find

end SkipL
