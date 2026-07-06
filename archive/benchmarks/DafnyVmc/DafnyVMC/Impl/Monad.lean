import DafnyVMC.Impl.Rand

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# DafnyVMC.Impl.Monad

Foundation types and monad combinators for probabilistic computation
(the Hurd monad, cf. Joe Hurd's PhD thesis).  `Result α` carries the
computed value and the unconsumed bitstream; `Hurd α` is a function
from a `Bitstream` to a `Result α`.

`return'`, `bind`, `map`, `coin`, and `join` form the core monad API.
`bitstreamsWithValueIn` and `bitstreamsWithRestIn` are vocabulary
helpers used by the Independence and correctness specs.

Translated from `src/ProbabilisticProgramming/Monad.dfy`.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Foundation types (DO NOT MODIFY) ──────────────────────────────

/-- The result of a probabilistic computation on a bitstream.
    Contains the computed value and the unconsumed rest of the stream.
    Corresponds to Dafny's `datatype Result<A>`. -/
structure Result (α : Type) where
  value : α
  rest  : Bitstream

instance {α : Type} [Inhabited α] : Inhabited (Result α) :=
  ⟨⟨default, default⟩⟩

/-- The Hurd monad: a probabilistic computation that consumes a
    `Bitstream` and produces a `Result`.
    Corresponds to Dafny's `type Hurd<A> = Rand.Bitstream -> Result<A>`. -/
abbrev Hurd (α : Type) := Bitstream → Result α

-- ── Monad combinators (reference implementations — LLM task) ───────

-- !benchmark @start code_aux def=return'
-- !benchmark @end code_aux def=return'

def return' {α : Type} (a : α) : Hurd α :=
-- !benchmark @start code def=return'
  fun s => ⟨a, s⟩
-- !benchmark @end code def=return'

-- !benchmark @start code_aux def=bind
-- !benchmark @end code_aux def=bind

def bind {α β : Type} (f : Hurd α) (g : α → Hurd β) : Hurd β :=
-- !benchmark @start code def=bind
  fun s => let r := f s; g r.value r.rest
-- !benchmark @end code def=bind

-- !benchmark @start code_aux def=map
-- !benchmark @end code_aux def=map

def map {α β : Type} (m : Hurd α) (f : α → β) : Hurd β :=
-- !benchmark @start code def=map
  bind m (fun a => return' (f a))
-- !benchmark @end code def=map

-- !benchmark @start code_aux def=coin
-- !benchmark @end code_aux def=coin

def coin : Hurd Bool :=
-- !benchmark @start code def=coin
  fun s => ⟨s 0, fun n => s (n + 1)⟩
-- !benchmark @end code def=coin

-- !benchmark @start code_aux def=join
-- !benchmark @end code_aux def=join

def join {α : Type} (ff : Hurd (Hurd α)) : Hurd α :=
-- !benchmark @start code def=join
  bind ff id
-- !benchmark @end code def=join

-- ── Vocabulary helpers (used by Independence and correctness specs) ─

-- !benchmark @start code_aux def=bitstreamsWithValueIn
-- !benchmark @end code_aux def=bitstreamsWithValueIn

def bitstreamsWithValueIn {α : Type} (h : Hurd α) (aSet : Set α) : Set Bitstream :=
-- !benchmark @start code def=bitstreamsWithValueIn
  fun s => aSet (h s).value
-- !benchmark @end code def=bitstreamsWithValueIn

-- !benchmark @start code_aux def=bitstreamsWithRestIn
-- !benchmark @end code_aux def=bitstreamsWithRestIn

def bitstreamsWithRestIn {α : Type} (h : Hurd α) (restSet : Set Bitstream) : Set Bitstream :=
-- !benchmark @start code def=bitstreamsWithRestIn
  fun s => restSet (h s).rest
-- !benchmark @end code def=bitstreamsWithRestIn
