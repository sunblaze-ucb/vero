---
name: vero-verus-pitfalls
description: Load BEFORE translating any Verus item to Lean 4 to avoid known Verus→Lean pitfalls. Pair with vero-source-verus and vero-lean-pitfalls.
allowed-tools: Read, Write, Edit, Bash, Grep, Glob
---

# Verus → Lean 4 Translation Pitfalls

Issues specific to translating Verus (Rust-based verification) to Lean 4.

## 1. external_body → opaque + noncomputable Chain

**Problem:** Verus `#[verifier(external_body)]` marks types/functions whose
implementation is trusted (not verified). In Lean, translate to `opaque`.
BUT: every downstream function referencing it must be `noncomputable`.

**Verus:**
```rust
#[verifier(external_body)]
pub struct HashMap<K, V> { ... }

#[verifier(external_body)]
pub fn insert<K, V>(m: &mut HashMap<K, V>, k: K, v: V) { ... }
```

**Lean (correct):**
```lean
opaque HashMap (K V : Type) : Type

opaque HashMap.insert {K V : Type} (m : HashMap K V) (k : K) (v : V) : HashMap K V

-- ALL functions using insert must be noncomputable:
noncomputable def receiveImpl (state : State) (msg : Msg) : State :=
-- !benchmark @start code def=receiveImpl
  -- translated reference body using HashMap.insert
  ...
-- !benchmark @end code def=receiveImpl
```

**Key insight:** Before using `opaque`, check `lean_local_search("HashMap")`
— Lean has `Std.HashMap` built in. If the source just wraps a standard
collection, map to the stdlib version instead.

## 2. requires/ensures → Hypotheses + Prop

**Verus:**
```rust
fn deposit(&mut self, value: u64)
    requires
        self.count < MAX_COUNT,
        value > 0,
    ensures
        self.balance == old(self).balance + value,
```

**Lean curation output:**
```lean
-- Function: translated reference implementation
def deposit (s : State) (value : UInt64) : State :=
-- !benchmark @start code def=deposit
  ...
-- !benchmark @end code def=deposit

-- Spec: ensures become frozen benchmark obligations, with no markers
def spec_deposit (impl : RepoImpl) : Prop :=
  ∀ (s : State) (value : UInt64),
  s.count < MAX_COUNT →
  value > 0 →
  (impl.bank.deposit s value).balance = s.balance + value.toNat
```

**Note:** `requires` become hypotheses (→) in the spec, not separate
precondition functions. Do not emit `spec` markers; Spec files are frozen.

## 3. exec vs proof vs spec Functions

**Verus distinguishes three modes:**

| Verus mode | Lean translation |
|-----------|-----------------|
| `exec fn` | `def f := <translated reference impl>` with `code` markers |
| `proof fn` | benchmark obligation `def spec_* (impl : RepoImpl) : Prop` in Spec, no markers |
| `spec fn` | vocabulary/helper `def` with a full body, no markers |
| `spec fn` (opaque) | `opaque f_spec ...` (no markers) |

**Key:** `exec` functions are the LLM-editable code tasks, but curation
still stores the translated reference body inside the marker. `proof`
functions become frozen spec obligations, not curation-time theorems.

## 4. Ghost Variables and old()

**Problem:** Verus `old(self)` refers to the pre-state. Lean has no built-in
`old` — you must pass both pre and post state explicitly.

**Verus:**
```rust
ensures self.items == old(self).items.push(value)
```

**Lean:**
```lean
def push_spec (pre post : Stack) (value : T) : Prop :=
  post.items = pre.items ++ [value]
```

## 5. Rust-Style Mutation → Pure Functional

**Problem:** Verus functions take `&mut self`. Lean is purely functional —
translate to functions that take old state and return new state.

**Verus:**
```rust
fn push(&mut self, value: T)
```

**Lean:**
```lean
def push (s : Stack T) (value : T) : Stack T :=
  { s with items := s.items ++ [value] }
```

## 6. Linear Types / Tracked

**Problem:** Verus `tracked` and `Tracked<T>` are ghost/proof-level values.
In Lean, these become regular parameters with `Prop` constraints.

**Simple rule:** Drop `tracked` annotations. If the tracked value is used
in specs, keep it as a regular parameter.

## 7. Integer Overflow

**Problem:** Verus uses `u32`, `u64`, etc. with overflow checking.
Lean's `UInt32`, `UInt64` wrap on overflow (modular arithmetic).

**Fix:** For specs that reason about overflow, use `Nat` or `Int` and add
explicit bounds as hypotheses:
```lean
def safe_add (a b : Nat) (h : a + b < 2^32) : Nat := a + b
```

## 8. Verus broadcast/reveal

**Problem:** Verus `broadcast use` and `reveal()` control lemma visibility.
No direct Lean equivalent.

**Fix:** In Lean, all lemmas are always available. Translate `broadcast`
lemmas as regular theorems. If the source uses `reveal(f)` before calling
`f`, the Lean translation doesn't need it — `unfold f` or `simp [f]` works.
