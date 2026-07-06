---
name: vero-lean-pitfalls
description: Load BEFORE writing any Lean 4 translation to avoid common Lean pitfalls (universes, coercions, type-class resolution, notation). Pair with vero-translate.
allowed-tools: Read, Write, Edit, Bash, Grep, Glob
---

# Lean 4 Translation Pitfalls

Common issues encountered when translating formally-verified code from
Dafny, Verus, or Coq into Lean 4. Check each pitfall proactively during
translation to avoid discovering them only at build time.

## 1. noncomputable Propagation

**Problem:** When a type or function is declared `opaque` in Lean (because
the source marks it as external/FFI), any function that references it
becomes non-computable. Lean requires these to be explicitly marked
`noncomputable`. This propagates transitively through the call chain.

**Symptom:**
```
error: definition 'funcName' depends on opaque 'externalFunc'
```

**Fix:** Add `noncomputable` to the definition:
```lean
noncomputable def funcName (x : T) : U := ...
```

**Prevention:** After declaring any `opaque`, immediately grep for all
functions that reference it and proactively add `noncomputable`:
```bash
grep -rn 'opaqueName' ProjectName/ --include='*.lean'
```

**Key insight:** `noncomputable` only matters for definitions that Lean
tries to compile to executable code. Theorems and proofs don't need it.
`#guard` tests CANNOT use noncomputable definitions — you need executable
reference implementations in the Test file.

## 2. Standard Library Mappings

Before declaring anything as `opaque`, check if Lean's stdlib already
provides it. Use `lean_local_search` MCP tool if available.

| Source construct | Lean equivalent |
|-----------------|-----------------|
| HashMap/Dictionary | `Std.HashMap K V` |
| HashSet | `Std.HashSet T` |
| Dynamic array / Vec | `Array T` |
| Linked list | `List T` |
| Optional/Option | `Option T` |
| Result/Either | `Except E T` |
| Tuple | `T × U` or `Prod T U` |
| String | `String` |
| Byte array | `ByteArray` |
| Integer (unbounded) | `Int` |
| Natural number | `Nat` |
| Bitvector | `BitVec n` |

## 3. Prop vs Bool Confusion

**Problem:** Lean distinguishes `Prop` (logical propositions) from `Bool`
(computational booleans). Source languages often conflate these.

**Rules:**
- Specifications and theorem statements use `Prop`
- Computable functions that branch use `Bool`
- `Decidable` instances bridge the gap (use `decide` to go from `Prop` to `Bool`)
- `#guard` requires `Bool` or `Decidable` — cannot test arbitrary `Prop`

**Common fix:** If a spec function returns `Bool` but should be `Prop`,
change the return type and use `:=` with propositional connectives:
```lean
-- Bad: def spec (x : Nat) : Bool := x > 0 && x < 10
-- Good: def spec (x : Nat) : Prop := x > 0 ∧ x < 10
```

## 4. Natural Number Subtraction

**Problem:** In Lean, `Nat` subtraction is truncating: `3 - 5 = 0`.
Source languages may use signed integers where `3 - 5 = -2`.

**Fix:** Use `Int` when negative results are possible:
```lean
def balance (deposits withdrawals : Int) : Int :=
  deposits - withdrawals  -- Can be negative
```

## 5. Division by Zero

**Problem:** In Lean, division by zero returns zero (`n / 0 = 0`).
Source languages may have preconditions preventing this.

**Fix:** Translate `requires d != 0` as a hypothesis:
```lean
def safeDivide (n d : Nat) (hd : d ≠ 0) : Nat := n / d
```

If callers are required to prove the divisor is nonzero, keep the
hypothesis in the API type and translate the real body under that
precondition.

## 6. Import Order

**Problem:** In Lean 4, `import` statements MUST be the very first
non-comment content in a file. Module docstrings must come AFTER imports.

**Symptom:**
```
error: unexpected token 'namespace'; expected 'import'
```

**Fix:** Always structure files as:
```lean
import ProjectName.Dependency

/-! Module docstring -/

namespace ProjectName.Module
```

## 7. autoImplicit Pitfalls

**Problem:** With `autoImplicit = false` (which we use), ALL type variables
must be explicitly declared.

**Symptom:**
```
error: unknown identifier 'α'
```

**Fix:** Add explicit universe polymorphism:
```lean
def push {α : Type} (s : Stack α) (v : α) : Stack α := ...
-- or use section variables:
variable {α : Type}
```

## 8. deriving Clause Limitations

**Problem:** Not all types can automatically derive all instances.
Large structures (>10 fields) may fail to derive `BEq` or `DecidableEq`.

**Fix:** Skip `BEq` for large structures. Use manual instances only
when the source semantics or tests actually require them:
```lean
structure LargeConfig where
  field1 : Nat
  -- ... many fields
  deriving Inhabited, Repr  -- Skip BEq, DecidableEq
```

## 9. Mutual Recursion

**Problem:** Lean requires `mutual ... end` blocks for mutually recursive
definitions, and termination must be proved for all functions in the block.

**Fix:**
```lean
mutual
  def even : Nat → Bool
    | 0 => true
    | n + 1 => odd n
  def odd : Nat → Bool
    | 0 => false
    | n + 1 => even n
end
```

For curated benchmark sources, translate the real mutual bodies and add
the needed termination hints. Pre-agent materialization introduces
`sorry` later, after this source has already built.

## 10. Universe Polymorphism

**Problem:** Source languages don't have universe levels. In Lean,
generic types may need explicit universe annotations.

**Simple rule:** Use `Type` (which is `Type 0`) unless you need
higher universes. Most translations don't need universe polymorphism.
