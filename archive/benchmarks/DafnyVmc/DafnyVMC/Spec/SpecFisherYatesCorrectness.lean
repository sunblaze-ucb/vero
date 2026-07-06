import DafnyVMC.Harness
import DafnyVMC.Impl.FisherYatesModel

/-!
# DafnyVMC.Spec.SpecFisherYatesCorrectness

Correctness specifications for the Fisher-Yates shuffle. These are the two
primary proof-mode theorem stubs for the LLM, corresponding to
`src/Util/FisherYates/Correctness.dfy`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- The Fisher-Yates shuffle assigns probability exactly `1/|xs|!` to every
    permutation `p` of an index-tagged list `xs`.

    Index tags make all elements globally distinct, so no uniqueness
    assumption on the original elements is needed: `xs.map Prod.fst ~ p.map Prod.fst`
    asserts that `xs` and `p` are permutations of the same multiset of values. -/
def spec_correctnessFisherYates (_impl : RepoImpl) : Prop :=
  ∀ (α : Type) [DecidableEq α] (xs p : List (α × Nat)),
    List.Perm (xs.map Prod.fst) (p.map Prod.fst) →
    prob {s | (shuffle xs s).value = p} = (1 : ENNReal) / Nat.factorial xs.length

/-- For lists with pairwise-distinct elements, the Fisher-Yates shuffle assigns
    probability exactly `1/|xs|!` to every permutation `p`.

    `xs.Nodup` asserts pairwise distinctness; `xs.toFinset = p.toFinset` asserts
    that `xs` and `p` cover the same set of elements. -/
def spec_correctnessFisherYatesUniqueElements (_impl : RepoImpl) : Prop :=
  ∀ (α : Type) [DecidableEq α] (xs p : List α),
    xs.Nodup → xs.toFinset = p.toFinset →
    prob {s | (shuffle xs s).value = p} = (1 : ENNReal) / Nat.factorial xs.length
