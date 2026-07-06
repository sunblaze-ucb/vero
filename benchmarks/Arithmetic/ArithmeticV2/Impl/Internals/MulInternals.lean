/-!
# ArithmeticV2.Impl.Internals.MulInternals

Internal multiplication helper predicates translated from Verus. This module
has no scored executable APIs; the definitions here are frozen vocabulary used
by other translated specifications.
-/


namespace ArithmeticV2

/--
This function performs multiplication recursively. It's only valid when `x` is
non-negative.
-/
def mul_pos (x y : Int) : Int :=
  if x <= 0 then 0 else x * y

/--
This function performs multiplication recursively.
-/
def mul_recursive (x y : Int) : Int :=
  if x >= 0 then mul_pos x y else -1 * mul_pos (-1 * x) y

/--
This function expresses that multiplication is commutative, distributes over
addition, and distributes over subtraction.
-/
def mul_auto : Prop := True

/--
Selected source item for the internal multiplication broadcast group.
-/
def group_mul_properties_internal : Prop := True

/--
This utility function helps prove a mathematical property by induction. The
caller supplies an integer predicate, proves the predicate holds in the base
case of 0, and proves correctness of inductive steps both upward and downward
from the base case.
-/
def helper_lemma_mul_induction : Prop :=
  ∀ (f : Int → Prop),
    (f 0) ∧
    (∀ (i : Int), i ≥ 0 ∧ (f i) → f (i + 1)) ∧
    (∀ (i : Int), i ≤ 0 ∧ (f i) → f (i - 1)) →
      ∀ (i : Int), f i

/--
Proof that multiplication is always commutative.
-/
def helper_lemma_mul_commutes : Prop :=
  ∀ (x : Int) (y : Int), (x * y) = y * x

/--
Proof that multiplication distributes over addition by 1 and over subtraction
by 1.
-/
def helper_lemma_mul_successor : Prop :=
  ∀ (x : Int) (y : Int),
    ((x + 1) * y) = x * y + y ∧
    ∀ (x : Int) (y : Int), ((x - 1) * y) = x * y - y

/--
Selected source item proving the broadcast group provides `mul_auto`.
-/
def helper_lemma_mul_properties_internal_prove_mul_auto : Prop := (mul_auto)

/--
This utility function helps prove a mathematical property by induction for a
given integer.
-/
def helper_lemma_mul_induction_auto : Prop :=
  ∀ (_x : Int) (_f : Int → Prop), (mul_auto) → True

/--
This utility function helps prove a mathematical property by induction for all
integers.
-/
def helper_lemma_mul_induction_auto_forall : Prop :=
  ∀ (_f : Int → Prop), (mul_auto) → True

/--
Proof that multiplication distributes over addition.
-/
def helper_lemma_mul_distributes_plus : Prop :=
  ∀ (x : Int) (y : Int) (z : Int), ((x + y) * z) = (x * z + y * z)

/--
Selected source item proving that multiplication distributes over subtraction.
-/
def helper_lemma_mul_distributes_minus : Prop :=
  ∀ (x : Int) (y : Int) (z : Int), ((x - y) * z) = (x * z - y * z)

end ArithmeticV2
