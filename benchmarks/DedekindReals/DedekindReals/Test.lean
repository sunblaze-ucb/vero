import DedekindReals.Harness
import DedekindReals.Spec.Multiplication

open DedekindReals

#guard Qmin4 1 2 3 4 == (1 : Rat)
#guard Qmax4 1 2 3 4 == (4 : Rat)
#guard sum_f_Q0 (fun n => (n : Rat)) 2 == (3 : Rat)

-- The inverse witness must use the same operations as its bundle.
example (impl : RepoImpl) (x : R)
    (h : impl.dedekindReals.Rneq x (impl.dedekindReals.R_of_Q 0)) : R :=
  impl.dedekindReals.Rinv x h

private def noncanonicalInverseBundle : DedekindRealsBundle :=
  { canonicalDedekindReals with
    Rneq := fun _ _ => True
    R_of_Q := fun _ => R_of_Q 1
    Rinv := fun x _ => x }

example (x : R) : noncanonicalInverseBundle.Rinv x True.intro = x := rfl
example : canonicalDedekindReals.Rinv = Rinv := rfl
