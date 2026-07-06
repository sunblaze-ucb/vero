import DedekindReals.Bundle

namespace DedekindReals

structure RepoImpl where
  dedekindReals : DedekindRealsBundle

def canonicalDedekindReals : DedekindRealsBundle where
  Rlt := Rlt
  Rle := Rle
  Req := Req
  Rneq := Rneq
  R_of_Q := R_of_Q
  Rzero := Rzero
  Zone := Zone
  Rplus := Rplus
  Ropp := Ropp
  Rminus := Rminus
  CauchyQ_R := CauchyQ_R
  RCut_of_R := RCut_of_R
  R_of_RCut := R_of_RCut
  Rmult := Rmult
  Rinv := Rinv
  Rmin := Rmin
  Rmax := Rmax

def canonical : RepoImpl where
  dedekindReals := canonicalDedekindReals

syntax "joint_unsat" : tactic

macro_rules
  | `(tactic| joint_unsat) => `(tactic| first | contradiction | simp_all)

end DedekindReals
