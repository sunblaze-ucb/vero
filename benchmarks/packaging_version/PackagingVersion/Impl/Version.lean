-- !benchmark @start imports
-- !benchmark @end imports

/-!
# PackagingVersion.Impl.Version

Version ordering over an already-parsed version `Ver` (an epoch, a release
tuple, and a pre/post/dev tag `PreTag`). The operations are the comparator
family (`verLe` / `verEq`), the extremal queries (`maxVer` / `minVer`), and a
canonical sort (`sortVers`).

Types and signatures are fixed vocabulary (DO NOT MODIFY). The intended order is
pinned by `Spec/Version.lean`, not by this file.
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- The pre/post/dev release tag. Canonical precedence within a release is
    `dev < a < b < rc < (final) < post`. `none'` is the "final" release
    (no qualifier). The carried `Nat` is the qualifier number (e.g. `rc 2`). -/
inductive PreTag where
  | dev   (n : Nat)
  | a     (n : Nat)
  | b     (n : Nat)
  | rc    (n : Nat)
  | none'
  | post  (n : Nat)
deriving DecidableEq, Repr

/-- A version: an epoch, a release tuple, and a pre/post/dev tag. -/
structure Ver where
  epoch   : Nat
  release : List Nat
  pre     : PreTag
deriving DecidableEq, Repr

-- ── Frozen comparison vocabulary (DO NOT MODIFY) ─────────────
-- `relCmp` and `tagCmp` (with their helpers `PreTag.rank` / `PreTag.num`) are
-- the fixed problem vocabulary the specs in `Spec/Version.lean` are stated in
-- terms of (e.g. `relCmp r1 r2 = .lt`, `tagCmp t1 t2 = .eq`). They define what
-- the comparison AXES mean; the agent must satisfy specs phrased over them.
-- They are frozen vocabulary, NOT the reference algorithm the agent implements
-- (that is `verCmp` / `insertVer` and the API bodies below).

/-- Rank of a tag for precedence: `dev=0 < a=1 < b=2 < rc=3 < final=4 < post=5`. -/
def PreTag.rank : PreTag → Nat
  | .dev _  => 0
  | .a _    => 1
  | .b _    => 2
  | .rc _   => 3
  | .none'  => 4
  | .post _ => 5

/-- The qualifier number carried by a tag (`0` for `final`). -/
def PreTag.num : PreTag → Nat
  | .dev n  => n
  | .a n    => n
  | .b n    => n
  | .rc n   => n
  | .none'  => 0
  | .post n => n

/-- Three-way comparison of tags: by rank, then by carried number. -/
def tagCmp (x y : PreTag) : Ordering :=
  match compare x.rank y.rank with
  | .eq => compare x.num y.num
  | o   => o

/-- Three-way comparison of release tuples with **trailing zeros trimmed**:
    compare element-wise, padding the shorter tuple with zeros. Hence
    `[1] ~ [1,0] ~ [1,0,0]` all compare equal. Structural on both lists. -/
def relCmp : List Nat → List Nat → Ordering
  | [],      []      => .eq
  | [],      y :: ys => match compare 0 y with
                        | .eq => relCmp [] ys
                        | o   => o
  | x :: xs, []      => match compare x 0 with
                        | .eq => relCmp xs []
                        | o   => o
  | x :: xs, y :: ys => match compare x y with
                        | .eq => relCmp xs ys
                        | o   => o

namespace PackagingVersion

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `verLe a b`: the canonical PEP 440 `a ≤ b`. -/
abbrev VerLeSig    := Ver → Ver → Bool

/-- `verEq a b`: order-equality (`a ≤ b` and `b ≤ a`); identifies versions
    that differ only by trailing release zeros. -/
abbrev VerEqSig    := Ver → Ver → Bool

/-- `maxVer xs`: the greatest version in `xs` under `verLe`, or `none` if
    `xs` is empty. -/
abbrev MaxVerSig   := List Ver → Option Ver

/-- `sortVers xs`: `xs` sorted ascending under `verLe` (a permutation). -/
abbrev SortVersSig := List Ver → List Ver

/-- `minVer xs`: the least version in `xs` under `verLe`, or `none` if
    `xs` is empty. -/
abbrev MinVerSig   := List Ver → Option Ver

end PackagingVersion

-- !benchmark @start global_aux

/-- Three-way comparison of versions: epoch, then release (trailing-zero
    trimmed), then tag precedence. This is the reference PEP 440 order. -/
def verCmp (a b : Ver) : Ordering :=
  match compare a.epoch b.epoch with
  | .eq => match relCmp a.release b.release with
           | .eq => tagCmp a.pre b.pre
           | o   => o
  | o   => o

/-- Insert `x` into an already-sorted list keeping it sorted under `verLe`. -/
def insertVer (le : Ver → Ver → Bool) (x : Ver) : List Ver → List Ver
  | []      => [x]
  | y :: ys => if le x y then x :: y :: ys else y :: insertVer le x ys

-- !benchmark @end global_aux

-- !benchmark @start code_aux def=verLe
-- !benchmark @end code_aux def=verLe

def PackagingVersion.verLe : PackagingVersion.VerLeSig :=
-- !benchmark @start code def=verLe
  fun a b => (verCmp a b) != Ordering.gt
-- !benchmark @end code def=verLe

-- !benchmark @start code_aux def=verEq
-- !benchmark @end code_aux def=verEq

def PackagingVersion.verEq : PackagingVersion.VerEqSig :=
-- !benchmark @start code def=verEq
  fun a b => (verCmp a b) == Ordering.eq
-- !benchmark @end code def=verEq

-- !benchmark @start code_aux def=maxVer
-- !benchmark @end code_aux def=maxVer

def PackagingVersion.maxVer : PackagingVersion.MaxVerSig :=
-- !benchmark @start code def=maxVer
  fun xs => xs.foldl
    (fun acc v =>
      match acc with
      | none      => some v
      | some best => if PackagingVersion.verLe best v then some v else some best)
    none
-- !benchmark @end code def=maxVer

-- !benchmark @start code_aux def=sortVers
-- !benchmark @end code_aux def=sortVers

def PackagingVersion.sortVers : PackagingVersion.SortVersSig :=
-- !benchmark @start code def=sortVers
  fun xs => xs.foldr (insertVer PackagingVersion.verLe) []
-- !benchmark @end code def=sortVers

-- !benchmark @start code_aux def=minVer
-- !benchmark @end code_aux def=minVer

def PackagingVersion.minVer : PackagingVersion.MinVerSig :=
-- !benchmark @start code def=minVer
  fun xs => xs.foldl
    (fun acc v =>
      match acc with
      | none      => some v
      | some best => if PackagingVersion.verLe v best then some v else some best)
    none
-- !benchmark @end code def=minVer
