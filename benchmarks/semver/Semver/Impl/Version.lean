-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Semver.Impl.Version

SemVer 2.0.0 version precedence and constraint selection.

A `Version` is a `major.minor.patch` core (each a `Nat`), a pre-release
identifier list (`List Ident`, each identifier numeric or alphanumeric), and
build metadata (`List String`), which is irrelevant to precedence. The API is
the comparator family (`compareV` / `versionLt` / `versionEq`), the constraint
predicate (`satisfies`), and `select`. Their intended behaviour is pinned by
`Spec/Version.lean`.

The field-precedence relations (`identCmp`, `preCmp`, `preFieldCmp`,
`compareCore`) in the `global_aux` block below are this implementation's own
helper definitions. The specs anchor to their OWN spec-side copies
(`identCmpRef` / `preCmpRef` / `preFieldCmpRef`, defined in `Spec/Version.lean`
and always shipped), so the specs never depend on these Impl helpers; a
conforming implementation supplies whatever helpers it needs here. The core
types and API signatures are fixed.
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- A single pre-release identifier: either purely numeric (`num`) or
    alphanumeric (`alpha`). SemVer §11.4.1–11.4.2: numeric identifiers compare
    numerically and always rank below alphanumeric identifiers, which compare in
    ASCII order. -/
inductive Ident where
  | num   (n : Nat)
  | alpha (s : String)
deriving DecidableEq, Repr

/-- A SemVer 2.0.0 version: a `major.minor.patch` core, a (possibly empty)
    pre-release identifier list, and (precedence-irrelevant) build metadata. -/
structure Version where
  major : Nat
  minor : Nat
  patch : Nat
  pre   : List Ident
  build : List String
deriving DecidableEq, Repr

/-- A comparison operator for a constraint clause. -/
inductive Op where
  | lt | le | gt | ge | eq
deriving DecidableEq, Repr

/-- A single constraint clause `op ⋄ ver` (e.g. `>= 1.2.0`). -/
structure Clause where
  op  : Op
  ver : Version
deriving DecidableEq, Repr

namespace Semver

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `compareV a b`: the SemVer 2.0.0 three-way precedence comparison
    (`major.minor.patch`, then pre-release, build metadata ignored). -/
abbrev CompareVSig := Version → Version → Ordering

/-- `versionLt a b`: strict SemVer precedence (`a` has lower precedence than `b`). -/
abbrev VersionLtSig := Version → Version → Bool

/-- `versionEq a b`: SemVer precedence-equality (equal core and pre-release; build
    metadata ignored). -/
abbrev VersionEqSig := Version → Version → Bool

/-- `satisfies cs v`: `v` satisfies every clause of the constraint `cs`. -/
abbrev SatisfiesSig := List Clause → Version → Bool

/-- `select cs xs`: the greatest version in `xs` satisfying the constraint
    `cs` under SemVer precedence, or `none` if none match. -/
abbrev SelectSig := List Clause → List Version → Option Version

end Semver

-- !benchmark @start global_aux

/-- Three-way comparison of a single pre-release identifier (frozen). SemVer
    §11.4: numeric identifiers always rank below alphanumeric identifiers; two
    numeric identifiers compare numerically; two alphanumeric identifiers
    compare in ASCII order. -/
def identCmp : Ident → Ident → Ordering
  | .num a,   .num b   => compare a b
  | .num _,   .alpha _ => .lt
  | .alpha _, .num _   => .gt
  | .alpha a, .alpha b => compare a b

/-- Three-way comparison of pre-release identifier lists (frozen), SemVer §11.4:
    the ordinary identifier-list order in which, among lists sharing a prefix,
    the longer one ranks higher (§11.4.4). The special "empty pre-release is
    GREATEST" rule lives in `preFieldCmp`, not here. -/
def preCmp : List Ident → List Ident → Ordering
  | [],      []      => .eq
  | [],      _ :: _  => .lt          -- fewer identifiers ranks below more
  | _ :: _,  []      => .gt
  | x :: xs, y :: ys => match identCmp x y with
                        | .eq => preCmp xs ys
                        | o   => o

/-- Three-way comparison of the pre-release FIELD (frozen). SemVer §11.3: a
    version WITHOUT a pre-release (the empty list) has the GREATEST precedence,
    so the empty list ranks above any non-empty one; two non-empty lists are
    compared by `preCmp`. -/
def preFieldCmp : List Ident → List Ident → Ordering
  | [],      []      => .eq
  | [],      _ :: _  => .gt          -- no pre-release ranks above a pre-release
  | _ :: _,  []      => .lt
  | x :: xs, y :: ys => preCmp (x :: xs) (y :: ys)

/-- Three-way comparison of the precedence-relevant core + pre-release (frozen):
    `major`, then `minor`, then `patch` numerically, then `preFieldCmp` on the
    pre-release list. Build metadata is NOT consulted. This is the reference
    SemVer 2.0.0 precedence relation. -/
def compareCore (a b : Version) : Ordering :=
  match compare a.major b.major with
  | .eq => match compare a.minor b.minor with
           | .eq => match compare a.patch b.patch with
                    | .eq => preFieldCmp a.pre b.pre
                    | o   => o
           | o   => o
  | o   => o

/-- Whether a single clause `op ⋄ ver` is satisfied by `v`, decided through the
    frozen `compareCore` precedence relation. -/
def clauseHolds (le : Version → Version → Bool) (lt : Version → Version → Bool)
    (eq : Version → Version → Bool) (c : Clause) (v : Version) : Bool :=
  match c.op with
  | .lt => lt v c.ver
  | .le => le v c.ver
  | .gt => lt c.ver v
  | .ge => le c.ver v
  | .eq => eq v c.ver

-- !benchmark @end global_aux

-- !benchmark @start code_aux def=compareV
-- !benchmark @end code_aux def=compareV

def Semver.compareV : Semver.CompareVSig :=
-- !benchmark @start code def=compareV
  fun a b => compareCore a b
-- !benchmark @end code def=compareV

-- !benchmark @start code_aux def=versionLt
-- !benchmark @end code_aux def=versionLt

def Semver.versionLt : Semver.VersionLtSig :=
-- !benchmark @start code def=versionLt
  fun a b => (compareCore a b) == Ordering.lt
-- !benchmark @end code def=versionLt

-- !benchmark @start code_aux def=versionEq
-- !benchmark @end code_aux def=versionEq

def Semver.versionEq : Semver.VersionEqSig :=
-- !benchmark @start code def=versionEq
  fun a b => (compareCore a b) == Ordering.eq
-- !benchmark @end code def=versionEq

-- !benchmark @start code_aux def=satisfies
-- !benchmark @end code_aux def=satisfies

def Semver.satisfies : Semver.SatisfiesSig :=
-- !benchmark @start code def=satisfies
  fun cs v =>
    cs.all (fun c =>
      clauseHolds
        (fun x y => (compareCore x y) != Ordering.gt)
        (fun x y => (compareCore x y) == Ordering.lt)
        (fun x y => (compareCore x y) == Ordering.eq)
        c v)
-- !benchmark @end code def=satisfies

-- !benchmark @start code_aux def=select
-- !benchmark @end code_aux def=select

def Semver.select : Semver.SelectSig :=
-- !benchmark @start code def=select
  fun cs xs =>
    xs.foldl
      (fun acc v =>
        if Semver.satisfies cs v then
          match acc with
          | none      => some v
          | some best => if (compareCore best v) == Ordering.lt then some v else some best
        else acc)
      none
-- !benchmark @end code def=select
