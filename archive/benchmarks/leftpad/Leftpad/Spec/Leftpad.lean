import Leftpad.Harness

/-!
# Leftpad.Spec.Leftpad

Specifications for list and string leftpad. Each `spec_*` is a property
over an arbitrary `impl : RepoImpl`.
-/

def spec_leftpad_length (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (n : Nat) (a : α) (l : List α),
    (impl.leftpad.leftpad n a l).length = max n l.length

def spec_leftpad_prefix (impl : RepoImpl) : Prop :=
  ∀ {α : Type} [BEq α] [LawfulBEq α] (n : Nat) (a : α) (l : List α),
    (List.replicate (n - l.length) a).isPrefixOf (impl.leftpad.leftpad n a l)

def spec_leftpad_suffix (impl : RepoImpl) : Prop :=
  ∀ {α : Type} [BEq α] [LawfulBEq α] (n : Nat) (a : α) (l : List α),
    l.isSuffixOf (impl.leftpad.leftpad n a l)

def spec_leftpadString_length (impl : RepoImpl) : Prop :=
  ∀ (n : Nat) (a : Char) (s : String),
    (impl.leftpad.leftpadString n a s).length = max n s.length

def spec_leftpadString_prefix (impl : RepoImpl) : Prop :=
  ∀ (n : Nat) (a : Char) (s : String),
    (List.replicate (n - s.length) a) <+: (impl.leftpad.leftpadString n a s).toList

def spec_leftpadString_suffix (impl : RepoImpl) : Prop :=
  ∀ (n : Nat) (a : Char) (s : String),
    s.toList <:+ (impl.leftpad.leftpadString n a s).toList
