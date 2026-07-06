import LinkedList.Harness

/-!
# LinkedList.Spec.IsPalindrome

Specifications for palindrome-checking operations.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- isPalindrome l is true iff l equals its own reverse. -/
def spec_palindrome_isPalindrome_eq_reverse (impl : RepoImpl) : Prop :=
  ∀ (l : List Int),
    impl.linkedList.palindrome_isPalindrome l = (l == l.reverse)

/-- The stack-based palindrome check agrees with the primary implementation. -/
def spec_palindrome_isPalindromeStack_agrees (impl : RepoImpl) : Prop :=
  ∀ (l : List Int),
    impl.linkedList.palindrome_isPalindromeStack l
      = impl.linkedList.palindrome_isPalindrome l

/-- The dict-based palindrome check agrees with the primary implementation. -/
def spec_palindrome_isPalindromeDict_agrees (impl : RepoImpl) : Prop :=
  ∀ (l : List Int),
    impl.linkedList.palindrome_isPalindromeDict l
      = impl.linkedList.palindrome_isPalindrome l

/-- The primary palindrome checker agrees with the independent print-reverse API. -/
def spec_palindrome_agrees_with_print_reverse (impl : RepoImpl) : Prop :=
  ∀ (l : List Int),
    impl.linkedList.palindrome_isPalindrome l =
      (l == impl.linkedList.printrev_inReverse l)

/-- Any list of the form l ++ [a] ++ l.reverse is a palindrome (structural witness family). -/
def spec_palindrome_palindrome_lists_true (impl : RepoImpl) : Prop :=
  ∀ (l : List Int) (a : Int),
    impl.linkedList.palindrome_isPalindrome (l ++ [a] ++ l.reverse) = true

/-- PR-#35 PalindromeIffReverse: Prop-level iff between palindrome check and equality to reverse. -/
def spec_palindrome_iff_reverse (impl : RepoImpl) : Prop :=
  ∀ (l : List Int),
    impl.linkedList.palindrome_isPalindrome l = true ↔ l = l.reverse
