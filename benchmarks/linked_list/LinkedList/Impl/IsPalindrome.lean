-- !benchmark @start imports
-- !benchmark @end imports

/-!
# LinkedList.Impl.IsPalindrome

Three approaches to palindrome checking on an integer-linked list:
- `isPalindrome`: split/reverse second half, compare.
- `isPalindromeStack`: stack-based comparison.
- `isPalindromeDict`: dict/position-symmetry check.

All three produce equivalent Boolean results. In this Lean model the
list is `List Int`; the Python `ListNode | None` input is modelled as
`List Int` (empty list = null head = not a palindrome by convention,
but an empty list IS a palindrome).

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Types (fixed vocabulary) ─────────────────────────────────────
/-- An integer linked list for palindrome testing, modelled as `List Int`. -/
abbrev Palindrome.ListNode := Int

namespace Palindrome

-- ── API signatures (fixed vocabulary) ────────────────────────────
abbrev IsPalindromeSig      := List Int → Bool
abbrev IsPalindromeStackSig := List Int → Bool
abbrev IsPalindromeDict     := List Int → Bool

end Palindrome

-- ── Implementations (LLM task) ───────────────────────────────────

-- !benchmark @start code_aux def=palindrome_isPalindrome
-- !benchmark @end code_aux def=palindrome_isPalindrome

def Palindrome.isPalindrome : Palindrome.IsPalindromeSig :=
-- !benchmark @start code def=palindrome_isPalindrome
  fun l => l == l.reverse
-- !benchmark @end code def=palindrome_isPalindrome

-- !benchmark @start code_aux def=palindrome_isPalindromeStack
-- !benchmark @end code_aux def=palindrome_isPalindromeStack

def Palindrome.isPalindromeStack : Palindrome.IsPalindromeStackSig :=
-- !benchmark @start code def=palindrome_isPalindromeStack
  -- Stack approach: push second half, pop and compare with first half.
  fun l =>
    let mid   := l.length / 2
    let first := l.take mid
    let stack := (l.drop (l.length - mid)).reverse
    first == stack
-- !benchmark @end code def=palindrome_isPalindromeStack

-- !benchmark @start code_aux def=palindrome_isPalindromeDict
-- !benchmark @end code_aux def=palindrome_isPalindromeDict

def Palindrome.isPalindromeDict : Palindrome.IsPalindromeDict :=
-- !benchmark @start code def=palindrome_isPalindromeDict
  -- Dict/symmetry approach: compare element i with element (n-1-i).
  fun l => l == l.reverse
-- !benchmark @end code def=palindrome_isPalindromeDict
