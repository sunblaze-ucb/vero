-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Textwrap.Impl.Wrap

Line-wrapping operations `wrap` and `shorten`.

A *word* is represented by its length (`Nat`), so the input is a
`List Nat` of word-lengths and `wrap`'s output is a `List (List Nat)` —
one inner list per output line, holding the word-lengths placed on that
line, in order. A word longer than `width` cannot be split: it occupies
a line of its own that exceeds `width`.

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- A line is the list of word-lengths placed on it, in order. -/
abbrev Line := List Nat

namespace Textwrap

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `wrap chunks width`: pack `chunks` (word-lengths) into lines so no
    line's total exceeds `width` unless it holds a single over-long
    word, breaking only between whole words. -/
abbrev WrapSig := List Nat → Nat → List Line

/-- `shorten chunks width`: the leading run of words whose running total
    stays within `width`. -/
abbrev ShortenSig := List Nat → Nat → List Nat

end Textwrap

-- !benchmark @start global_aux
/-- Worker for `wrap`. Carries the line under construction and its
    running width as it consumes the remaining word-lengths. -/
def Textwrap.wrapGo : List Nat → Nat → Line → Nat → List Line
  | [], _, cur, _ => match cur with
    | [] => []
    | _  => [cur.reverse]
  | c :: rest, width, cur, curLen => match cur with
    | [] => Textwrap.wrapGo rest width [c] c
    | _  =>
      if curLen + c ≤ width then
        Textwrap.wrapGo rest width (c :: cur) (curLen + c)
      else
        cur.reverse :: Textwrap.wrapGo rest width [c] c

/-- Worker for `shorten`, tracking the width `used` by the words kept so
    far. -/
def Textwrap.shortenGo : List Nat → Nat → Nat → List Nat
  | [], _, _ => []
  | c :: rest, width, used =>
    if used + c ≤ width then c :: Textwrap.shortenGo rest width (used + c) else []
-- !benchmark @end global_aux

-- total occupied width of a line, the sum of its word-lengths. Frozen vocabulary
-- exposed so specs can reference it directly (like Ipaddress.coveredBy); never a
-- fillable slot or Bundle field.
def Textwrap.lineWidth : Line → Nat := fun line => line.sum

-- !benchmark @start code_aux def=wrap
-- !benchmark @end code_aux def=wrap

def Textwrap.wrap : Textwrap.WrapSig :=
-- !benchmark @start code def=wrap
  fun chunks width => Textwrap.wrapGo chunks width [] 0
-- !benchmark @end code def=wrap

-- !benchmark @start code_aux def=shorten
-- !benchmark @end code_aux def=shorten

def Textwrap.shorten : Textwrap.ShortenSig :=
-- !benchmark @start code def=shorten
  fun chunks width => Textwrap.shortenGo chunks width 0
-- !benchmark @end code def=shorten
