import Pyradix.Impl.Radix

/-!
# Pyradix.Test

Executable conformance tests. `#guard` assertions run against the
curator's reference implementations inside the `code` markers in
`Impl/Radix.lean`.

Addresses use the top byte for readability (`a * 2^24`): a `/8` prefix
`(net = a * 2^24, plen = 8)` covers exactly the addresses whose top byte
is `a`. A `/16` prefix narrows to the top two bytes, etc.

DO NOT MODIFY — infrastructure.
-/

open Pyradix

/-- `0x0A000000` = `10.0.0.0`. -/
private def a10 : Nat := 10 * 2 ^ 24
/-- `0x0A0B0000` = `10.11.0.0`. -/
private def a10_11 : Nat := 10 * 2 ^ 24 + 11 * 2 ^ 16
/-- `0x0A0B0C0D` = `10.11.12.13`. -/
private def q : Nat := 10 * 2 ^ 24 + 11 * 2 ^ 16 + 12 * 2 ^ 8 + 13
/-- `0x14000000` = `20.0.0.0` (top byte 20, not covered by 10/8). -/
private def a20 : Nat := 20 * 2 ^ 24

private def p8  : Prefix := { net := a10,    plen := 8,  value := 1 }
private def p16 : Prefix := { net := a10_11, plen := 16, value := 2 }
private def tbl : Table := [p8, p16]

-- ── searchBest: most-specific (longest) covering prefix ─────────
-- both 10/8 and 10.11/16 cover 10.11.12.13; the /16 is more specific.
#guard searchBest tbl q == some p16
#guard searchBest [p8] q == some p8                 -- only the /8 covers
#guard searchBest tbl a20 == none                   -- nothing covers 20.0.0.0
#guard searchBest ([] : Table) q == none            -- empty table
-- order-independent: the longer prefix still wins when listed first.
#guard searchBest [p16, p8] q == some p16

-- ── searchWorst: least-specific (shortest) covering prefix ──────
#guard searchWorst tbl q == some p8                  -- the /8 is least specific
#guard searchWorst [p16] q == some p16
#guard searchWorst tbl a20 == none

-- ── searchExact: exact-block lookup ─────────────────────────────
#guard searchExact tbl a10 8 == some p8
#guard searchExact tbl a10_11 16 == some p16
#guard searchExact tbl a10 16 == none                -- right net, wrong length
#guard searchExact tbl q 8 == some p8                -- q masks to 10/8

-- ── add / delete ────────────────────────────────────────────────
#guard searchExact (add tbl { net := a20, plen := 8, value := 9 }) a20 8
        == some { net := a20, plen := 8, value := 9 }
#guard searchExact (delete tbl a10 8) a10 8 == none  -- block removed
#guard searchExact (delete tbl a10 8) a10_11 16 == some p16  -- other block kept
-- add overwrites the same block (same net mask + plen):
#guard searchExact (add tbl { net := a10, plen := 8, value := 99 }) a10 8
        == some { net := a10, plen := 8, value := 99 }

-- ── covered: entries contained in a query block ─────────────────
-- the /16 lies inside 10/8; the /8 itself does too (plen 8 ≥ 8, net covered).
#guard covered tbl a10 8 == [p8, p16]
#guard covered tbl a10_11 16 == [p16]                -- only the /16 fits inside /16
#guard covered tbl a20 8 == []                       -- nothing inside 20/8
