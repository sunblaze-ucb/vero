import Bidict.Harness

/-!
# Bidict.Test

`#guard` conformance tests. Guards run against `canonical.bidict.*` so that
the test suite goes through the benchmark `RepoImpl` indirection — pre-agent-gen
replaces the curator's reference impls (inside `!benchmark @start code` markers)
with `sorry`, and these guards then catch regressions in the LLM-completed
implementations.

DO NOT MODIFY — infrastructure.
-/

open Bidict OnDupAction

-- ── Helpers ──────────────────────────────────────────────────

/-- Test an Except.ok result against an expected value. -/
private def checkOk {E V : Type} [BEq V] (e : Except E V) (expected : V) : Bool :=
  match e with
  | .ok v  => v == expected
  | .error _ => false

/-- Test an Except.error result against an expected error. -/
private def checkErr {E V : Type} [BEq E] (e : Except E V) (expected : E) : Bool :=
  match e with
  | .ok _    => false
  | .error e => e == expected

-- ── BidictBase: inverse ────────────────────────────────────

#guard canonical.bidict.inverse (init (HashMap.ofList [(1, "a"), (2, "b")])) ==
       init (HashMap.ofList [("a", 1), ("b", 2)])

#guard canonical.bidict.inverse (init (HashMap.ofList [(3, "x"), (4, "y"), (5, "z")])) ==
       init (HashMap.ofList [("x", 3), ("y", 4), ("z", 5)])

#guard canonical.bidict.inverse (init (HashMap.ofList [(10, "ten")])) ==
       init (HashMap.ofList [("ten", 10)])

#guard canonical.bidict.inverse (init (HashMap.ofList [(0, "zero")])) ==
       init (HashMap.ofList [("zero", 0)])

#guard canonical.bidict.inverse (init (HashMap.ofList ([] : List (Nat × String)))) ==
       init (HashMap.ofList ([] : List (String × Nat)))

-- inverse-of-inverse roundtrip
#guard canonical.bidict.inverse
         (canonical.bidict.inverse (init (HashMap.ofList [(1, "a"), (2, "b")]))) ==
       init (HashMap.ofList [(1, "a"), (2, "b")])

-- ── BidictBase: inv ───────────────────────────────────────

#guard canonical.bidict.inv (init (HashMap.ofList [(1, "a"), (2, "b")])) ==
       init (HashMap.ofList [("a", 1), ("b", 2)])

#guard canonical.bidict.inv (init (HashMap.ofList [(0, "zero")])) ==
       init (HashMap.ofList [("zero", 0)])

#guard canonical.bidict.inv (init (HashMap.ofList ([] : List (Nat × String)))) ==
       init (HashMap.ofList ([] : List (String × Nat)))

-- `inv` is an alias for `inverse`
#guard canonical.bidict.inv (init (HashMap.ofList [(7, "seven"), (8, "eight")])) ==
       canonical.bidict.inverse (init (HashMap.ofList [(7, "seven"), (8, "eight")]))

-- ── BidictBase: copy ──────────────────────────────────────

#guard canonical.bidict.copy (init (HashMap.ofList [(1, "a"), (2, "b")])) ==
       init (HashMap.ofList [(1, "a"), (2, "b")])

#guard canonical.bidict.copy (init (HashMap.ofList ([] : List (Nat × String)))) ==
       init (HashMap.ofList ([] : List (Nat × String)))

#guard canonical.bidict.copy (init (HashMap.ofList [(42, "answer")])) ==
       init (HashMap.ofList [(42, "answer")])

#guard canonical.bidict.copy (init (HashMap.ofList [(1, "a"), (2, "b"), (3, "c")])) ==
       init (HashMap.ofList [(1, "a"), (2, "b"), (3, "c")])

-- ── BidictBase: union ─────────────────────────────────────
-- self wins on key conflict; self keys come first.

#guard canonical.bidict.union (init (HashMap.ofList [(1, "a"), (2, "b")]))
                              (init (HashMap.ofList [(3, "c"), (4, "d")])) ==
       init (HashMap.ofList [(1, "a"), (2, "b"), (3, "c"), (4, "d")])

#guard canonical.bidict.union (init (HashMap.ofList [(1, "x"), (2, "y")]))
                              (init (HashMap.ofList [(2, "y"), (3, "z")])) ==
       init (HashMap.ofList [(1, "x"), (2, "y"), (3, "z")])

#guard canonical.bidict.union (init (HashMap.ofList ([] : List (Nat × String))))
                              (init (HashMap.ofList [(10, "ten")])) ==
       init (HashMap.ofList [(10, "ten")])

#guard canonical.bidict.union (init (HashMap.ofList [(1, "a"), (2, "b")]))
                              (init (HashMap.ofList [(1, "a")])) ==
       init (HashMap.ofList [(1, "a"), (2, "b")])

-- ── BidictBase: runion ────────────────────────────────────
-- other wins on key conflict; self order preserved; new from other appended.

#guard canonical.bidict.runion (init (HashMap.ofList [(1, "a"), (2, "b")]))
                               (init (HashMap.ofList [(2, "x"), (3, "c")])) ==
       init (HashMap.ofList [(1, "a"), (2, "x"), (3, "c")])

#guard canonical.bidict.runion (init (HashMap.ofList [(10, "ten")]))
                               (init (HashMap.ofList [(10, "TEN"), (11, "eleven")])) ==
       init (HashMap.ofList [(10, "TEN"), (11, "eleven")])

#guard canonical.bidict.runion (init (HashMap.ofList ([] : List (Nat × String))))
                               (init (HashMap.ofList [(5, "five")])) ==
       init (HashMap.ofList [(5, "five")])

#guard canonical.bidict.runion (init (HashMap.ofList [(0, "zero")]))
                               (init (HashMap.ofList ([] : List (Nat × String)))) ==
       init (HashMap.ofList [(0, "zero")])

-- ── BidictBase: length ────────────────────────────────────

#guard canonical.bidict.length (init (HashMap.ofList ([] : List (Nat × String)))) == 0
#guard canonical.bidict.length (init (HashMap.ofList [(1, "a")])) == 1
#guard canonical.bidict.length (init (HashMap.ofList [(1, "a"), (2, "b")])) == 2
#guard canonical.bidict.length (init (HashMap.ofList [(10, "x"), (11, "y"), (12, "z")])) == 3

-- ── BidictBase: iter ─────────────────────────────────────
-- Returns keys in insertion order (list-preserving).

#guard canonical.bidict.iter (init (HashMap.ofList [(1, "a"), (2, "b")])) == [1, 2]
#guard canonical.bidict.iter (init (HashMap.ofList [(10, "ten"), (20, "twenty")])) == [10, 20]
#guard canonical.bidict.iter (init (HashMap.ofList ([] : List (Nat × String)))) == []
#guard canonical.bidict.iter (init (HashMap.ofList [(0, "zero")])) == [0]
#guard canonical.bidict.iter (init (HashMap.ofList [(3, "c"), (1, "a"), (2, "b")])) == [3, 1, 2]

-- ── BidictBase: getitem ───────────────────────────────────
-- Returns Option VT; some v when found.

#guard canonical.bidict.getitem (init (HashMap.ofList [(1, "a"), (2, "b")])) 1 == some "a"
#guard canonical.bidict.getitem (init (HashMap.ofList [(1, "a"), (2, "b")])) 2 == some "b"
#guard canonical.bidict.getitem (init (HashMap.ofList [(10, "ten"), (20, "twenty")])) 20 == some "twenty"
#guard canonical.bidict.getitem (init (HashMap.ofList [(5, "five"), (6, "six")])) 6 == some "six"
#guard canonical.bidict.getitem (init (HashMap.ofList [(1, "a"), (2, "b")])) 99 == none

-- ── Iter: iteritems ──────────────────────────────────────

#guard canonical.bidict.iteritems (HashMap.ofList [(1, "a"), (2, "b"), (3, "c")]) ==
       [(1, "a"), (2, "b"), (3, "c")]
#guard canonical.bidict.iteritems (HashMap.ofList [(10, "ten"), (20, "twenty")]) ==
       [(10, "ten"), (20, "twenty")]
#guard canonical.bidict.iteritems (HashMap.ofList [(0, "zero")]) == [(0, "zero")]
#guard canonical.bidict.iteritems (HashMap.ofList ([] : List (Nat × String))) == []

-- ── Iter: inverted ────────────────────────────────────────

#guard canonical.bidict.inverted (HashMap.ofList [(1, "a"), (2, "b"), (3, "c")]) ==
       [("a", 1), ("b", 2), ("c", 3)]
#guard canonical.bidict.inverted (HashMap.ofList [(10, "ten"), (20, "twenty")]) ==
       [("ten", 10), ("twenty", 20)]
#guard canonical.bidict.inverted (HashMap.ofList [(0, "zero")]) == [("zero", 0)]
#guard canonical.bidict.inverted (HashMap.ofList ([] : List (Nat × String))) == []

-- ── FrozenBidict: frozenBidictHash ───────────────────────
-- Order-independent: equal contents → equal hash. Empty bidict hashes to 0.

#guard canonical.bidict.frozenBidictHash
         (init (HashMap.ofList [(1, "a"), (2, "b")])) ==
       canonical.bidict.frozenBidictHash
         (init (HashMap.ofList [(2, "b"), (1, "a")]))

#guard canonical.bidict.frozenBidictHash
         (init (HashMap.ofList ([] : List (Nat × String)))) ==
       canonical.bidict.frozenBidictHash
         (init (HashMap.ofList ([] : List (Nat × String))))

#guard canonical.bidict.frozenBidictHash
         (init (HashMap.ofList ([] : List (Nat × String)))) == 0

#guard canonical.bidict.frozenBidictHash
         (init (HashMap.ofList [(1, "a"), (2, "b"), (3, "c")])) ==
       canonical.bidict.frozenBidictHash
         (init (HashMap.ofList [(3, "c"), (1, "a"), (2, "b")]))

--   hash (init ...) but hash on List is a different UInt64-based function;
--   commutativity tests above are the curator's substitute.

-- ── MutableBidict: initMutableBidict ─────────────────────

#guard canonical.bidict.initMutableBidict
         (init (HashMap.ofList [(1, "a"), (2, "b")]))
         { key := raise, val := raise } ==
       { data := [(1, "a"), (2, "b")], ondup := { key := raise, val := raise } }

#guard canonical.bidict.initMutableBidict
         (init (HashMap.ofList ([] : List (Nat × String))))
         { key := raise, val := raise } ==
       { data := [], ondup := { key := raise, val := raise } }

#guard canonical.bidict.initMutableBidict
         (init (HashMap.ofList [(7, "seven")]))
         { key := dropOld, val := dropNew } ==
       { data := [(7, "seven")], ondup := { key := dropOld, val := dropNew } }

-- ── MutableBidict: delItem ────────────────────────────────

#guard canonical.bidict.delItem
         (canonical.bidict.initMutableBidict
            (init (HashMap.ofList [(1, "a"), (2, "b")]))
            { key := raise, val := raise }) 1 ==
       canonical.bidict.initMutableBidict
         (init (HashMap.ofList [(2, "b")])) { key := raise, val := raise }

-- key absent → no-op
#guard canonical.bidict.delItem
         (canonical.bidict.initMutableBidict
            (init (HashMap.ofList [(5, "x"), (6, "y")]))
            { key := raise, val := raise }) 10 ==
       canonical.bidict.initMutableBidict
         (init (HashMap.ofList [(5, "x"), (6, "y")])) { key := raise, val := raise }

-- delete from singleton → empty
#guard canonical.bidict.delItem
         (canonical.bidict.initMutableBidict
            (init (HashMap.ofList [(42, "answer")]))
            { key := raise, val := raise }) 42 ==
       canonical.bidict.initMutableBidict
         (init (HashMap.ofList ([] : List (Nat × String))))
         { key := raise, val := raise }

-- ── MutableBidict: setItem ───────────────────────────────

-- ok: new key and new value
#guard checkOk
       (canonical.bidict.setItem
          (canonical.bidict.initMutableBidict
             (init (HashMap.ofList [(1, "a"), (2, "b")]))
             { key := raise, val := raise }) 3 "c")
       (canonical.bidict.initMutableBidict
          (init (HashMap.ofList [(1, "a"), (2, "b"), (3, "c")]))
          { key := raise, val := raise })

-- ok: empty bidict
#guard checkOk
       (canonical.bidict.setItem
          (canonical.bidict.initMutableBidict
             (init (HashMap.ofList ([] : List (Nat × String))))
             { key := raise, val := raise }) 1 "alpha")
       (canonical.bidict.initMutableBidict
          (init (HashMap.ofList [(1, "alpha")])) { key := raise, val := raise })

-- ok: duplicate key with on_dup.key = dropNew → keep self unchanged
#guard checkOk
       (canonical.bidict.setItem
          (canonical.bidict.initMutableBidict
             (init (HashMap.ofList [(1, "a")]))
             { key := dropNew, val := raise }) 1 "b")
       (canonical.bidict.initMutableBidict
          (init (HashMap.ofList [(1, "a")])) { key := dropNew, val := raise })

-- error: duplicate key with on_dup.key = raise
#guard checkErr
       (canonical.bidict.setItem
          (canonical.bidict.initMutableBidict
             (init (HashMap.ofList [(1, "a")]))
             { key := raise, val := raise }) 1 "b")
       DuplicationError.duplicateKeyError

--   DuplicationError.keyDup but Exc.lean defines DuplicationError.duplicateKeyError;
--   curator chose the explicit `duplicateKeyError` name in Exc.lean and the test
--   above asserts that.

-- ── MutableBidict: forceput ──────────────────────────────

#guard canonical.bidict.forceput
         (canonical.bidict.initMutableBidict
            (init (HashMap.ofList [(1, "a"), (2, "b")]))
            { key := raise, val := raise }) 3 "c" ==
       canonical.bidict.initMutableBidict
         (init (HashMap.ofList [(1, "a"), (2, "b"), (3, "c")]))
         { key := raise, val := raise }

-- overwrite existing key in-place
#guard canonical.bidict.forceput
         (canonical.bidict.initMutableBidict
            (init (HashMap.ofList [(1, "a")]))
            { key := raise, val := raise }) 1 "b" ==
       canonical.bidict.initMutableBidict
         (init (HashMap.ofList [(1, "b")])) { key := raise, val := raise }

#guard canonical.bidict.forceput
         (canonical.bidict.initMutableBidict
            (init (HashMap.ofList [(5, "x"), (6, "y")]))
            { key := raise, val := raise }) 5 "z" ==
       canonical.bidict.initMutableBidict
         (init (HashMap.ofList [(5, "z"), (6, "y")])) { key := raise, val := raise }

-- ── MutableBidict: clear ─────────────────────────────────

#guard canonical.bidict.clear
         (canonical.bidict.initMutableBidict
            (init (HashMap.ofList [(1, "a"), (2, "b")]))
            { key := raise, val := raise }) ==
       canonical.bidict.initMutableBidict
         (init (HashMap.ofList ([] : List (Nat × String))))
         { key := raise, val := raise }

-- clear of empty bidict is empty
#guard canonical.bidict.clear
         (canonical.bidict.initMutableBidict
            (init (HashMap.ofList ([] : List (Nat × String))))
            { key := raise, val := raise }) ==
       canonical.bidict.initMutableBidict
         (init (HashMap.ofList ([] : List (Nat × String))))
         { key := raise, val := raise }

-- clear preserves the ondup policy
#guard canonical.bidict.clear
         (canonical.bidict.initMutableBidict
            (init (HashMap.ofList [(1, "a")]))
            { key := dropOld, val := dropNew }) ==
       canonical.bidict.initMutableBidict
         (init (HashMap.ofList ([] : List (Nat × String))))
         { key := dropOld, val := dropNew }

-- ── MutableBidict: pop ────────────────────────────────────
-- Returns (newMutableBidict, Sum.inl val) when found.

#guard let (mb', res) := canonical.bidict.pop
         (canonical.bidict.initMutableBidict
            (init (HashMap.ofList [(1, "a"), (2, "b")]))
            { key := raise, val := raise }) 1 "default"
       mb' == canonical.bidict.initMutableBidict
                (init (HashMap.ofList [(2, "b")]))
                { key := raise, val := raise } &&
       (match res with | .inl v => v == "a" | .inr _ => false)

#guard let (mb', res) := canonical.bidict.pop
         (canonical.bidict.initMutableBidict
            (init (HashMap.ofList [(3, "x"), (4, "y")]))
            { key := raise, val := raise }) 5 "none"
       mb' == canonical.bidict.initMutableBidict
                (init (HashMap.ofList [(3, "x"), (4, "y")]))
                { key := raise, val := raise } &&
       (match res with | .inl _ => false | .inr d => d == "none")

-- pop from singleton → empty
#guard let (mb', res) := canonical.bidict.pop
         (canonical.bidict.initMutableBidict
            (init (HashMap.ofList [(42, "answer")]))
            { key := raise, val := raise }) 42 "missing"
       mb' == canonical.bidict.initMutableBidict
                (init (HashMap.ofList ([] : List (Nat × String))))
                { key := raise, val := raise } &&
       (match res with | .inl v => v == "answer" | .inr _ => false)

-- ── MutableBidict: popitem ────────────────────────────────
-- Returns some (newMutableBidict, (key, val)); pops first entry.

#guard match canonical.bidict.popitem
               (canonical.bidict.initMutableBidict
                  (init (HashMap.ofList [(1, "a"), (2, "b")]))
                  { key := raise, val := raise }) with
       | some (mb', kv) =>
           mb' == canonical.bidict.initMutableBidict
                    (init (HashMap.ofList [(2, "b")]))
                    { key := raise, val := raise }
           && kv == (1, "a")
       | none => false

#guard match canonical.bidict.popitem
               (canonical.bidict.initMutableBidict
                  (init (HashMap.ofList [(42, "x")]))
                  { key := raise, val := raise }) with
       | some (mb', kv) =>
           mb' == canonical.bidict.initMutableBidict
                    (init (HashMap.ofList ([] : List (Nat × String))))
                    { key := raise, val := raise }
           && kv == (42, "x")
       | none => false

-- popitem on empty bidict → none
#guard match canonical.bidict.popitem
               (canonical.bidict.initMutableBidict
                  (init (HashMap.ofList ([] : List (Nat × String))))
                  { key := raise, val := raise }) with
       | some _ => false
       | none   => true

-- ── MutableBidict: update ─────────────────────────────────
-- ok cases (no conflict with on_dup.key = raise)

#guard checkOk
       (canonical.bidict.update
          (canonical.bidict.initMutableBidict
             (init (HashMap.ofList [(1, "a")]))
             { key := raise, val := raise })
          (init (HashMap.ofList [(2, "b"), (3, "c")])))
       (canonical.bidict.initMutableBidict
          (init (HashMap.ofList [(1, "a"), (2, "b"), (3, "c")]))
          { key := raise, val := raise })

#guard checkOk
       (canonical.bidict.update
          (canonical.bidict.initMutableBidict
             (init (HashMap.ofList ([] : List (Nat × String))))
             { key := raise, val := raise })
          (init (HashMap.ofList ([] : List (Nat × String)))))
       (canonical.bidict.initMutableBidict
          (init (HashMap.ofList ([] : List (Nat × String))))
          { key := raise, val := raise })

-- error: duplicate key with on_dup.key = raise
#guard checkErr
       (canonical.bidict.update
          (canonical.bidict.initMutableBidict
             (init (HashMap.ofList [(1, "a")]))
             { key := raise, val := raise })
          (init (HashMap.ofList [(1, "b")])))
       DuplicationError.duplicateKeyError

--   inl/inr (Sum) but our impl returns Except.ok/Except.error; the error case
--   above uses checkErr to assert the curator-chosen `duplicateKeyError`.

-- ── MutableBidict: forceupdate ────────────────────────────

#guard canonical.bidict.forceupdate
         (canonical.bidict.initMutableBidict
            (init (HashMap.ofList [(1, "a")]))
            { key := raise, val := raise })
         (init (HashMap.ofList [(1, "x"), (2, "b")])) ==
       canonical.bidict.initMutableBidict
         (init (HashMap.ofList [(1, "x"), (2, "b")]))
         { key := raise, val := raise }

#guard canonical.bidict.forceupdate
         (canonical.bidict.initMutableBidict
            (init (HashMap.ofList [(2, "b")]))
            { key := raise, val := raise })
         (init (HashMap.ofList [(3, "c")])) ==
       canonical.bidict.initMutableBidict
         (init (HashMap.ofList [(2, "b"), (3, "c")]))
         { key := raise, val := raise }

#guard canonical.bidict.forceupdate
         (canonical.bidict.initMutableBidict
            (init (HashMap.ofList ([] : List (Nat × String))))
            { key := raise, val := raise })
         (init (HashMap.ofList [(0, "zero")])) ==
       canonical.bidict.initMutableBidict
         (init (HashMap.ofList [(0, "zero")]))
         { key := raise, val := raise }

-- ── MutableBidict: putall ─────────────────────────────────

#guard canonical.bidict.putall
         (canonical.bidict.initMutableBidict
            (init (HashMap.ofList [(1, "a")]))
            { key := raise, val := raise })
         (init (HashMap.ofList [(2, "b"), (3, "c")]))
         { key := raise, val := raise } ==
       canonical.bidict.initMutableBidict
         (init (HashMap.ofList [(1, "a"), (2, "b"), (3, "c")]))
         { key := raise, val := raise }

-- merging an empty bidict is a no-op
#guard canonical.bidict.putall
         (canonical.bidict.initMutableBidict
            (init (HashMap.ofList [(1, "a"), (2, "b")]))
            { key := raise, val := raise })
         (init (HashMap.ofList ([] : List (Nat × String))))
         { key := raise, val := raise } ==
       canonical.bidict.initMutableBidict
         (init (HashMap.ofList [(1, "a"), (2, "b")]))
         { key := raise, val := raise }

-- putall preserves self.ondup even after using mergeOndup for the merge pass
#guard (canonical.bidict.putall
         (canonical.bidict.initMutableBidict
            (init (HashMap.ofList [(1, "a")]))
            { key := dropOld, val := dropOld })
         (init (HashMap.ofList [(2, "b")]))
         { key := raise, val := raise }).ondup ==
       { key := dropOld, val := dropOld }

-- ── OrderedBidict: initOrderedBidict ─────────────────────

#guard canonical.bidict.initOrderedBidict (init (HashMap.ofList [(1, "a"), (2, "b")])) ==
       canonical.bidict.initOrderedBidict (init (HashMap.ofList [(1, "a"), (2, "b")]))

#guard canonical.bidict.initOrderedBidict (init (HashMap.ofList ([] : List (Nat × String)))) ==
       canonical.bidict.initOrderedBidict (init (HashMap.ofList ([] : List (Nat × String))))

#guard canonical.bidict.initOrderedBidict (init (HashMap.ofList [(7, "seven")])) ==
       canonical.bidict.initOrderedBidict (init (HashMap.ofList [(7, "seven")]))

-- ── OrderedBidict: iterOrderedBidict ─────────────────────
-- Returns keys in insertion order; reverse flag flips it.

#guard canonical.bidict.iterOrderedBidict
         (canonical.bidict.initOrderedBidict (init (HashMap.ofList [(1, "a"), (2, "b")]))) false ==
       [1, 2]

#guard canonical.bidict.iterOrderedBidict
         (canonical.bidict.initOrderedBidict (init (HashMap.ofList [(1, "a"), (2, "b")]))) true ==
       [2, 1]

#guard canonical.bidict.iterOrderedBidict
         (canonical.bidict.initOrderedBidict (init (HashMap.ofList ([] : List (Nat × String))))) false ==
       []

#guard canonical.bidict.iterOrderedBidict
         (canonical.bidict.initOrderedBidict (init (HashMap.ofList [(5, "x"), (3, "y"), (1, "z")]))) false ==
       [5, 3, 1]

#guard canonical.bidict.iterOrderedBidict
         (canonical.bidict.initOrderedBidict (init (HashMap.ofList [(5, "x"), (3, "y"), (1, "z")]))) true ==
       [1, 3, 5]

-- ── OrderedBidict: inverseOrderedBidict ──────────────────

#guard canonical.bidict.inverseOrderedBidict
         (canonical.bidict.initOrderedBidict (init (HashMap.ofList [(1, "a"), (2, "b")]))) ==
       canonical.bidict.initOrderedBidict (init (HashMap.ofList [("a", 1), ("b", 2)]))

#guard canonical.bidict.inverseOrderedBidict
         (canonical.bidict.initOrderedBidict (init (HashMap.ofList [(0, "zero")]))) ==
       canonical.bidict.initOrderedBidict (init (HashMap.ofList [("zero", 0)]))

#guard canonical.bidict.inverseOrderedBidict
         (canonical.bidict.initOrderedBidict (init (HashMap.ofList ([] : List (Nat × String))))) ==
       canonical.bidict.initOrderedBidict (init (HashMap.ofList ([] : List (String × Nat))))

-- inverse-of-inverse roundtrip
#guard canonical.bidict.inverseOrderedBidict
         (canonical.bidict.inverseOrderedBidict
            (canonical.bidict.initOrderedBidict
               (init (HashMap.ofList [(1, "a"), (2, "b")])))) ==
       canonical.bidict.initOrderedBidict (init (HashMap.ofList [(1, "a"), (2, "b")]))

-- ── OrderedBidict: invOrderedBidict ──────────────────────

#guard canonical.bidict.invOrderedBidict
         (canonical.bidict.initOrderedBidict (init (HashMap.ofList [(1, "a"), (2, "b")]))) ==
       canonical.bidict.initOrderedBidict (init (HashMap.ofList [("a", 1), ("b", 2)]))

#guard canonical.bidict.invOrderedBidict
         (canonical.bidict.initOrderedBidict (init (HashMap.ofList ([] : List (Nat × String))))) ==
       canonical.bidict.initOrderedBidict (init (HashMap.ofList ([] : List (String × Nat))))

-- alias for inverseOrderedBidict
#guard canonical.bidict.invOrderedBidict
         (canonical.bidict.initOrderedBidict (init (HashMap.ofList [(7, "seven"), (8, "eight")]))) ==
       canonical.bidict.inverseOrderedBidict
         (canonical.bidict.initOrderedBidict (init (HashMap.ofList [(7, "seven"), (8, "eight")])))

-- ── OrderedBidict: clearOrderedBidict ────────────────────

#guard canonical.bidict.clearOrderedBidict
         (canonical.bidict.initOrderedBidict (init (HashMap.ofList [(1, "a"), (2, "b")]))) ==
       canonical.bidict.initOrderedBidict (init (HashMap.ofList ([] : List (Nat × String))))

#guard canonical.bidict.clearOrderedBidict
         (canonical.bidict.initOrderedBidict (init (HashMap.ofList ([] : List (Nat × String))))) ==
       canonical.bidict.initOrderedBidict (init (HashMap.ofList ([] : List (Nat × String))))

#guard canonical.bidict.clearOrderedBidict
         (canonical.bidict.initOrderedBidict (init (HashMap.ofList [(5, "x"), (6, "y"), (7, "z")]))) ==
       canonical.bidict.initOrderedBidict (init (HashMap.ofList ([] : List (Nat × String))))

-- ── OrderedBidict: popOrderedBidict ──────────────────────
-- Returns some (newOrderedBidict, val); none if key absent.

#guard match canonical.bidict.popOrderedBidict
               (canonical.bidict.initOrderedBidict (init (HashMap.ofList [(1, "a"), (2, "b")]))) 1 with
       | some (od', v) =>
           od' == canonical.bidict.initOrderedBidict (init (HashMap.ofList [(2, "b")])) && v == "a"
       | none => false

#guard match canonical.bidict.popOrderedBidict
               (canonical.bidict.initOrderedBidict (init (HashMap.ofList [(3, "x"), (4, "y")]))) 4 with
       | some (od', v) =>
           od' == canonical.bidict.initOrderedBidict (init (HashMap.ofList [(3, "x")])) && v == "y"
       | none => false

-- key absent → none
#guard match canonical.bidict.popOrderedBidict
               (canonical.bidict.initOrderedBidict (init (HashMap.ofList [(1, "a")]))) 99 with
       | some _ => false
       | none   => true

-- ── OrderedBidict: popitemOrderedBidict ──────────────────
-- last=true removes last; last=false removes first.

#guard match canonical.bidict.popitemOrderedBidict
               (canonical.bidict.initOrderedBidict (init (HashMap.ofList [(1, "a"), (2, "b")]))) true with
       | some (od', kv) =>
           od' == canonical.bidict.initOrderedBidict (init (HashMap.ofList [(1, "a")])) && kv == (2, "b")
       | none => false

#guard match canonical.bidict.popitemOrderedBidict
               (canonical.bidict.initOrderedBidict (init (HashMap.ofList [(3, "x"), (4, "y")]))) false with
       | some (od', kv) =>
           od' == canonical.bidict.initOrderedBidict (init (HashMap.ofList [(4, "y")])) && kv == (3, "x")
       | none => false

-- empty bidict → none for either flag
#guard match canonical.bidict.popitemOrderedBidict
               (canonical.bidict.initOrderedBidict
                  (init (HashMap.ofList ([] : List (Nat × String))))) true with
       | some _ => false
       | none   => true

#guard match canonical.bidict.popitemOrderedBidict
               (canonical.bidict.initOrderedBidict
                  (init (HashMap.ofList ([] : List (Nat × String))))) false with
       | some _ => false
       | none   => true

-- ── OrderedBidict: moveToEndOrderedBidict ────────────────

#guard canonical.bidict.moveToEndOrderedBidict
         (canonical.bidict.initOrderedBidict
            (init (HashMap.ofList [(1, "a"), (2, "b"), (3, "c")]))) 1 true ==
       canonical.bidict.initOrderedBidict
         (init (HashMap.ofList [(2, "b"), (3, "c"), (1, "a")]))

#guard canonical.bidict.moveToEndOrderedBidict
         (canonical.bidict.initOrderedBidict
            (init (HashMap.ofList [(4, "x"), (5, "y")]))) 5 false ==
       canonical.bidict.initOrderedBidict
         (init (HashMap.ofList [(5, "y"), (4, "x")]))

-- key absent → no-op
#guard canonical.bidict.moveToEndOrderedBidict
         (canonical.bidict.initOrderedBidict
            (init (HashMap.ofList [(1, "a"), (2, "b")]))) 99 true ==
       canonical.bidict.initOrderedBidict
         (init (HashMap.ofList [(1, "a"), (2, "b")]))

-- ── OrderedBidict: keysOrderedBidict ─────────────────────

#guard canonical.bidict.keysOrderedBidict
         (canonical.bidict.initOrderedBidict (init (HashMap.ofList [(1, "a"), (2, "b")]))) ==
       [1, 2]

#guard canonical.bidict.keysOrderedBidict
         (canonical.bidict.initOrderedBidict (init (HashMap.ofList [(3, "x"), (4, "y"), (5, "z")]))) ==
       [3, 4, 5]

#guard canonical.bidict.keysOrderedBidict
         (canonical.bidict.initOrderedBidict
            (init (HashMap.ofList ([] : List (Nat × String))))) == []

-- ── OrderedBidict: itemsOrderedBidict ────────────────────

#guard canonical.bidict.itemsOrderedBidict
         (canonical.bidict.initOrderedBidict (init (HashMap.ofList [(1, "a"), (2, "b")]))) ==
       [(1, "a"), (2, "b")]

#guard canonical.bidict.itemsOrderedBidict
         (canonical.bidict.initOrderedBidict (init (HashMap.ofList [(3, "x"), (4, "y"), (5, "z")]))) ==
       [(3, "x"), (4, "y"), (5, "z")]

#guard canonical.bidict.itemsOrderedBidict
         (canonical.bidict.initOrderedBidict
            (init (HashMap.ofList ([] : List (Nat × String))))) == []
