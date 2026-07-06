import Bidict.Impl.BidictBase
import Bidict.Impl.Iter
import Bidict.Impl.FrozenBidict
import Bidict.Impl.MutableBidict
import Bidict.Impl.OrderedBidict

/-!
# Bidict.Bundle

Per-package implementation bundle for the `Bidict` root package.
Collects all 31 API signatures into one concrete structure.

Because the bidict library is polymorphic, each field is universally
quantified over `KT` and `VT` (and whichever instances the implementation
actually requires). Field types match the exact types of the reference
implementations so that `canonical` can be written without coercions.

DO NOT MODIFY — benchmark infrastructure.
-/

structure BidictBundle where
  -- BidictBase APIs (8)
  inverse :
    ∀ {KT VT : Type}, BidictBase KT VT → BidictBase VT KT
  inv :
    ∀ {KT VT : Type}, BidictBase KT VT → BidictBase VT KT
  copy :
    ∀ {KT VT : Type}, BidictBase KT VT → BidictBase KT VT
  union :
    ∀ {KT VT : Type} [BEq KT],
      BidictBase KT VT → BidictBase KT VT → BidictBase KT VT
  runion :
    ∀ {KT VT : Type} [BEq KT],
      BidictBase KT VT → BidictBase KT VT → BidictBase KT VT
  length :
    ∀ {KT VT : Type}, BidictBase KT VT → Nat
  iter :
    ∀ {KT VT : Type}, BidictBase KT VT → List KT
  getitem :
    ∀ {KT VT : Type} [BEq KT], BidictBase KT VT → KT → Option VT
  -- Iter APIs (2)
  iteritems :
    ∀ {KT VT : Type}, HashMap KT VT → List (KT × VT)
  inverted :
    ∀ {KT VT : Type}, HashMap KT VT → List (VT × KT)
  -- FrozenBidict APIs (1)
  frozenBidictHash :
    ∀ {KT VT : Type} [Hashable KT] [Hashable VT],
      BidictBase KT VT → Int
  -- MutableBidict APIs (10)
  initMutableBidict :
    ∀ {KT VT : Type}, BidictBase KT VT → OnDup → MutableBidict KT VT
  delItem :
    ∀ {KT VT : Type} [BEq KT],
      MutableBidict KT VT → KT → MutableBidict KT VT
  setItem :
    ∀ {KT VT : Type} [BEq KT] [BEq VT],
      MutableBidict KT VT → KT → VT →
        Except DuplicationError (MutableBidict KT VT)
  forceput :
    ∀ {KT VT : Type} [BEq KT] [BEq VT],
      MutableBidict KT VT → KT → VT → MutableBidict KT VT
  clear :
    ∀ {KT VT : Type}, MutableBidict KT VT → MutableBidict KT VT
  pop :
    ∀ {KT VT : Type} [BEq KT] {DT : Type},
      MutableBidict KT VT → KT → DT → MutableBidict KT VT × Sum VT DT
  popitem :
    ∀ {KT VT : Type},
      MutableBidict KT VT → Option (MutableBidict KT VT × (KT × VT))
  update :
    ∀ {KT VT : Type} [BEq KT] [BEq VT],
      MutableBidict KT VT → BidictBase KT VT →
        Except DuplicationError (MutableBidict KT VT)
  forceupdate :
    ∀ {KT VT : Type} [BEq KT] [BEq VT],
      MutableBidict KT VT → BidictBase KT VT → MutableBidict KT VT
  putall :
    ∀ {KT VT : Type} [BEq KT] [BEq VT],
      MutableBidict KT VT → BidictBase KT VT → OnDup → MutableBidict KT VT
  -- OrderedBidict APIs (10)
  initOrderedBidict :
    ∀ {KT VT : Type}, BidictBase KT VT → OrderedBidict KT VT
  iterOrderedBidict :
    ∀ {KT VT : Type}, OrderedBidict KT VT → Bool → List KT
  inverseOrderedBidict :
    ∀ {KT VT : Type}, OrderedBidict KT VT → OrderedBidict VT KT
  invOrderedBidict :
    ∀ {KT VT : Type}, OrderedBidict KT VT → OrderedBidict VT KT
  clearOrderedBidict :
    ∀ {KT VT : Type}, OrderedBidict KT VT → OrderedBidict KT VT
  popOrderedBidict :
    ∀ {KT VT : Type} [BEq KT],
      OrderedBidict KT VT → KT → Option (OrderedBidict KT VT × VT)
  popitemOrderedBidict :
    ∀ {KT VT : Type},
      OrderedBidict KT VT → Bool →
        Option (OrderedBidict KT VT × (KT × VT))
  moveToEndOrderedBidict :
    ∀ {KT VT : Type} [BEq KT],
      OrderedBidict KT VT → KT → Bool → OrderedBidict KT VT
  keysOrderedBidict :
    ∀ {KT VT : Type}, OrderedBidict KT VT → List KT
  itemsOrderedBidict :
    ∀ {KT VT : Type}, OrderedBidict KT VT → List (KT × VT)
