import JsonV2.Harness

/-!
# Json.Spec.Utils.Views.Writers

Frozen specifications for writer chains from `JSON.Utils.Views.Writers`.
-/

open JSON

/-- Chain copy writes the chain bytes into the destination prefix. -/
def spec_chain_copy_to_prefix (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (dest : List UInt8) (end_ : UInt32),
    chain__Valid? chain = true →
    end_.toNat = (chain__Bytes chain).length →
    end_.toNat ≤ dest.length →
    (impl.json.chain_CopyTo chain dest end_).take end_.toNat = chain__Bytes chain

/-- Chain copy preserves the destination suffix after the copied prefix. -/
def spec_chain_copy_to_suffix (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (dest : List UInt8) (end_ : UInt32),
    chain__Valid? chain = true →
    end_.toNat = (chain__Bytes chain).length →
    end_.toNat ≤ dest.length →
    (impl.json.chain_CopyTo chain dest end_).drop end_.toNat = dest.drop end_.toNat

/-- Appending a view appends its bytes to the writer chain bytes. -/
def spec_writer_append_bytes (impl : RepoImpl) : Prop :=
  ∀ (w : Writer_) (v : View_),
    writer__Valid? w = true →
    view__Valid? v = true →
    chain__Bytes (impl.json.writer__Append w v).chain =
    chain__Bytes w.chain ++ view__Bytes v

/-- Appending a view updates the writer length with saturated UInt32 addition. -/
def spec_writer_append_length (impl : RepoImpl) : Prop :=
  ∀ (w : Writer_) (v : View_),
    writer__Valid? w = true →
    view__Valid? v = true →
    (impl.json.writer__Append w v).length.toNat =
      if w.length.toNat + (v.end_ - v.beg).toNat < UInt32.size
      then w.length.toNat + (v.end_ - v.beg).toNat
      else UInt32.size - 1

/-- Writer copy writes the chain bytes into the destination prefix. -/
def spec_writer_copy_to_prefix (impl : RepoImpl) : Prop :=
  ∀ (w : Writer_) (dest : List UInt8),
    writer__Valid? w = true →
    writer__Unsaturated? w = true →
    w.length.toNat ≤ dest.length →
    (impl.json.writer__CopyTo w dest).take w.length.toNat = chain__Bytes w.chain

/-- Writer copy preserves the destination suffix after the copied prefix. -/
def spec_writer_copy_to_suffix (impl : RepoImpl) : Prop :=
  ∀ (w : Writer_) (dest : List UInt8),
    writer__Valid? w = true →
    writer__Unsaturated? w = true →
    w.length.toNat ≤ dest.length →
    (impl.json.writer__CopyTo w dest).drop w.length.toNat = dest.drop w.length.toNat

/-- Materializing an unsaturated valid writer returns exactly its chain bytes. -/
def spec_writer_to_array_correct (impl : RepoImpl) : Prop :=
  ∀ (w : Writer_),
    writer__Valid? w = true →
    writer__Unsaturated? w = true →
    (chain__Bytes w.chain).length < UInt32.size →
    impl.json.writer__ToArray w = chain__Bytes w.chain
