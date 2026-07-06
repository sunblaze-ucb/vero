import JsonV2.Impl.Utils.Views

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Json.Impl.Utils.Views.Writers

Writer chains for byte views translated from `JSON.Utils.Views.Writers`.

DO NOT MODIFY types or signatures - these are the fixed vocabulary.
Implement only the function bodies.
-/

namespace JSON

-- Types (no markers - fixed vocabulary)

inductive Chain where
  | empty : Chain
  | cons (previous : Chain) (v : View_) : Chain

structure Writer_ where
  length : UInt32
  chain : Chain

abbrev Writer := Writer_

-- Spec helpers (no markers - fixed vocabulary)

def chain__Bytes : Chain → List UInt8
  | .empty => []
  | .cons prev v => chain__Bytes prev ++ view__Bytes v

def chain__Valid? : Chain → Bool
  | .empty => true
  | .cons prev v => chain__Valid? prev && view__Valid? v

def writer__Bytes (w : Writer_) : List UInt8 := chain__Bytes w.chain

def writer__Count (w : Writer_) : Nat := (writer__Bytes w).length

def writer__Empty : Writer_ := { length := 0, chain := Chain.empty }

def writer__Bytes_2 (w : Writer_) : List UInt8 := chain__Bytes w.chain

def saturatedAddU32 (a b : UInt32) : UInt32 :=
  if a.toNat + b.toNat < UInt32.size then
    UInt32.ofNat (a.toNat + b.toNat)
  else
    UInt32.ofNat (UInt32.size - 1)

def writer__Then (w : Writer_) (fn : Writer_ → Writer_) : Writer_ := fn w

def writer__Valid? (w : Writer_) : Bool :=
  let len := (chain__Bytes w.chain).length
  chain__Valid? w.chain &&
  decide (w.length.toNat = if len < UInt32.size then len else UInt32.size - 1)

def writer__Unsaturated? (w : Writer_) : Bool :=
  decide (w.length.toNat ≠ UInt32.size - 1)

-- API signatures (no markers - fixed vocabulary)

abbrev ChainCopyToSig := Chain → List UInt8 → UInt32 → List UInt8

abbrev WriterAppendSig := Writer_ → View_ → Writer_

abbrev WriterCopyToSig := Writer_ → List UInt8 → List UInt8

abbrev WriterToArraySig := Writer_ → List UInt8

end JSON

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=chain_CopyTo
-- !benchmark @end code_aux def=chain_CopyTo

def JSON.chain_CopyTo : JSON.ChainCopyToSig :=
-- !benchmark @start code def=chain_CopyTo
  fun chain dest end_ =>
    let bytes := JSON.chain__Bytes chain
    dest.take (end_.toNat - bytes.length) ++ bytes ++ dest.drop end_.toNat
-- !benchmark @end code def=chain_CopyTo

-- !benchmark @start code_aux def=writer__Append
-- !benchmark @end code_aux def=writer__Append

def JSON.writer__Append : JSON.WriterAppendSig :=
-- !benchmark @start code def=writer__Append
  fun w v =>
    { length := JSON.saturatedAddU32 w.length (v.end_ - v.beg),
      chain := JSON.Chain.cons w.chain v }
-- !benchmark @end code def=writer__Append

-- !benchmark @start code_aux def=writer__CopyTo
-- !benchmark @end code_aux def=writer__CopyTo

def JSON.writer__CopyTo : JSON.WriterCopyToSig :=
-- !benchmark @start code def=writer__CopyTo
  fun w dest =>
    JSON.chain_CopyTo w.chain dest w.length
-- !benchmark @end code def=writer__CopyTo

-- !benchmark @start code_aux def=writer__ToArray
-- !benchmark @end code_aux def=writer__ToArray

def JSON.writer__ToArray : JSON.WriterToArraySig :=
-- !benchmark @start code def=writer__ToArray
  fun w =>
    JSON.chain__Bytes w.chain
-- !benchmark @end code def=writer__ToArray
