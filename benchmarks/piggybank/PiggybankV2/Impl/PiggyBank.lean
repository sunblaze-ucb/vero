import PiggybankV2.Impl.ConcertShim

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# PiggybankV2.Impl.PiggyBank

Executable Lean translation of the PiggyBank contract entrypoints from
`examples/piggybank/PiggyBank.v`.

DO NOT MODIFY types or signatures -- these are fixed vocabulary.
-/

inductive PiggyState where
  | Intact : PiggyState
  | Smashed : PiggyState
  deriving Repr, DecidableEq, BEq

inductive Msg where
  | Insert : Msg
  | Smash : Msg
  deriving Repr, DecidableEq, BEq

abbrev Setup := Unit

abbrev Error := Nat

structure State where
  balance : Amount
  owner : Address
  piggyState : PiggyState
  deriving Repr, DecidableEq, BEq

abbrev Result := Except Error (State × List ActionBody)

def error_no_msg : Error := 1

def error_not_owner : Error := 2

def error_already_smashed : Error := 3

def error_amount_not_positive : Error := 4

def error_amount_not_zero : Error := 5

def is_smashed (state : State) : Bool :=
  match state.piggyState with
  | PiggyState.Intact => false
  | PiggyState.Smashed => true

namespace PiggybankV2

abbrev InsertSig := State → ContractCallContext → Result

abbrev SmashSig := State → ContractCallContext → Result

abbrev InitSig := Chain → ContractCallContext → Setup → Except Error State

abbrev ReceiveSig := Chain → ContractCallContext → State → Option Msg → Result

end PiggybankV2

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=insert
-- !benchmark @end code_aux def=insert

def PiggybankV2.insert : PiggybankV2.InsertSig :=
-- !benchmark @start code def=insert
  fun state ctx =>
    if ctx.ctx_amount < 0 then
      Except.error error_amount_not_positive
    else if is_smashed state then
      Except.error error_already_smashed
    else
      Except.ok ({ state with balance := ctx.ctx_amount + state.balance }, [])
-- !benchmark @end code def=insert

-- !benchmark @start code_aux def=smash
-- !benchmark @end code_aux def=smash

def PiggybankV2.smash : PiggybankV2.SmashSig :=
-- !benchmark @start code def=smash
  fun state ctx =>
    if address_neqb ctx.ctx_from state.owner then
      Except.error error_not_owner
    else if is_smashed state then
      Except.error error_already_smashed
    else
      Except.ok (
        { state with balance := 0, piggyState := PiggyState.Smashed },
        [ActionBody.act_transfer state.owner (state.balance + ctx.ctx_amount)]
      )
-- !benchmark @end code def=smash

-- !benchmark @start code_aux def=init
-- !benchmark @end code_aux def=init

def PiggybankV2.init : PiggybankV2.InitSig :=
-- !benchmark @start code def=init
  fun _chain ctx _setup =>
    Except.ok {
      balance := ctx.ctx_amount,
      owner := ctx.ctx_from,
      piggyState := PiggyState.Intact
    }
-- !benchmark @end code def=init

-- !benchmark @start code_aux def=receive
-- !benchmark @end code_aux def=receive

def PiggybankV2.receive : PiggybankV2.ReceiveSig :=
-- !benchmark @start code def=receive
  fun _chain ctx state msg =>
    match msg with
    | some Msg.Insert => PiggybankV2.insert state ctx
    | some Msg.Smash => PiggybankV2.smash state ctx
    | none => Except.error error_no_msg
-- !benchmark @end code def=receive
