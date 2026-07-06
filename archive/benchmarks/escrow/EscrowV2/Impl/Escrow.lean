-- !benchmark @start imports
-- !benchmark @end imports

/-!
# EscrowV2.Impl.Escrow

Core executable model for the ConCert Escrow contract from `examples/escrow/Escrow.v`.
The scoped v2 surface covers the concrete `init` and `receive` entry points; high-level
ConCert trace theorems remain deferred in the curation plan.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

abbrev Address := Nat

abbrev Amount := Int

structure Chain where
  current_slot : Nat
  deriving DecidableEq, Repr, BEq

structure ContractCallContext where
  ctx_from : Address
  ctx_amount : Amount
  ctx_contract_balance : Amount
  deriving DecidableEq, Repr, BEq

inductive ActionBody where
  | act_transfer : Address → Amount → ActionBody
  deriving DecidableEq, Repr, BEq

structure Setup where
  setup_buyer : Address
  deriving DecidableEq, Repr, BEq

inductive NextStep where
  | buyer_commit
  | buyer_confirm
  | withdrawals
  | no_next_step
  deriving DecidableEq, Repr, BEq

abbrev Error := Nat

def default_error : Error := 1

inductive Msg where
  | commit_money
  | confirm_item_received
  | withdraw
  deriving DecidableEq, Repr, BEq

structure State where
  last_action : Nat
  next_step : NextStep
  seller : Address
  buyer : Address
  seller_withdrawable : Amount
  buyer_withdrawable : Amount
  deriving DecidableEq, Repr, BEq

def subAmountOption (n m : Amount) : Option Amount :=
  if n < m then none else some (n - m)

namespace Escrow

abbrev InitSig :=
  Chain → ContractCallContext → Setup → Except Error State

abbrev ReceiveSig :=
  Chain → ContractCallContext → State → Option Msg →
  Except Error (State × List ActionBody)

end Escrow

-- !benchmark @start code_aux def=init
-- !benchmark @end code_aux def=init

def Escrow.init : Escrow.InitSig :=
-- !benchmark @start code def=init
  fun chain ctx setup =>
    let seller := ctx.ctx_from
    let buyer := setup.setup_buyer
    if buyer == seller then Except.error default_error
    else if ctx.ctx_amount == 0 then Except.error default_error
    else if ctx.ctx_amount % 2 != 0 then Except.error default_error
    else Except.ok {
      last_action := chain.current_slot
      next_step := NextStep.buyer_commit
      seller := seller
      buyer := buyer
      seller_withdrawable := 0
      buyer_withdrawable := 0
    }
-- !benchmark @end code def=init

-- !benchmark @start code_aux def=receive
-- !benchmark @end code_aux def=receive

def Escrow.receive : Escrow.ReceiveSig :=
-- !benchmark @start code def=receive
  fun chain ctx state msg =>
    match msg, state.next_step with
    | some Msg.commit_money, NextStep.buyer_commit =>
      match subAmountOption ctx.ctx_contract_balance ctx.ctx_amount with
      | none => Except.error default_error
      | some diff =>
        let item_price := diff / 2
        let expected := item_price * 2
        if ctx.ctx_from != state.buyer then Except.error default_error
        else if ctx.ctx_amount != expected then Except.error default_error
        else Except.ok ({ state with
          next_step := NextStep.buyer_confirm
          last_action := chain.current_slot }, [])
    | some Msg.confirm_item_received, NextStep.buyer_confirm =>
      let item_price := ctx.ctx_contract_balance / 4
      if ctx.ctx_from != state.buyer then Except.error default_error
      else if ctx.ctx_amount != 0 then Except.error default_error
      else Except.ok ({ state with
        next_step := NextStep.withdrawals
        buyer_withdrawable := item_price
        seller_withdrawable := item_price * 3 }, [])
    | some Msg.withdraw, NextStep.withdrawals =>
      if ctx.ctx_amount != 0 then Except.error default_error
      else
        let sender := ctx.ctx_from
        if sender == state.buyer then
          let to_pay := state.buyer_withdrawable
          if to_pay ≤ 0 then Except.error default_error
          else
            let ns := { state with buyer_withdrawable := 0 }
            let ns :=
              if ns.buyer_withdrawable == 0 && ns.seller_withdrawable == 0
              then { ns with next_step := NextStep.no_next_step }
              else ns
            Except.ok (ns, [ActionBody.act_transfer sender to_pay])
        else if sender == state.seller then
          let to_pay := state.seller_withdrawable
          if to_pay ≤ 0 then Except.error default_error
          else
            let ns := { state with seller_withdrawable := 0 }
            let ns :=
              if ns.buyer_withdrawable == 0 && ns.seller_withdrawable == 0
              then { ns with next_step := NextStep.no_next_step }
              else ns
            Except.ok (ns, [ActionBody.act_transfer sender to_pay])
        else Except.error default_error
    | some Msg.withdraw, NextStep.buyer_commit =>
      if ctx.ctx_amount != 0 then Except.error default_error
      else if state.last_action + 50 < chain.current_slot then Except.error default_error
      else if ctx.ctx_from != state.seller then Except.error default_error
      else
        Except.ok ({ state with next_step := NextStep.no_next_step },
          [ActionBody.act_transfer state.seller ctx.ctx_contract_balance])
    | _, _ => Except.error default_error
-- !benchmark @end code def=receive
