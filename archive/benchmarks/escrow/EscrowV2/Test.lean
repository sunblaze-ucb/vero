import EscrowV2.Impl.Escrow

/-!
# EscrowV2.Test

Executable guards for source-shaped Escrow branches.
-/

open Escrow

def testChain0 : Chain := { current_slot := 0 }
def testChain1 : Chain := { current_slot := 1 }

def sellerCtx (amount balance : Amount) : ContractCallContext :=
  { ctx_from := 1, ctx_amount := amount, ctx_contract_balance := balance }

def buyerCtx (amount balance : Amount) : ContractCallContext :=
  { ctx_from := 2, ctx_amount := amount, ctx_contract_balance := balance }

def baseState : State :=
  { last_action := 0
    next_step := NextStep.buyer_commit
    seller := 1
    buyer := 2
    seller_withdrawable := 0
    buyer_withdrawable := 0 }

def confirmState : State :=
  { last_action := 0
    next_step := NextStep.buyer_confirm
    seller := 1
    buyer := 2
    seller_withdrawable := 0
    buyer_withdrawable := 0 }

def withdrawalsState : State :=
  { last_action := 0
    next_step := NextStep.withdrawals
    seller := 1
    buyer := 2
    seller_withdrawable := 6
    buyer_withdrawable := 2 }

def strangerCtx : ContractCallContext :=
  { ctx_from := 99, ctx_amount := 0, ctx_contract_balance := 8 }

def sellerExitCtx : ContractCallContext :=
  { ctx_from := 1, ctx_amount := 0, ctx_contract_balance := 4 }

#guard (init testChain0 (sellerCtx 4 0) { setup_buyer := 1 }).isOk == false

#guard (init testChain0 (sellerCtx 0 0) { setup_buyer := 2 }).isOk == false

#guard (init testChain0 (sellerCtx 3 0) { setup_buyer := 2 }).isOk == false

#guard match init { current_slot := 5 } (sellerCtx 4 0) { setup_buyer := 2 } with
  | .ok st => st.next_step == NextStep.buyer_commit && st.last_action == 5
  | .error _ => false

#guard match receive testChain1 { ctx_from := 99, ctx_amount := 4, ctx_contract_balance := 8 }
    baseState (some Msg.commit_money) with
  | .ok _ => false
  | .error _ => true

#guard match receive testChain1 (buyerCtx 4 8) baseState (some Msg.commit_money) with
  | .ok (st, acts) => st.next_step == NextStep.buyer_confirm &&
      st.last_action == 1 && acts == []
  | .error _ => false

#guard match receive testChain1 (buyerCtx 0 8)
    confirmState (some Msg.confirm_item_received) with
  | .ok (st, acts) => st.next_step == NextStep.withdrawals &&
      st.buyer_withdrawable == 2 && st.seller_withdrawable == 6 && acts == []
  | .error _ => false

#guard match receive testChain1 (buyerCtx 0 8)
    withdrawalsState (some Msg.withdraw) with
  | .ok (st, acts) => st.buyer_withdrawable == 0 &&
      acts == [ActionBody.act_transfer 2 2]
  | .error _ => false

#guard match receive testChain1 strangerCtx withdrawalsState (some Msg.withdraw) with
  | .ok _ => false
  | .error _ => true

#guard match receive { current_slot := 51 } sellerExitCtx baseState (some Msg.withdraw) with
  | .ok _ => false
  | .error _ => true

#guard match receive { current_slot := 50 } sellerExitCtx baseState (some Msg.withdraw) with
  | .ok (st, acts) => st.next_step == NextStep.no_next_step &&
      acts == [ActionBody.act_transfer 1 4]
  | .error _ => false

#guard match receive testChain1 (buyerCtx 0 8) baseState none with
  | .ok _ => false
  | .error _ => true
