import EIP20V2.Harness

/-!
# Eip20.EIP20V2.Spec.EIP20TokenCorrect

Frozen specifications translated from the Coq `EIP20TokenCorrect` module.
Each `spec_*` property is stated over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY - this file is frozen curator-given content.
-/

/-- A successful receive call implies the call amount was nonpositive. -/
def spec_EIP20_not_payable (impl : RepoImpl) : Prop :=
  ∀ (prev_state new_state : State) (chain : Chain) (ctx : ContractCallContext) (msg : Option Msg) (new_acts : List ActionBody),
    stateWF prev_state →
    impl.eip20.receive chain ctx prev_state msg = Except.ok (new_state, new_acts) →
    stateWF new_state ∧ ctx.ctx_amount ≤ 0

/-- A successful receive call emits no outgoing actions. -/
def spec_EIP20_no_acts (impl : RepoImpl) : Prop :=
  ∀ (prev_state new_state : State) (chain : Chain) (ctx : ContractCallContext) (msg : Option Msg) (new_acts : List ActionBody),
    stateWF prev_state →
    impl.eip20.receive chain ctx prev_state msg = Except.ok (new_state, new_acts) →
    stateWF new_state ∧ new_acts = []

/-- Calling receive with no message returns the default error. -/
def spec_default_none (impl : RepoImpl) : Prop :=
  ∀ (prev_state : State) (chain : Chain) (ctx : ContractCallContext),
    stateWF prev_state →
    impl.eip20.receive chain ctx prev_state none = Except.error default_error

/-- A successful transfer message updates sender and recipient balances exactly. -/
def spec_try_transfer_balance_correct (impl : RepoImpl) : Prop :=
  ∀ (prev_state new_state : State) (chain : Chain) (ctx : ContractCallContext) (to : Address) (amount : TokenValue) (new_acts : List ActionBody),
    stateWF prev_state →
    impl.eip20.receive chain ctx prev_state (some (Msg.transfer to amount)) = Except.ok (new_state, new_acts) →
    stateWF new_state ∧ transfer_balance_update_correct prev_state new_state ctx.ctx_from to amount = true

/-- A successful transfer message preserves total supply. -/
def spec_try_transfer_preserves_total_supply (impl : RepoImpl) : Prop :=
  ∀ (prev_state new_state : State) (chain : Chain) (ctx : ContractCallContext) (to : Address) (amount : TokenValue) (new_acts : List ActionBody),
    stateWF prev_state →
    impl.eip20.receive chain ctx prev_state (some (Msg.transfer to amount)) = Except.ok (new_state, new_acts) →
    stateWF new_state ∧ prev_state.total_supply = new_state.total_supply

/-- A successful transfer message does not change allowances. -/
def spec_try_transfer_preserves_allowances (impl : RepoImpl) : Prop :=
  ∀ (prev_state new_state : State) (chain : Chain) (ctx : ContractCallContext) (to : Address) (amount : TokenValue) (new_acts : List ActionBody),
    stateWF prev_state →
    impl.eip20.receive chain ctx prev_state (some (Msg.transfer to amount)) = Except.ok (new_state, new_acts) →
    stateWF new_state ∧ allowanceMapEquiv prev_state.allowances new_state.allowances

/-- A successful transfer changes no balances except sender and recipient. -/
def spec_try_transfer_preserves_other_balances (impl : RepoImpl) : Prop :=
  ∀ (prev_state new_state : State) (chain : Chain) (ctx : ContractCallContext) (to account : Address) (amount : TokenValue) (new_acts : List ActionBody),
    stateWF prev_state →
    impl.eip20.receive chain ctx prev_state (some (Msg.transfer to amount)) = Except.ok (new_state, new_acts) →
    stateWF new_state ∧
      (account ≠ ctx.ctx_from →
       account ≠ to →
       lookup account prev_state.balances = lookup account new_state.balances)

/-- Receive succeeds on a transfer exactly when the call is not payable and the sender has enough balance. -/
def spec_try_transfer_is_some (impl : RepoImpl) : Prop :=
  ∀ (state : State) (chain : Chain) (ctx : ContractCallContext) (to : Address) (amount : TokenValue),
    stateWF state →
    ((ctx.ctx_amount ≤ 0 ∧ amount ≤ withDefault 0 (lookup ctx.ctx_from state.balances)) ↔
      isOk (impl.eip20.receive chain ctx state (some (Msg.transfer to amount))) = true)

/-- A successful transfer_from updates balances and the delegate allowance exactly. -/
def spec_try_transfer_from_balance_correct (impl : RepoImpl) : Prop :=
  ∀ (prev_state new_state : State) (chain : Chain) (ctx : ContractCallContext) (fromAddr to : Address) (amount : TokenValue) (new_acts : List ActionBody),
    stateWF prev_state →
    impl.eip20.receive chain ctx prev_state (some (Msg.transfer_from fromAddr to amount)) = Except.ok (new_state, new_acts) →
    stateWF new_state ∧
      transfer_balance_update_correct prev_state new_state fromAddr to amount = true ∧
      transfer_from_allowances_update_correct prev_state new_state fromAddr ctx.ctx_from amount = true

/-- A successful transfer_from message preserves total supply. -/
def spec_try_transfer_from_preserves_total_supply (impl : RepoImpl) : Prop :=
  ∀ (prev_state new_state : State) (chain : Chain) (ctx : ContractCallContext) (fromAddr to : Address) (amount : TokenValue) (new_acts : List ActionBody),
    stateWF prev_state →
    impl.eip20.receive chain ctx prev_state (some (Msg.transfer_from fromAddr to amount)) = Except.ok (new_state, new_acts) →
    stateWF new_state ∧ prev_state.total_supply = new_state.total_supply

/-- A successful transfer_from changes no balances except owner and recipient. -/
def spec_try_transfer_from_preserves_other_balances (impl : RepoImpl) : Prop :=
  ∀ (prev_state new_state : State) (chain : Chain) (ctx : ContractCallContext) (fromAddr to account : Address) (amount : TokenValue) (new_acts : List ActionBody),
    stateWF prev_state →
    impl.eip20.receive chain ctx prev_state (some (Msg.transfer_from fromAddr to amount)) = Except.ok (new_state, new_acts) →
    stateWF new_state ∧
      (account ≠ fromAddr →
       account ≠ to →
       lookup account prev_state.balances = lookup account new_state.balances)

/-- A successful transfer_from changes no allowance map except the owner's map. -/
def spec_try_transfer_from_preserves_other_allowances (impl : RepoImpl) : Prop :=
  ∀ (prev_state new_state : State) (chain : Chain) (ctx : ContractCallContext) (fromAddr to account : Address) (amount : TokenValue) (new_acts : List ActionBody),
    stateWF prev_state →
    impl.eip20.receive chain ctx prev_state (some (Msg.transfer_from fromAddr to amount)) = Except.ok (new_state, new_acts) →
    stateWF new_state ∧
      (account ≠ fromAddr →
       allowanceOwnerEquiv prev_state.allowances new_state.allowances account)

/-- A successful transfer_from preserves allowances of delegates other than the caller. -/
def spec_try_transfer_from_preserves_other_allowance (impl : RepoImpl) : Prop :=
  ∀ (prev_state new_state : State) (chain : Chain) (ctx : ContractCallContext) (fromAddr to account : Address) (amount : TokenValue) (new_acts : List ActionBody),
    stateWF prev_state →
    impl.eip20.receive chain ctx prev_state (some (Msg.transfer_from fromAddr to amount)) = Except.ok (new_state, new_acts) →
    stateWF new_state ∧
      (account ≠ ctx.ctx_from →
       get_allowance prev_state fromAddr account = get_allowance new_state fromAddr account)

/-- Receive succeeds on transfer_from exactly when allowance entries exist and allowance and balance are sufficient. -/
def spec_try_transfer_from_is_some (impl : RepoImpl) : Prop :=
  ∀ (state : State) (chain : Chain) (ctx : ContractCallContext) (fromAddr to : Address) (amount : TokenValue),
    stateWF state →
    ((ctx.ctx_amount ≤ 0 ∧
      isSome (lookup fromAddr state.allowances) = true ∧
      isSome (lookup ctx.ctx_from (withDefault [] (lookup fromAddr state.allowances))) = true ∧
      amount ≤ withDefault 0 (lookup fromAddr state.balances) ∧
      amount ≤ withDefault 0 (lookup ctx.ctx_from (withDefault [] (lookup fromAddr state.allowances))) ↔
      isOk (impl.eip20.receive chain ctx state (some (Msg.transfer_from fromAddr to amount))) = true)
    )

/-- A successful approve message sets the caller's allowance for the delegate. -/
def spec_try_approve_allowance_correct (impl : RepoImpl) : Prop :=
  ∀ (prev_state new_state : State) (chain : Chain) (ctx : ContractCallContext) (delegate : Address) (amount : TokenValue) (new_acts : List ActionBody),
    stateWF prev_state →
    impl.eip20.receive chain ctx prev_state (some (Msg.approve delegate amount)) = Except.ok (new_state, new_acts) →
    stateWF new_state ∧ approve_allowance_update_correct new_state ctx.ctx_from delegate amount = true

/-- A successful approve message preserves total supply. -/
def spec_try_approve_preserves_total_supply (impl : RepoImpl) : Prop :=
  ∀ (prev_state new_state : State) (chain : Chain) (ctx : ContractCallContext) (delegate : Address) (amount : TokenValue) (new_acts : List ActionBody),
    stateWF prev_state →
    impl.eip20.receive chain ctx prev_state (some (Msg.approve delegate amount)) = Except.ok (new_state, new_acts) →
    stateWF new_state ∧ prev_state.total_supply = new_state.total_supply

/-- A successful approve message does not change balances. -/
def spec_try_approve_preserves_balances (impl : RepoImpl) : Prop :=
  ∀ (prev_state new_state : State) (chain : Chain) (ctx : ContractCallContext) (delegate : Address) (amount : TokenValue) (new_acts : List ActionBody),
    stateWF prev_state →
    impl.eip20.receive chain ctx prev_state (some (Msg.approve delegate amount)) = Except.ok (new_state, new_acts) →
    stateWF new_state ∧ tokenMapEquiv prev_state.balances new_state.balances

/-- A successful approve changes no allowance map except the caller's map. -/
def spec_try_approve_preserves_other_allowances (impl : RepoImpl) : Prop :=
  ∀ (prev_state new_state : State) (chain : Chain) (ctx : ContractCallContext) (delegate account : Address) (amount : TokenValue) (new_acts : List ActionBody),
    stateWF prev_state →
    impl.eip20.receive chain ctx prev_state (some (Msg.approve delegate amount)) = Except.ok (new_state, new_acts) →
    stateWF new_state ∧
      (account ≠ ctx.ctx_from →
       allowanceOwnerEquiv prev_state.allowances new_state.allowances account)

/-- A successful approve preserves allowances for delegates other than the approved delegate. -/
def spec_try_approve_preserves_other_allowance (impl : RepoImpl) : Prop :=
  ∀ (prev_state new_state : State) (chain : Chain) (ctx : ContractCallContext) (delegate account : Address) (amount : TokenValue) (new_acts : List ActionBody),
    stateWF prev_state →
    impl.eip20.receive chain ctx prev_state (some (Msg.approve delegate amount)) = Except.ok (new_state, new_acts) →
    stateWF new_state ∧
      (account ≠ delegate →
       get_allowance prev_state ctx.ctx_from account = get_allowance new_state ctx.ctx_from account)

/-- Receive succeeds on approve exactly when the call is not payable. -/
def spec_try_approve_is_some (impl : RepoImpl) : Prop :=
  ∀ (state : State) (chain : Chain) (ctx : ContractCallContext) (delegate : Address) (amount : TokenValue),
    stateWF state →
    (ctx.ctx_amount ≤ 0 ↔ isOk (impl.eip20.receive chain ctx state (some (Msg.approve delegate amount))) = true)

/-- A successful transfer message preserves the sum of balances. -/
def spec_try_transfer_preserves_balances_sum (impl : RepoImpl) : Prop :=
  ∀ (prev_state new_state : State) (chain : Chain) (ctx : ContractCallContext) (to : Address) (amount : TokenValue) (new_acts : List ActionBody),
    stateWF prev_state →
    impl.eip20.receive chain ctx prev_state (some (Msg.transfer to amount)) = Except.ok (new_state, new_acts) →
    stateWF new_state ∧ sum_balances prev_state = sum_balances new_state

/-- A successful transfer_from message preserves the sum of balances. -/
def spec_try_transfer_from_preserves_balances_sum (impl : RepoImpl) : Prop :=
  ∀ (prev_state new_state : State) (chain : Chain) (ctx : ContractCallContext) (fromAddr to : Address) (amount : TokenValue) (new_acts : List ActionBody),
    stateWF prev_state →
    impl.eip20.receive chain ctx prev_state (some (Msg.transfer_from fromAddr to amount)) = Except.ok (new_state, new_acts) →
    stateWF new_state ∧ sum_balances prev_state = sum_balances new_state

/-- A successful approve message preserves the sum of balances. -/
def spec_try_approve_preserves_balances_sum (impl : RepoImpl) : Prop :=
  ∀ (prev_state new_state : State) (chain : Chain) (ctx : ContractCallContext) (delegate : Address) (amount : TokenValue) (new_acts : List ActionBody),
    stateWF prev_state →
    impl.eip20.receive chain ctx prev_state (some (Msg.approve delegate amount)) = Except.ok (new_state, new_acts) →
    stateWF new_state ∧ sum_balances prev_state = sum_balances new_state

/-- For a reachable state with this contract deployed, no outgoing actions are recorded for the contract address. -/
def spec_outgoing_acts_nil (impl : RepoImpl) : Prop :=
  ∀ (bstate : ChainState) (caddr : Address),
    reachable impl.eip20.init impl.eip20.receive bstate →
    env_contracts bstate caddr = some (contract impl.eip20.init impl.eip20.receive) →
    outgoing_acts bstate caddr = []

/-- For a deployed EIP20 contract, the stored total supply equals the initial deployment amount. -/
def spec_total_supply_eq_init_supply (impl : RepoImpl) : Prop :=
  ∀ (bstate : ChainState) (caddr : Address) (trace : ChainTrace impl.eip20.init impl.eip20.receive empty_state bstate),
    env_contracts bstate caddr = some (contract impl.eip20.init impl.eip20.receive) →
    ∃ deploy_info cstate,
      deployment_info trace caddr = some deploy_info ∧
      contract_state bstate caddr = some cstate ∧
      deploy_info.deployment_setup.init_amount = cstate.total_supply

/-- For a reachable deployed EIP20 contract, total supply equals the sum of all balances. -/
def spec_sum_balances_eq_total_supply (impl : RepoImpl) : Prop :=
  ∀ (bstate : ChainState) (caddr : Address),
    reachable impl.eip20.init impl.eip20.receive bstate →
    env_contracts bstate caddr = some (contract impl.eip20.init impl.eip20.receive) →
    ∃ cstate,
      contract_state bstate caddr = some cstate ∧
      cstate.total_supply = sum_balances cstate
