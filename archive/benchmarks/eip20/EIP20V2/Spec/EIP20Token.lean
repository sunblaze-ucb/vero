import EIP20V2.Harness

/-!
# Eip20.EIP20V2.Spec.EIP20Token

Direct API specifications for the scored `EIP20Token` surface. The Coq
correctness theorems mostly constrain token behavior through `receive`; these
specs additionally bind the four helper APIs that are exposed as scored Bundle
fields.
-/

/-- Initialization installs the owner's full initial balance and no allowances. -/
def spec_init_direct (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (setup : Setup),
    impl.eip20.init chain ctx setup =
      Except.ok
        { total_supply := setup.init_amount,
          balances := setEntry setup.owner setup.init_amount [],
          allowances := [] }

/-- Direct transfer succeeds exactly when the sender has enough balance, and successful transfers update balances only. -/
def spec_try_transfer_direct (impl : RepoImpl) : Prop :=
  ∀ (state : State) (fromAddr to : Address) (amount : TokenValue),
    stateWF state →
    ((amount ≤ withDefault 0 (lookup fromAddr state.balances)) ↔
      isOk (impl.eip20.try_transfer fromAddr to amount state) = true) ∧
    (∀ newState,
      impl.eip20.try_transfer fromAddr to amount state = Except.ok newState →
        stateWF newState ∧
        transfer_balance_update_correct state newState fromAddr to amount = true ∧
        newState.total_supply = state.total_supply ∧
        allowanceMapEquiv state.allowances newState.allowances ∧
        (∀ account,
          account ≠ fromAddr →
          account ≠ to →
          lookup account state.balances = lookup account newState.balances)) ∧
    (impl.eip20.try_transfer fromAddr to amount state = Except.error default_error →
      withDefault 0 (lookup fromAddr state.balances) < amount) ∧
    (match impl.eip20.try_transfer fromAddr to amount state with
     | Except.error err => err = default_error
     | Except.ok _ => True)

/-- Direct delegated transfer requires owner/delegate allowance entries plus enough allowance and balance. -/
def spec_try_transfer_from_direct (impl : RepoImpl) : Prop :=
  ∀ (state : State) (delegate fromAddr to : Address) (amount : TokenValue),
    stateWF state →
    ((isSome (lookup fromAddr state.allowances) = true ∧
      isSome (lookup delegate (withDefault [] (lookup fromAddr state.allowances))) = true ∧
      amount ≤ withDefault 0 (lookup fromAddr state.balances) ∧
      amount ≤ withDefault 0 (lookup delegate (withDefault [] (lookup fromAddr state.allowances))) ↔
      isOk (impl.eip20.try_transfer_from delegate fromAddr to amount state) = true) ∧
    (∀ newState,
      impl.eip20.try_transfer_from delegate fromAddr to amount state = Except.ok newState →
        stateWF newState ∧
        transfer_balance_update_correct state newState fromAddr to amount = true ∧
        transfer_from_allowances_update_correct state newState fromAddr delegate amount = true ∧
        newState.total_supply = state.total_supply ∧
        (∀ account,
          account ≠ fromAddr →
          account ≠ to →
          lookup account state.balances = lookup account newState.balances) ∧
        (∀ owner,
          owner ≠ fromAddr →
          allowanceOwnerEquiv state.allowances newState.allowances owner) ∧
        (∀ account,
          account ≠ delegate →
          get_allowance state fromAddr account = get_allowance newState fromAddr account)) ∧
    (impl.eip20.try_transfer_from delegate fromAddr to amount state = Except.error default_error →
      isSome (lookup fromAddr state.allowances) = false ∨
      isSome (lookup delegate (withDefault [] (lookup fromAddr state.allowances))) = false ∨
      withDefault 0 (lookup fromAddr state.balances) < amount ∨
      withDefault 0 (lookup delegate (withDefault [] (lookup fromAddr state.allowances))) < amount) ∧
    (match impl.eip20.try_transfer_from delegate fromAddr to amount state with
     | Except.error err => err = default_error
     | Except.ok _ => True)
    )

/-- Direct approve always succeeds, preserves balances and supply, and sets the caller/delegate allowance. -/
def spec_try_approve_direct (impl : RepoImpl) : Prop :=
  ∀ (state : State) (caller delegate : Address) (amount : TokenValue),
    stateWF state →
    ∃ newState,
      impl.eip20.try_approve caller delegate amount state = Except.ok newState ∧
      stateWF newState ∧
      approve_allowance_update_correct newState caller delegate amount = true ∧
      tokenMapEquiv state.balances newState.balances ∧
      newState.total_supply = state.total_supply ∧
      (∀ owner,
        owner ≠ caller →
        allowanceOwnerEquiv state.allowances newState.allowances owner) ∧
      (∀ account,
        account ≠ delegate →
        get_allowance state caller account = get_allowance newState caller account)
