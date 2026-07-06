import PiggybankV2.Spec.PiggyBank

/-!
# PiggybankV2.Spec.PiggyBankCorrect

Specifications translated from `examples/piggybank/PiggyBankCorrect.v`.
Each `spec_*` is a property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY -- this file is frozen curator-given content.
-/

/-- If insert succeeds, it emits no actions and adds the transferred amount to the previous balance. -/
def spec_insert_inserts_correct (impl : RepoImpl) : Prop :=
  ∀ (prev_state next_state : State) (ctx : ContractCallContext) (acts : List ActionBody),
    impl.piggybankV2.insert prev_state ctx = Except.ok (next_state, acts) →
      acts = [] ∧ ContractCallContext.ctx_amount ctx + prev_state.balance = next_state.balance

/-- Insert rejects a negative transferred amount. -/
def spec_insert_negative_amount_fails (impl : RepoImpl) : Prop :=
  ∀ (prev_state : State) (ctx : ContractCallContext),
    ctx.ctx_amount < 0 →
      ∃ e : Error, impl.piggybankV2.insert prev_state ctx = Except.error e

/-- Insert rejects an already-smashed piggy bank. -/
def spec_insert_smashed_fails (impl : RepoImpl) : Prop :=
  ∀ (prev_state : State) (ctx : ContractCallContext),
    prev_state.piggyState = PiggyState.Smashed →
      ∃ e : Error, impl.piggybankV2.insert prev_state ctx = Except.error e

/-- Insert succeeds exactly on intact states with nonnegative transferred amount. -/
def spec_insert_intact_nonnegative_succeeds (impl : RepoImpl) : Prop :=
  ∀ (prev_state : State) (ctx : ContractCallContext),
    prev_state.piggyState = PiggyState.Intact →
    0 ≤ ctx.ctx_amount →
      impl.piggybankV2.insert prev_state ctx =
        Except.ok ({ prev_state with balance := ctx.ctx_amount + prev_state.balance }, [])

/-- If smash succeeds, the next state is smashed with zero balance and the sole outgoing transfer sends the prior balance plus call amount to the owner. -/
def spec_smash_transfers_correctly (impl : RepoImpl) : Prop :=
  ∀ (prev_state next_state : State) (ctx : ContractCallContext) (acts : List ActionBody),
    impl.piggybankV2.smash prev_state ctx = Except.ok (next_state, acts) →
      next_state.piggyState = PiggyState.Smashed ∧
        next_state.balance = 0 ∧
          acts = [ActionBody.act_transfer prev_state.owner (prev_state.balance + ContractCallContext.ctx_amount ctx)]

/-- Smash rejects calls not sent by the owner. -/
def spec_smash_non_owner_fails (impl : RepoImpl) : Prop :=
  ∀ (prev_state : State) (ctx : ContractCallContext),
    ctx.ctx_from ≠ prev_state.owner →
      ∃ e : Error, impl.piggybankV2.smash prev_state ctx = Except.error e

/-- Smash rejects an already-smashed piggy bank. -/
def spec_smash_smashed_fails (impl : RepoImpl) : Prop :=
  ∀ (prev_state : State) (ctx : ContractCallContext),
    prev_state.piggyState = PiggyState.Smashed →
      ∃ e : Error, impl.piggybankV2.smash prev_state ctx = Except.error e

/-- Smash succeeds for the owner while the piggy bank is intact. -/
def spec_smash_owner_intact_succeeds (impl : RepoImpl) : Prop :=
  ∀ (prev_state : State) (ctx : ContractCallContext),
    ctx.ctx_from = prev_state.owner →
    prev_state.piggyState = PiggyState.Intact →
      impl.piggybankV2.smash prev_state ctx =
        Except.ok (
          { prev_state with balance := 0, piggyState := PiggyState.Smashed },
          [ActionBody.act_transfer prev_state.owner (prev_state.balance + ctx.ctx_amount)]
        )

/-- If receive succeeds, the result satisfies the Insert or Smash postcondition according to the supplied message, and a missing message cannot succeed. -/
def spec_receive_is_correct (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (prev_state next_state : State) (msg : Option Msg) (acts : List ActionBody),
    impl.piggybankV2.receive chain ctx prev_state msg = Except.ok (next_state, acts) →
      match msg with
      | some Msg.Insert =>
          acts = [] ∧ ContractCallContext.ctx_amount ctx + prev_state.balance = next_state.balance
      | some Msg.Smash =>
          next_state.piggyState = PiggyState.Smashed ∧
            next_state.balance = 0 ∧
              acts = [ActionBody.act_transfer prev_state.owner (prev_state.balance + ContractCallContext.ctx_amount ctx)]
      | none => False

/-- Receive dispatches Insert messages to the insert entrypoint. -/
def spec_receive_dispatch_insert (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (prev_state : State),
    impl.piggybankV2.receive chain ctx prev_state (some Msg.Insert) =
      impl.piggybankV2.insert prev_state ctx

/-- Receive dispatches Smash messages to the smash entrypoint. -/
def spec_receive_dispatch_smash (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (prev_state : State),
    impl.piggybankV2.receive chain ctx prev_state (some Msg.Smash) =
      impl.piggybankV2.smash prev_state ctx

/-- Receive rejects missing messages. -/
def spec_receive_missing_msg_fails (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (prev_state : State),
    ∃ e : Error, impl.piggybankV2.receive chain ctx prev_state none = Except.error e

/-- A reachable deployed PiggyBank contract never has an outgoing action that calls or transfers to its own address. -/
def spec_no_self_calls (impl : RepoImpl) : Prop :=
  ∀ (bstate : ChainState) (caddr : Address),
    reachable bstate →
      env_contracts bstate caddr = some (toWeakContract (contract impl)) →
        ∀ actBody ∈ outgoing_acts bstate caddr,
          match actBody with
          | ActionBody.act_transfer to _ => address_eqb to caddr = false
          | _ => False

/-- The owner field is unchanged by every successful receive call. -/
def spec_owner_remains (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (prev_state next_state : State) (msg : Option Msg) (acts : List ActionBody),
    impl.piggybankV2.receive chain ctx prev_state msg = Except.ok (next_state, acts) →
      prev_state.owner = next_state.owner

/-- Along any trace from the empty state, a deployed PiggyBank state's owner equals the original deployment sender. -/
def spec_owner_correct (impl : RepoImpl) : Prop :=
  ∀ (bstate : ChainState) (caddr : Address) (trace : ChainTrace empty_state bstate),
    env_contracts bstate caddr = some (toWeakContract (contract impl)) →
      ∃ (cstate : State) (dep : DeploymentInfo),
        deployment_info (Setup := Setup) trace caddr = some dep ∧
          contract_state bstate caddr = some cstate ∧
            cstate.owner = deployment_from dep

/-- Once the stored state is Smashed, every receive call fails with some error. -/
def spec_stay_smashed (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (prev_state : State) (msg : Option Msg),
    prev_state.piggyState = PiggyState.Smashed →
      ∃ e : Error, impl.piggybankV2.receive chain ctx prev_state msg = Except.error e

/-- For an Intact piggy bank, any successful Insert receive call cannot decrease the stored balance. -/
def spec_if_intact_then_balance_can_only_increase (impl : RepoImpl) : Prop :=
  ∀ (prev_state next_state : State) (ctx : ContractCallContext) (chain : Chain) (new_acts : List ActionBody),
    prev_state.piggyState = PiggyState.Intact →
      impl.piggybankV2.receive chain ctx prev_state (some Msg.Insert) = Except.ok (next_state, new_acts) →
        prev_state.balance ≤ next_state.balance

/-- Every successful init call creates a state whose piggyState is Intact. -/
def spec_initializes_correctly (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (setup : Setup) (new_state : State),
    impl.piggybankV2.init chain ctx setup = Except.ok new_state →
      new_state.piggyState = PiggyState.Intact

/-- Init exactly records the deployment sender as owner and the attached amount as balance. -/
def spec_initializes_owner_and_balance (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (setup : Setup),
    impl.piggybankV2.init chain ctx setup =
      Except.ok {
        balance := ctx.ctx_amount,
        owner := ctx.ctx_from,
        piggyState := PiggyState.Intact
      }

/-- For a reachable deployed PiggyBank with no outgoing actions, the on-chain account balance equals the stored contract balance. -/
def spec_balance_on_chain (impl : RepoImpl) : Prop :=
  ∀ (bstate : ChainState) (caddr : Address),
    reachable bstate →
      env_contracts bstate caddr = some (toWeakContract (contract impl)) →
        outgoing_acts bstate caddr = [] →
          ∃ cstate : State,
            contract_state bstate caddr = some cstate ∧
              env_account_balances bstate caddr = cstate.balance

/-- For a reachable deployed PiggyBank, if its stored state is Intact then it has no outgoing actions queued. -/
def spec_no_outgoing_actions_when_intact (impl : RepoImpl) : Prop :=
  ∀ (bstate : ChainState) (caddr : Address),
    reachable bstate →
      env_contracts bstate caddr = some (toWeakContract (contract impl)) →
        ∃ cstate : State,
          contract_state bstate caddr = some cstate ∧
            (cstate.piggyState = PiggyState.Intact → outgoing_acts bstate caddr = [])

/-- For a reachable deployed PiggyBank with no outgoing actions, if its stored state is Smashed then its on-chain balance is zero. -/
def spec_balance_is_zero_when_smashed (impl : RepoImpl) : Prop :=
  ∀ (bstate : ChainState) (caddr : Address),
    reachable bstate →
      env_contracts bstate caddr = some (toWeakContract (contract impl)) →
        outgoing_acts bstate caddr = [] →
          ∃ cstate : State,
            contract_state bstate caddr = some cstate ∧
              (cstate.piggyState = PiggyState.Smashed → env_account_balances bstate caddr = 0)

/-- For a reachable deployed PiggyBank with no outgoing actions, the stored contract balance is nonnegative. -/
def spec_balance_on_pos (impl : RepoImpl) : Prop :=
  ∀ (bstate : ChainState) (caddr : Address),
    reachable bstate →
      env_contracts bstate caddr = some (toWeakContract (contract impl)) →
        outgoing_acts bstate caddr = [] →
          ∃ cstate : State,
            contract_state bstate caddr = some cstate ∧
              (0 : Amount) ≤ cstate.balance
