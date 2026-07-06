import EscrowV2.Harness

/-!
# EscrowV2.Spec.Escrow

Scoped branch-behavior specifications for the concrete `init` and `receive` APIs.
High-level ConCert trace correctness theorems are recorded as deferred source specs
in the curation plan and are not scored in this candidate.
-/

/-- `init` returns an error when buyer and seller are the same address. -/
def spec_init_buyer_eq_seller_fails (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (setup : Setup),
    ctx.ctx_from = setup.setup_buyer →
    ∃ e : Error, impl.escrowV2.init chain ctx setup = Except.error e

/-- `init` returns an error when the sent amount is zero. -/
def spec_init_zero_amount_fails (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (setup : Setup),
    ctx.ctx_from ≠ setup.setup_buyer →
    ctx.ctx_amount = 0 →
    ∃ e : Error, impl.escrowV2.init chain ctx setup = Except.error e

/-- `init` returns an error when the sent amount is odd. -/
def spec_init_odd_amount_fails (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (setup : Setup),
    ctx.ctx_from ≠ setup.setup_buyer →
    ctx.ctx_amount ≠ 0 →
    ctx.ctx_amount % 2 ≠ 0 →
    ∃ e : Error, impl.escrowV2.init chain ctx setup = Except.error e

/-- On successful `init`, the protocol starts in `buyer_commit`. -/
def spec_init_next_step (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (setup : Setup) (st : State),
    impl.escrowV2.init chain ctx setup = Except.ok st →
    st.next_step = NextStep.buyer_commit

/-- On successful `init`, parties, slot, and withdrawable amounts match the source initialization record. -/
def spec_init_state_fields (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (setup : Setup) (st : State),
    impl.escrowV2.init chain ctx setup = Except.ok st →
    st.last_action = chain.current_slot ∧
    st.seller = ctx.ctx_from ∧
    st.buyer = setup.setup_buyer ∧
    st.seller_withdrawable = 0 ∧
    st.buyer_withdrawable = 0

/-- `commit_money` rejects calls not sent by the buyer. -/
def spec_receive_commit_wrong_sender_fails (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (st : State),
    st.next_step = NextStep.buyer_commit →
    ctx.ctx_from ≠ st.buyer →
    ∃ e : Error, impl.escrowV2.receive chain ctx st (some Msg.commit_money) = Except.error e

/-- `commit_money` rejects calls whose amount exceeds the contract balance. -/
def spec_receive_commit_underfunded_balance_fails (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (st : State),
    st.next_step = NextStep.buyer_commit →
    ctx.ctx_contract_balance < ctx.ctx_amount →
    ∃ e : Error, impl.escrowV2.receive chain ctx st (some Msg.commit_money) = Except.error e

/-- Successful `commit_money` moves to `buyer_confirm`, updates `last_action`, and emits no actions. -/
def spec_receive_commit_success (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (st st' : State) (acts : List ActionBody),
    st.next_step = NextStep.buyer_commit →
    impl.escrowV2.receive chain ctx st (some Msg.commit_money) = Except.ok (st', acts) →
    st'.next_step = NextStep.buyer_confirm ∧
    st'.last_action = chain.current_slot ∧
    acts = []

/-- `commit_money` rejects buyer calls whose attached amount is not the exact expected amount. -/
def spec_receive_commit_wrong_amount_fails (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (st : State),
    st.next_step = NextStep.buyer_commit →
    ctx.ctx_from = st.buyer →
    ¬ ctx.ctx_contract_balance < ctx.ctx_amount →
    ctx.ctx_amount ≠ ((ctx.ctx_contract_balance - ctx.ctx_amount) / 2) * 2 →
    ∃ e : Error, impl.escrowV2.receive chain ctx st (some Msg.commit_money) = Except.error e

/-- `confirm_item_received` rejects non-buyer senders. -/
def spec_receive_confirm_wrong_sender_fails (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (st : State),
    st.next_step = NextStep.buyer_confirm →
    ctx.ctx_from ≠ st.buyer →
    ∃ e : Error, impl.escrowV2.receive chain ctx st (some Msg.confirm_item_received) = Except.error e

/-- `confirm_item_received` rejects nonzero attached amount. -/
def spec_receive_confirm_nonzero_amount_fails (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (st : State),
    st.next_step = NextStep.buyer_confirm →
    ctx.ctx_amount ≠ 0 →
    ∃ e : Error, impl.escrowV2.receive chain ctx st (some Msg.confirm_item_received) = Except.error e

/-- Successful `confirm_item_received` enters withdrawals and assigns buyer/seller shares. -/
def spec_receive_confirm_success (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (st st' : State) (acts : List ActionBody),
    st.next_step = NextStep.buyer_confirm →
    impl.escrowV2.receive chain ctx st (some Msg.confirm_item_received) = Except.ok (st', acts) →
    st'.next_step = NextStep.withdrawals ∧
    st'.buyer_withdrawable = ctx.ctx_contract_balance / 4 ∧
    st'.seller_withdrawable = (ctx.ctx_contract_balance / 4) * 3 ∧
    acts = []

/-- `withdraw` in the withdrawals state rejects nonzero attached amount. -/
def spec_receive_withdraw_nonzero_amount_fails (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (st : State),
    st.next_step = NextStep.withdrawals →
    ctx.ctx_amount ≠ 0 →
    ∃ e : Error, impl.escrowV2.receive chain ctx st (some Msg.withdraw) = Except.error e

/-- `withdraw` in the withdrawals state rejects senders who are neither buyer nor seller. -/
def spec_receive_withdraw_unauthorized_fails (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (st : State),
    st.next_step = NextStep.withdrawals →
    ctx.ctx_amount = 0 →
    ctx.ctx_from ≠ st.buyer →
    ctx.ctx_from ≠ st.seller →
    ∃ e : Error, impl.escrowV2.receive chain ctx st (some Msg.withdraw) = Except.error e

/-- A successful buyer withdrawal zeroes the buyer share and emits a transfer to the buyer. -/
def spec_receive_withdraw_buyer_success (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (st st' : State) (acts : List ActionBody),
    st.next_step = NextStep.withdrawals →
    ctx.ctx_amount = 0 →
    ctx.ctx_from = st.buyer →
    impl.escrowV2.receive chain ctx st (some Msg.withdraw) = Except.ok (st', acts) →
    st'.buyer_withdrawable = 0 ∧
    st'.seller_withdrawable = st.seller_withdrawable ∧
    (st.seller_withdrawable = 0 → st'.next_step = NextStep.no_next_step) ∧
    (st.seller_withdrawable ≠ 0 → st'.next_step = NextStep.withdrawals) ∧
    acts = [ActionBody.act_transfer st.buyer st.buyer_withdrawable]

/-- Buyer withdrawal rejects when the buyer has no positive withdrawable balance. -/
def spec_receive_withdraw_buyer_no_funds_fails (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (st : State),
    st.next_step = NextStep.withdrawals →
    ctx.ctx_amount = 0 →
    ctx.ctx_from = st.buyer →
    st.buyer_withdrawable ≤ 0 →
    ∃ e : Error, impl.escrowV2.receive chain ctx st (some Msg.withdraw) = Except.error e

/-- A successful seller withdrawal zeroes the seller share and emits a transfer to the seller. -/
def spec_receive_withdraw_seller_success (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (st st' : State) (acts : List ActionBody),
    st.next_step = NextStep.withdrawals →
    ctx.ctx_amount = 0 →
    ctx.ctx_from = st.seller →
    ctx.ctx_from ≠ st.buyer →
    impl.escrowV2.receive chain ctx st (some Msg.withdraw) = Except.ok (st', acts) →
    st'.seller_withdrawable = 0 ∧
    st'.buyer_withdrawable = st.buyer_withdrawable ∧
    (st.buyer_withdrawable = 0 → st'.next_step = NextStep.no_next_step) ∧
    (st.buyer_withdrawable ≠ 0 → st'.next_step = NextStep.withdrawals) ∧
    acts = [ActionBody.act_transfer st.seller st.seller_withdrawable]

/-- Seller withdrawal rejects when the seller has no positive withdrawable balance. -/
def spec_receive_withdraw_seller_no_funds_fails (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (st : State),
    st.next_step = NextStep.withdrawals →
    ctx.ctx_amount = 0 →
    ctx.ctx_from = st.seller →
    ctx.ctx_from ≠ st.buyer →
    st.seller_withdrawable ≤ 0 →
    ∃ e : Error, impl.escrowV2.receive chain ctx st (some Msg.withdraw) = Except.error e

/-- Seller early-exit withdrawal rejects nonzero attached amount before checking other conditions. -/
def spec_receive_seller_exit_nonzero_amount_fails (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (st : State),
    st.next_step = NextStep.buyer_commit →
    ctx.ctx_amount ≠ 0 →
    ∃ e : Error, impl.escrowV2.receive chain ctx st (some Msg.withdraw) = Except.error e

/-- Seller early-exit withdrawal rejects calls after the source deadline guard expires. -/
def spec_receive_seller_exit_deadline_fails (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (st : State),
    st.next_step = NextStep.buyer_commit →
    ctx.ctx_amount = 0 →
    st.last_action + 50 < chain.current_slot →
    ∃ e : Error, impl.escrowV2.receive chain ctx st (some Msg.withdraw) = Except.error e

/-- Seller early-exit withdrawal rejects zero-amount calls from non-sellers before the deadline. -/
def spec_receive_seller_exit_wrong_sender_fails (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (st : State),
    st.next_step = NextStep.buyer_commit →
    ctx.ctx_amount = 0 →
    ¬ st.last_action + 50 < chain.current_slot →
    ctx.ctx_from ≠ st.seller →
    ∃ e : Error, impl.escrowV2.receive chain ctx st (some Msg.withdraw) = Except.error e

/-- Successful seller early-exit withdrawal terminates the protocol and pays the contract balance to the seller. -/
def spec_receive_seller_exit_success (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (st st' : State) (acts : List ActionBody),
    st.next_step = NextStep.buyer_commit →
    ctx.ctx_amount = 0 →
    ¬ st.last_action + 50 < chain.current_slot →
    ctx.ctx_from = st.seller →
    impl.escrowV2.receive chain ctx st (some Msg.withdraw) = Except.ok (st', acts) →
    st'.next_step = NextStep.no_next_step ∧
    acts = [ActionBody.act_transfer st.seller ctx.ctx_contract_balance]

/-- Missing messages are rejected in every protocol state. -/
def spec_receive_none_msg_fails (impl : RepoImpl) : Prop :=
  ∀ (chain : Chain) (ctx : ContractCallContext) (st : State),
    ∃ e : Error, impl.escrowV2.receive chain ctx st none = Except.error e
