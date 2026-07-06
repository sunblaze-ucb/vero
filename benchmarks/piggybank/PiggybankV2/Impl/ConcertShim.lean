/-!
# PiggybankV2.Impl.ConcertShim

Minimal Lean model of the ConCert blockchain vocabulary needed by the
PiggyBank contract and its correctness statements.

DO NOT MODIFY types or signatures -- these are fixed vocabulary.
-/

abbrev Amount := Int

abbrev Address := Nat

abbrev Chain := Unit

structure ContractCallContext where
  ctx_from : Address
  ctx_amount : Amount
  deriving Repr, DecidableEq, BEq

opaque ChainState : Type

opaque DeploymentInfo : Type

opaque WeakContract : Type

inductive ActionBody where
  | act_transfer : Address → Amount → ActionBody
  | act_deploy : ActionBody
  | act_call : ActionBody
  deriving Repr, DecidableEq, BEq

opaque Contract : Type → Type → Type → Type → Type

opaque ChainTrace : ChainState → ChainState → Type

def address_neqb (x y : Address) : Bool := x != y

def address_eqb (x y : Address) : Bool := x == y

axiom build_contract :
  {Setup Msg State Error : Type} →
    (Chain → ContractCallContext → Setup → Except Error State) →
    (Chain → ContractCallContext → State → Option Msg → Except Error (State × List ActionBody)) →
    Contract Setup Msg State Error

axiom toWeakContract :
  {Setup Msg State Error : Type} →
    Contract Setup Msg State Error → WeakContract

axiom empty_state : ChainState

/-- ConCert's `reachable`: existence of a trace from the empty chain state. -/
def reachable (bstate : ChainState) : Prop :=
  Nonempty (ChainTrace empty_state bstate)

axiom env_contracts : ChainState → Address → Option WeakContract

axiom outgoing_acts : ChainState → Address → List ActionBody

axiom contract_state : {State : Type} → ChainState → Address → Option State

axiom env_account_balances : ChainState → Address → Amount

set_option linter.unusedVariables false

axiom deployment_info :
  {Setup : Type} →
    {bstate : ChainState} →
    ChainTrace empty_state bstate → Address → Option DeploymentInfo

set_option linter.unusedVariables true

axiom deployment_from : DeploymentInfo → Address

axiom account_balance_nonnegative :
  ∀ (bstate : ChainState) (addr : Address),
    (0 : Amount) ≤ env_account_balances bstate addr

/-- Amount carried by an action body; only transfers move funds. -/
def actBodyAmount : ActionBody → Amount
  | ActionBody.act_transfer _ amt => amt
  | ActionBody.act_deploy => 0
  | ActionBody.act_call => 0

/-- Sum of a measure over a list, ConCert's `sumZ`. -/
def sumZ {α : Type} (f : α → Amount) : List α → Amount
  | [] => 0
  | a :: rest => f a + sumZ f rest

/-- ConCert's `contract_induction`, with only unobserved height and history
indices erased.

The cases mirror `BlockchainInduction.v`: deployment, execution of a queued
action, nonrecursive and recursive calls, and queue permutation. Crucially, the
conclusion instantiates `P` with the deployed address and metadata, stored
state, on-chain balance, and actual outgoing queue. This trusted principle is
the boundary replacing ConCert's unported `ChainStep` operational semantics. -/
axiom contract_induction
    {Setup Msg State Error : Type}
    (init : Chain → ContractCallContext → Setup → Except Error State)
    (receive :
      Chain → ContractCallContext → State → Option Msg →
        Except Error (State × List ActionBody))
    (P : Address → DeploymentInfo → State → Amount → List ActionBody → Prop) :
  (∀ (chain : Chain) (ctx : ContractCallContext) (setup : Setup)
      (st : State) (caddr : Address) (dep : DeploymentInfo),
      init chain ctx setup = Except.ok st →
      deployment_from dep = ctx.ctx_from →
      P caddr dep st ctx.ctx_amount []) →
  (∀ (caddr : Address) (dep : DeploymentInfo) (st : State)
      (balance : Amount) (act : ActionBody) (queue : List ActionBody),
      P caddr dep st balance (act :: queue) →
      P caddr dep st (balance - actBodyAmount act) queue) →
  (∀ (chain : Chain) (ctx : ContractCallContext) (caddr : Address)
      (dep : DeploymentInfo) (prev : State) (msg : Option Msg)
      (queue : List ActionBody) (balance : Amount) (next : State)
      (newActs : List ActionBody),
      ctx.ctx_from ≠ caddr →
      P caddr dep prev balance queue →
      receive chain ctx prev msg = Except.ok (next, newActs) →
      P caddr dep next (balance + ctx.ctx_amount) (newActs ++ queue)) →
  (∀ (chain : Chain) (ctx : ContractCallContext) (caddr : Address)
      (dep : DeploymentInfo) (prev : State) (msg : Option Msg)
      (head : ActionBody) (queue : List ActionBody) (balance : Amount)
      (next : State) (newActs : List ActionBody),
      ctx.ctx_from = caddr →
      P caddr dep prev balance (head :: queue) →
      (match head with
        | ActionBody.act_transfer to amount =>
            to = caddr ∧ amount = ctx.ctx_amount ∧ msg = none
        | ActionBody.act_call => msg ≠ none
        | ActionBody.act_deploy => False) →
      receive chain ctx prev msg = Except.ok (next, newActs) →
      P caddr dep next balance (newActs ++ queue)) →
  (∀ (caddr : Address) (dep : DeploymentInfo) (st : State)
      (balance : Amount) (queue queue' : List ActionBody),
      P caddr dep st balance queue →
      List.Perm queue queue' →
      P caddr dep st balance queue') →
  ∀ (bstate : ChainState) (caddr : Address)
      (trace : ChainTrace empty_state bstate),
    env_contracts bstate caddr =
        some (toWeakContract (build_contract init receive)) →
      ∃ (dep : DeploymentInfo) (cstate : State),
        deployment_info (Setup := Setup) trace caddr = some dep ∧
        contract_state bstate caddr = some cstate ∧
        P caddr dep cstate
          (env_account_balances bstate caddr)
          (outgoing_acts bstate caddr)
