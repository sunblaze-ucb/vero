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

axiom reachable : ChainState → Prop

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
