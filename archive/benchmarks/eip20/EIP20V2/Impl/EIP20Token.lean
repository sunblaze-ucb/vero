-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Eip20.EIP20V2.Impl.EIP20Token

Core EIP20 token vocabulary, finite-map helpers, operational trace helpers,
API signatures, and reference implementations translated from the Coq
`EIP20Token` module.

DO NOT MODIFY types or signatures. Implement only the function bodies inside
the `code` markers.
-/

-- Core contract and chain model types.

abbrev Address := Nat

structure Chain where
  current_slot : Nat
  deriving Repr, DecidableEq, BEq

def empty_chain : Chain := { current_slot := 0 }

structure ContractCallContext where
  ctx_from : Address
  ctx_amount : Int
  deriving Repr, DecidableEq, BEq

inductive ActionBody where
  | transfer (fromAddr to : Address) (amount : Int)
  deriving Repr, DecidableEq, BEq

abbrev AddressMap (α : Type) := List (Address × α)

abbrev TokenValue := Nat

abbrev Error := Nat

inductive Msg where
  | transfer (to : Address) (amount : TokenValue)
  | transfer_from (fromAddr : Address) (to : Address) (amount : TokenValue)
  | approve (delegate : Address) (amount : TokenValue)
  deriving Repr, DecidableEq, BEq

structure State where
  total_supply : TokenValue
  balances : AddressMap TokenValue
  allowances : AddressMap (AddressMap TokenValue)
  deriving Repr, DecidableEq, BEq

structure Setup where
  owner : Address
  init_amount : TokenValue
  deriving Repr, DecidableEq, BEq

structure Contract where
  init : Chain → ContractCallContext → Setup → Except Error State
  receive : Chain → ContractCallContext → State → Option Msg → Except Error (State × List ActionBody)

structure DeploymentInfo where
  deployment_setup : Setup
  deriving Repr, DecidableEq, BEq

structure ChainState where
  env_contracts : AddressMap Contract
  contract_states : AddressMap State
  outgoing_actions : AddressMap (List ActionBody)
  deployment_infos : AddressMap DeploymentInfo

-- Frozen helpers for the list-map representation and semantic model.

def lookup {α β : Type} [DecidableEq α] (key : α) (entries : List (α × β)) : Option β :=
  match entries with
  | [] => none
  | (k, v) :: rest => if k = key then some v else lookup key rest

def setEntry {α β : Type} [DecidableEq α] (key : α) (value : β) (entries : List (α × β)) : List (α × β) :=
  (key, value) :: entries.filter (fun entry => decide (entry.1 ≠ key))

def withDefault {α : Type} (fallback : α) : Option α → α
  | some value => value
  | none => fallback

def isOk {ε α : Type} : Except ε α → Bool
  | Except.ok _ => true
  | Except.error _ => false

def isSome {α : Type} : Option α → Bool
  | some _ => true
  | none => false

def withoutActions : Except Error State → Except Error (State × List ActionBody)
  | Except.ok state => Except.ok (state, [])
  | Except.error err => Except.error err

def default_error : Error := 1

def error (α : Type) : Except Error α := Except.error default_error

def increment_balance (m : AddressMap TokenValue) (addr : Address) (inc : TokenValue) : AddressMap TokenValue :=
  let old := withDefault 0 (lookup addr m)
  setEntry addr (old + inc) m

def sum_balances (state : State) : TokenValue :=
  state.balances.foldl (fun acc entry => acc + entry.2) 0

def get_allowance (state : State) (fromAddr delegate : Address) : TokenValue :=
  match lookup fromAddr state.allowances with
  | some fromAllowances => withDefault 0 (lookup delegate fromAllowances)
  | none => 0

def mapWF {α β : Type} (entries : List (α × β)) : Prop :=
  entries.Pairwise (fun left right => left.1 ≠ right.1)

def tokenMapEquiv (lhs rhs : AddressMap TokenValue) : Prop :=
  ∀ addr : Address, lookup addr lhs = lookup addr rhs

def allowanceOwnerEquiv (lhs rhs : AddressMap (AddressMap TokenValue)) (owner : Address) : Prop :=
  match lookup owner lhs, lookup owner rhs with
  | none, none => True
  | some left, some right => tokenMapEquiv left right
  | _, _ => False

def allowanceMapEquiv (lhs rhs : AddressMap (AddressMap TokenValue)) : Prop :=
  ∀ owner : Address, allowanceOwnerEquiv lhs rhs owner

def stateWF (state : State) : Prop :=
  mapWF state.balances ∧
  mapWF state.allowances ∧
  ∀ owner ownerAllowances, lookup owner state.allowances = some ownerAllowances → mapWF ownerAllowances

def contract
    (initFn : Chain → ContractCallContext → Setup → Except Error State)
    (receiveFn : Chain → ContractCallContext → State → Option Msg → Except Error (State × List ActionBody)) :
    Contract :=
  { init := initFn, receive := receiveFn }

def empty_state : ChainState :=
  { env_contracts := [], contract_states := [], outgoing_actions := [], deployment_infos := [] }

def env_contracts (state : ChainState) (addr : Address) : Option Contract :=
  lookup addr state.env_contracts

def contract_state (state : ChainState) (addr : Address) : Option State :=
  lookup addr state.contract_states

def outgoing_acts (state : ChainState) (addr : Address) : List ActionBody :=
  withDefault [] (lookup addr state.outgoing_actions)

def chainStateWF (state : ChainState) : Prop :=
  mapWF state.env_contracts ∧
  mapWF state.contract_states ∧
  mapWF state.outgoing_actions ∧
  mapWF state.deployment_infos ∧
  ∀ addr cstate, contract_state state addr = some cstate → stateWF cstate

def deployState
    (state : ChainState) (addr : Address) (setup : Setup) (deployedState : State)
    (initFn : Chain → ContractCallContext → Setup → Except Error State)
    (receiveFn : Chain → ContractCallContext → State → Option Msg → Except Error (State × List ActionBody)) : ChainState :=
  { env_contracts := setEntry addr (contract initFn receiveFn) state.env_contracts,
    contract_states := setEntry addr deployedState state.contract_states,
    outgoing_actions := setEntry addr [] state.outgoing_actions,
    deployment_infos := setEntry addr { deployment_setup := setup } state.deployment_infos }

def callSuccessState (state : ChainState) (addr : Address) (newState : State) (acts : List ActionBody) : ChainState :=
  { env_contracts := state.env_contracts,
    contract_states := setEntry addr newState state.contract_states,
    outgoing_actions := setEntry addr acts state.outgoing_actions,
    deployment_infos := state.deployment_infos }

inductive ChainTrace
    (initFn : Chain → ContractCallContext → Setup → Except Error State)
    (receiveFn : Chain → ContractCallContext → State → Option Msg → Except Error (State × List ActionBody)) :
    ChainState → ChainState → Type where
  | empty (state : ChainState) : ChainTrace initFn receiveFn state state
  | deploy {fromState midState : ChainState}
      (trace : ChainTrace initFn receiveFn fromState midState)
      (caddr : Address) (chain : Chain) (ctx : ContractCallContext) (setup : Setup) (deployedState : State)
      (hinit : initFn chain ctx setup = Except.ok deployedState)
      (hnotDeployed : env_contracts midState caddr = none) :
      ChainTrace initFn receiveFn fromState (deployState midState caddr setup deployedState initFn receiveFn)
  | callOk {fromState midState : ChainState}
      (trace : ChainTrace initFn receiveFn fromState midState)
      (caddr : Address) (chain : Chain) (ctx : ContractCallContext) (oldState newState : State)
      (msg : Option Msg) (acts : List ActionBody)
      (hcontract : env_contracts midState caddr = some (contract initFn receiveFn))
      (hstate : contract_state midState caddr = some oldState)
      (hreceive : receiveFn chain ctx oldState msg = Except.ok (newState, acts)) :
      ChainTrace initFn receiveFn fromState (callSuccessState midState caddr newState acts)
  | callErr {fromState midState : ChainState}
      (trace : ChainTrace initFn receiveFn fromState midState)
      (caddr : Address) (chain : Chain) (ctx : ContractCallContext) (oldState : State)
      (msg : Option Msg) (err : Error)
      (hcontract : env_contracts midState caddr = some (contract initFn receiveFn))
      (hstate : contract_state midState caddr = some oldState)
      (hreceive : receiveFn chain ctx oldState msg = Except.error err) :
      ChainTrace initFn receiveFn fromState midState

def reachable
    (initFn : Chain → ContractCallContext → Setup → Except Error State)
    (receiveFn : Chain → ContractCallContext → State → Option Msg → Except Error (State × List ActionBody))
    (state : ChainState) : Prop :=
  Nonempty (ChainTrace initFn receiveFn empty_state state) ∧ chainStateWF state

def deployment_info
    {initFn : Chain → ContractCallContext → Setup → Except Error State}
    {receiveFn : Chain → ContractCallContext → State → Option Msg → Except Error (State × List ActionBody)}
    {fromState toState : ChainState}
    (_trace : ChainTrace initFn receiveFn fromState toState)
    (addr : Address) : Option DeploymentInfo :=
  lookup addr toState.deployment_infos

namespace EIP20V2

-- API signatures.

abbrev InitSig := Chain → ContractCallContext → Setup → Except Error State
abbrev TryTransferSig := Address → Address → TokenValue → State → Except Error State
abbrev TryTransferFromSig := Address → Address → Address → TokenValue → State → Except Error State
abbrev TryApproveSig := Address → Address → TokenValue → State → Except Error State
abbrev ReceiveSig := Chain → ContractCallContext → State → Option Msg → Except Error (State × List ActionBody)

end EIP20V2

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=init
-- !benchmark @end code_aux def=init

def EIP20V2.init : EIP20V2.InitSig :=
-- !benchmark @start code def=init
  fun _chain _ctx setup =>
    Except.ok
      { total_supply := setup.init_amount,
        balances := setEntry setup.owner setup.init_amount [],
        allowances := [] }
-- !benchmark @end code def=init

-- !benchmark @start code_aux def=try_transfer
-- !benchmark @end code_aux def=try_transfer

def EIP20V2.try_transfer : EIP20V2.TryTransferSig :=
-- !benchmark @start code def=try_transfer
  fun fromAddr to amount state =>
    let fromBalance := withDefault 0 (lookup fromAddr state.balances)
    if fromBalance < amount then
      error State
    else
      let debitedBalances := setEntry fromAddr (fromBalance - amount) state.balances
      let newBalances := increment_balance debitedBalances to amount
      Except.ok { state with balances := newBalances }
-- !benchmark @end code def=try_transfer

-- !benchmark @start code_aux def=try_transfer_from
-- !benchmark @end code_aux def=try_transfer_from

def EIP20V2.try_transfer_from : EIP20V2.TryTransferFromSig :=
-- !benchmark @start code def=try_transfer_from
  fun delegate fromAddr to amount state =>
    match lookup fromAddr state.allowances with
    | none => error State
    | some fromAllowances =>
        match lookup delegate fromAllowances with
        | none => error State
        | some delegateAllowance =>
            let fromBalance := withDefault 0 (lookup fromAddr state.balances)
            if delegateAllowance < amount || fromBalance < amount then
              error State
            else
              let newAllowances := setEntry delegate (delegateAllowance - amount) fromAllowances
              let debitedBalances := setEntry fromAddr (fromBalance - amount) state.balances
              let newBalances := increment_balance debitedBalances to amount
              Except.ok
                { state with
                  balances := newBalances,
                  allowances := setEntry fromAddr newAllowances state.allowances }
-- !benchmark @end code def=try_transfer_from

-- !benchmark @start code_aux def=try_approve
-- !benchmark @end code_aux def=try_approve

def EIP20V2.try_approve : EIP20V2.TryApproveSig :=
-- !benchmark @start code def=try_approve
  fun caller delegate amount state =>
    let callerAllowances :=
      match lookup caller state.allowances with
      | some allowances => allowances
      | none => []
    let newCallerAllowances := setEntry delegate amount callerAllowances
    Except.ok { state with allowances := setEntry caller newCallerAllowances state.allowances }
-- !benchmark @end code def=try_approve

-- !benchmark @start code_aux def=receive
-- !benchmark @end code_aux def=receive

def EIP20V2.receive : EIP20V2.ReceiveSig :=
-- !benchmark @start code def=receive
  fun _chain ctx state maybeMsg =>
    let sender := ctx.ctx_from
    if ctx.ctx_amount > 0 then
      error (State × List ActionBody)
    else
      match maybeMsg with
      | some (Msg.transfer to amount) =>
          withoutActions (EIP20V2.try_transfer sender to amount state)
      | some (Msg.transfer_from fromAddr to amount) =>
          withoutActions (EIP20V2.try_transfer_from sender fromAddr to amount state)
      | some (Msg.approve delegate amount) =>
          withoutActions (EIP20V2.try_approve sender delegate amount state)
      | none =>
          error (State × List ActionBody)
-- !benchmark @end code def=receive
