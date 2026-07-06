import EIP20V2.Impl.EIP20Token

/-!
# Eip20.EIP20V2.Impl.EIP20TokenCorrect

Frozen correctness vocabulary translated from the Coq `EIP20TokenCorrect`
module. This module contributes semantic helper predicates for the EIP20
receive specifications and has no scored API implementation slots.

DO NOT MODIFY types or signatures. This module has no API code markers.
-/

def transfer_balance_update_correct (old_state new_state : State) (fromAddr to : Address) (tokens : TokenValue) : Bool :=
  let getBalance addr state := withDefault 0 (lookup addr state.balances)
  let fromBefore := getBalance fromAddr old_state
  let toBefore := getBalance to old_state
  let fromAfter := getBalance fromAddr new_state
  let toAfter := getBalance to new_state
  if fromAddr = to then
    (fromBefore == fromAfter) && (toBefore == toAfter)
  else
    (fromBefore == fromAfter + tokens) && (toBefore + tokens == toAfter)

def transfer_from_allowances_update_correct (old_state new_state : State) (fromAddr delegate : Address) (tokens : TokenValue) : Bool :=
  let before := get_allowance old_state fromAddr delegate
  let after := get_allowance new_state fromAddr delegate
  before == after + tokens

def approve_allowance_update_correct (new_state : State) (fromAddr delegate : Address) (tokens : TokenValue) : Bool :=
  get_allowance new_state fromAddr delegate == tokens
