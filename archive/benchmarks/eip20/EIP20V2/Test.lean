import EIP20V2.Impl.EIP20Token
import EIP20V2.Impl.EIP20TokenCorrect
import EIP20V2.Impl.EIP20TokenTests

/-!
# EIP20V2.Test

Executable conformance tests. `#guard` assertions run against the curator's
reference implementations that live inside the `code` markers in `Impl/*.lean`.

DO NOT MODIFY - infrastructure.
-/

#guard match EIP20V2.init empty_chain { ctx_from := 1, ctx_amount := 0 } { owner := 1, init_amount := 100 } with
  | Except.ok state => state == { total_supply := 100, balances := [(1, 100)], allowances := [] }
  | Except.error _ => false

#guard match EIP20V2.try_transfer 1 2 30 { total_supply := 100, balances := [(1, 100)], allowances := [] } with
  | Except.ok state => state == { total_supply := 100, balances := [(2, 30), (1, 70)], allowances := [] }
  | Except.error _ => false

#guard match EIP20V2.try_transfer 1 2 130 { total_supply := 100, balances := [(1, 100)], allowances := [] } with
  | Except.error err => err == default_error
  | Except.ok _ => false

#guard match EIP20V2.try_approve 1 2 40 { total_supply := 100, balances := [(1, 100)], allowances := [] } with
  | Except.ok state => state == { total_supply := 100, balances := [(1, 100)], allowances := [(1, [(2, 40)])] }
  | Except.error _ => false

#guard match EIP20V2.try_transfer_from 2 1 3 25 { total_supply := 100, balances := [(1, 100)], allowances := [(1, [(2, 40)])] } with
  | Except.ok state => state == { total_supply := 100, balances := [(3, 25), (1, 75)], allowances := [(1, [(2, 15)])] }
  | Except.error _ => false

#guard match EIP20V2.try_transfer_from 2 1 3 45 { total_supply := 100, balances := [(1, 100)], allowances := [(1, [(2, 40)])] } with
  | Except.error err => err == default_error
  | Except.ok _ => false

#guard match EIP20V2.try_transfer_from 2 1 3 10 { total_supply := 100, balances := [(1, 100)], allowances := [] } with
  | Except.error err => err == default_error
  | Except.ok _ => false

#guard match EIP20V2.try_transfer_from 4 1 3 10 { total_supply := 100, balances := [(1, 100)], allowances := [(1, [(2, 40)])] } with
  | Except.error err => err == default_error
  | Except.ok _ => false

#guard match EIP20V2.receive empty_chain { ctx_from := 1, ctx_amount := 0 } { total_supply := 100, balances := [(1, 100)], allowances := [] } (some (Msg.transfer 2 10)) with
  | Except.ok (state, acts) => state == { total_supply := 100, balances := [(2, 10), (1, 90)], allowances := [] } && acts == []
  | Except.error _ => false

#guard match EIP20V2.receive empty_chain { ctx_from := 2, ctx_amount := 0 } { total_supply := 100, balances := [(1, 100)], allowances := [(1, [(2, 40)])] } (some (Msg.transfer_from 1 3 25)) with
  | Except.ok (state, acts) => state == { total_supply := 100, balances := [(3, 25), (1, 75)], allowances := [(1, [(2, 15)])] } && acts == []
  | Except.error _ => false

#guard match EIP20V2.receive empty_chain { ctx_from := 1, ctx_amount := 0 } { total_supply := 100, balances := [(1, 100)], allowances := [] } (some (Msg.approve 2 10)) with
  | Except.ok (state, acts) => state == { total_supply := 100, balances := [(1, 100)], allowances := [(1, [(2, 10)])] } && acts == []
  | Except.error _ => false

#guard match EIP20V2.receive empty_chain { ctx_from := 1, ctx_amount := 0 } { total_supply := 100, balances := [(1, 100)], allowances := [] } none with
  | Except.error err => err == default_error
  | Except.ok _ => false

#guard match EIP20V2.receive empty_chain { ctx_from := 1, ctx_amount := 1 } { total_supply := 100, balances := [(1, 100)], allowances := [] } (some (Msg.approve 2 10)) with
  | Except.error err => err == default_error
  | Except.ok _ => false
