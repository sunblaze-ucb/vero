import PiggybankV2.Impl.PiggyBank

/-!
# PiggybankV2.Test

Executable conformance tests. `#guard` assertions run against the
curator's reference implementations inside the `code` markers.

DO NOT MODIFY -- benchmark infrastructure.
-/

open PiggybankV2

#guard error_no_msg == 1

#guard error_not_owner == 2

#guard error_already_smashed == 3

#guard error_amount_not_positive == 4

#guard error_amount_not_zero == 5

#guard is_smashed { balance := 7, owner := 1, piggyState := PiggyState.Intact } == false

#guard is_smashed { balance := 0, owner := 1, piggyState := PiggyState.Smashed } == true

#guard
  match insert { balance := 10, owner := 1, piggyState := PiggyState.Intact } { ctx_from := 2, ctx_amount := 5 } with
  | Except.ok (state, acts) =>
      state == { balance := 15, owner := 1, piggyState := PiggyState.Intact } && acts == []
  | _ => false

#guard
  match insert { balance := 10, owner := 1, piggyState := PiggyState.Intact } { ctx_from := 2, ctx_amount := -1 } with
  | Except.error e => e == error_amount_not_positive
  | _ => false

#guard
  match insert { balance := 0, owner := 1, piggyState := PiggyState.Smashed } { ctx_from := 2, ctx_amount := 5 } with
  | Except.error e => e == error_already_smashed
  | _ => false

#guard
  match smash { balance := 10, owner := 1, piggyState := PiggyState.Intact } { ctx_from := 2, ctx_amount := 3 } with
  | Except.error e => e == error_not_owner
  | _ => false

#guard
  match smash { balance := 10, owner := 1, piggyState := PiggyState.Intact } { ctx_from := 1, ctx_amount := 3 } with
  | Except.ok (state, acts) =>
      state == { balance := 0, owner := 1, piggyState := PiggyState.Smashed } &&
        acts == [ActionBody.act_transfer 1 13]
  | _ => false

#guard
  match receive () { ctx_from := 2, ctx_amount := 5 } { balance := 10, owner := 1, piggyState := PiggyState.Intact } none with
  | Except.error e => e == error_no_msg
  | _ => false

#guard
  match receive () { ctx_from := 2, ctx_amount := 5 } { balance := 10, owner := 1, piggyState := PiggyState.Intact } (some Msg.Insert) with
  | Except.ok (state, acts) =>
      state == { balance := 15, owner := 1, piggyState := PiggyState.Intact } && acts == []
  | _ => false

#guard
  match receive () { ctx_from := 1, ctx_amount := 3 } { balance := 10, owner := 1, piggyState := PiggyState.Intact } (some Msg.Smash) with
  | Except.ok (state, acts) =>
      state == { balance := 0, owner := 1, piggyState := PiggyState.Smashed } &&
        acts == [ActionBody.act_transfer 1 13]
  | _ => false

#guard
  match init () { ctx_from := 7, ctx_amount := 11 } () with
  | Except.ok state => state == { balance := 11, owner := 7, piggyState := PiggyState.Intact }
  | _ => false
