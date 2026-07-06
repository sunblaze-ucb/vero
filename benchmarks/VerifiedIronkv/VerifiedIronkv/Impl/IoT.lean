import VerifiedIronkv.Impl.AppInterfaceT
-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VerifiedIronkv.Impl.IoT

Translated Verus vocabulary and reference implementations for `IoT`.

DO NOT MODIFY types or signatures. Implement only the marked function bodies.
-/

inductive HostEnvironment where
  | mk
  deriving Repr, DecidableEq, BEq, Inhabited

structure EndPoint where
  id : List Nat
  deriving Repr, DecidableEq, BEq, Inhabited

inductive State where
  | Receiving
  | Sending
  | Error
  deriving Repr, DecidableEq, BEq, Inhabited

structure IronfleetIOError where
  message : String
  deriving Repr, DecidableEq, BEq, Inhabited

structure NetClientCPointers where
  get_time_func : Nat
  receive_func : Nat
  send_func : Nat
  deriving Repr, DecidableEq, BEq, Inhabited

abbrev NetPacket := LPacket AbstractEndPoint (List Nat)

abbrev NetEvent := LIoOp AbstractEndPoint (List Nat)

abbrev History := List NetEvent

inductive NetcReceiveResult where
  | Received (sender : EndPoint) (message : List Nat)
  | TimedOut
  | Error
  deriving Repr, DecidableEq, BEq, Inhabited

structure DuctTapeProfiler where
  last_event : Nat
  last_report : Nat
  event_counter : List (String × Nat)
  deriving Repr, DecidableEq, BEq, Inhabited

structure NetClient where
  state : State
  history : History
  end_point : EndPoint
  c_pointers : NetClientCPointers
  profiler : DuctTapeProfiler
  deriving Repr, DecidableEq, BEq, Inhabited

def ioTView (x : EndPoint) : AbstractEndPoint :=
  { id := x.id }

def ioSendTrustedCallbackModel (pre post : NetClient) (recipient : EndPoint) (message : List Nat) (result : Except IronfleetIOError Unit) : Prop :=
  post.end_point = pre.end_point ∧
  post.c_pointers = pre.c_pointers ∧
  post.profiler = pre.profiler ∧
  match result with
  | Except.ok _ => post.state = State.Sending ∧ post.history = pre.history ++ [LIoOp.Send { dst := ioTView recipient, src := ioTView pre.end_point, msg := message }]
  | Except.error _ => post.state = State.Error ∧ post.history = pre.history

def ioSendInternalWrapperFrameModel (pre wrapperPost : NetClient) : Prop :=
  wrapperPost = pre

def ioSendInternalResultPolicy (result : Except IronfleetIOError Unit) : Prop :=
  match result with
  | Except.ok _ => True
  | Except.error err => err.message = "Failed to send"

def ioSendInternalWrapperBridgeModel (pre wrapperPost : NetClient) (result : Except IronfleetIOError Unit) : Prop :=
  ioSendInternalWrapperFrameModel pre wrapperPost ∧
  ioSendInternalResultPolicy result

namespace Bank

abbrev ValidPhysicalAddressSig := EndPoint → Bool
abbrev SendSig := NetClient → EndPoint → List Nat → NetClient × Except IronfleetIOError Unit
abbrev NewL202Sig := EndPoint → NetClientCPointers → NetClient
abbrev ReceiveInternalSig := NetClient → Int → NetClient × NetcReceiveResult
abbrev SendInternalSig := NetClient → EndPoint → List Nat → NetClient × Except IronfleetIOError Unit
abbrev SendInternalWrapperSig := NetClient → EndPoint → List Nat → NetClient × Except IronfleetIOError Unit
abbrev ResetSig := NetClient → NetClient

end Bank

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=valid_physical_address
-- !benchmark @end code_aux def=valid_physical_address

def Bank.valid_physical_address : Bank.ValidPhysicalAddressSig :=
-- !benchmark @start code def=valid_physical_address
  fun ep => decide (ep.id.length < 1048576)
-- !benchmark @end code def=valid_physical_address

opaque Bank.new_l202 : Bank.NewL202Sig

opaque Bank.receive_internal : Bank.ReceiveInternalSig

opaque Bank.send_internal : Bank.SendInternalSig

opaque Bank.send_internal_wrapper : Bank.SendInternalWrapperSig

def ioSendInternalWrapperCallBridge (netc : NetClient) (recipient : EndPoint) (message : List Nat) : Prop :=
  let trusted := Bank.send_internal_wrapper netc recipient message
  ioSendInternalWrapperBridgeModel netc trusted.1 trusted.2

opaque Bank.reset : Bank.ResetSig

-- !benchmark @start code_aux def=send
-- !benchmark @end code_aux def=send

noncomputable def Bank.send : Bank.SendSig :=
-- !benchmark @start code def=send
  fun netc recipient message =>
    let trusted := Bank.send_internal_wrapper netc recipient message
    match trusted.2 with
    | Except.ok () =>
        let post := { netc with state := State.Sending, history := netc.history ++ [LIoOp.Send { dst := ioTView recipient, src := ioTView netc.end_point, msg := message }] }
        (post, Except.ok ())
    | Except.error err =>
        ({ netc with state := State.Error }, Except.error err)
-- !benchmark @end code def=send
