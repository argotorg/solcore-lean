import Solcore.Frontend.RustHull.AccountRuntime

/-! Execute a selected Hull object on Core with byte calldata, shared message
state and explicit account context. The transaction caller supplies the entry
balance after transferring call value; the receipt exports committed balances. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.Contract

structure Context where
  calldata : List UInt8 := []
  storage : Core.WordMapping.Entries := []
  value : Core.Word := Core.Word.zero
  caller : Core.Word := Core.Word.zero
  address : Core.Word := Core.Word.zero
  /-- An explicit environment input, not a gas meter for Core transitions. -/
  availableGas : Option Core.Word := none
  /-- Balance on entry, including the value transferred by this message. -/
  balance : Core.Word := Core.Word.zero
  /-- Explicit balances of other accounts; the current address is overwritten by `balance`. -/
  accounts : Core.WordMapping.Entries := []
  /-- Accounts known to have no executable code. Unknown call targets are rejected. -/
  emptyAccounts : List Core.Word := []
  isStatic : Bool := false
  /-- False while init code is running, before runtime code is installed. -/
  selfCodeAvailable : Bool := true
  deriving Repr

def snapshotType : Core.Ty := AccountRuntime.snapshotType

def resultType : Core.Ty := AccountRuntime.resultType

structure Prepared where
  expression : Core.Expr
  context : Context
  deriving Repr

/-- One checked runtime object, reusable across independent call contexts. -/
structure CompiledObject where
  expression : Core.Expr
  deriving Repr

def contextType : Core.Ty := AccountRuntime.contextType

private def calldataEntries (bytes : List UInt8) : Core.WordMapping.Entries :=
  Memory.packBytes bytes

def compileObject (program : Program) (objectPath : List String)
    (fuel : Nat := 4096) (codeBytes : Option (List UInt8) := none) : LowerM CompiledObject := do
  return ⟨← AccountRuntime.compileObject program objectPath fuel codeBytes⟩

def CompiledObject.instantiate (compiled : CompiledObject) (context : Context := {}) : Prepared :=
  let address (value : Core.Word) := Core.Word.ofNatModulo (value.val % 2 ^ 160)
  let context := {context with
    address := address context.address, caller := address context.caller,
    accounts := context.accounts.map fun (key, value) => (address key, value),
    emptyAccounts := context.emptyAccounts.map address}
  let availableGas := match context.availableGas with
    | none => Core.Expr.inLeft .word .unit
    | some gas => .inRight .unit (.word gas)
  let argument := bundle [Core.WordMapping.literal (calldataEntries context.calldata),
    .word (Core.Word.ofNatModulo context.calldata.length), Core.WordMapping.literal context.storage,
    .word context.value, .word context.caller, .word context.address, availableGas,
    Core.WordMapping.literal (Core.WordMapping.insertEntries context.address context.balance context.accounts),
    Core.WordMapping.literal (context.emptyAccounts.map fun address => (address, Core.Word.ofNatModulo 1)),
    .bool context.isStatic, .bool context.selfCodeAvailable]
  ⟨.apply compiled.expression argument, context⟩

def prepare (program : Program) (objectPath : List String) (context : Context := {})
    (fuel : Nat := 4096) : LowerM Prepared := do
  return (← compileObject program objectPath fuel).instantiate context

private def mappingEntries : Core.Value → Except String Core.WordMapping.Entries
  | .constructed constructor .unit =>
      if constructor = Core.WordMapping.nilConstructor then pure []
      else .error "unexpected empty mapping constructor"
  | .constructed constructor (.pair (.pair (.word key) (.word value)) tail) => do
      unless constructor = Core.WordMapping.consConstructor do throw "unexpected mapping constructor"
      pure ((key, value) :: (← mappingEntries tail))
  | _ => .error "invalid mapping result"

inductive Outcome where
  | returned (bytes : List UInt8) (storage : Core.WordMapping.Entries)
  | reverted (bytes : List UInt8)
  | invalid
  | languageFailure (reason : Core.Value)
  | outOfFuel (state : Core.State)
  | coreFault (error : Core.MachineFault)
  | exportError (message : String)
  deriving Repr

structure Receipt where
  outcome : Outcome
  logs : List Logs.Event := []
  balances : Core.WordMapping.Entries := []
  deriving Repr

private def finishOutcome (maxReturnBytes : Nat) (result : Core.Value) : Outcome := Id.run do
  let .pair status (.pair (.word exit) (.pair (.word offset) (.pair (.word count)
      (.pair memory storage)))) := result | return .exportError "invalid runtime result shape"
  if exit.val = 3 then return .invalid
  if exit.val = 0 then
    match status with
    | .inLeft _ reason => return .languageFailure reason
    | .inRight _ .unit => pure ()
    | _ => return .exportError "invalid runtime completion"
  else if exit.val ≠ 1 && exit.val ≠ 2 then
    return .exportError "unknown runtime exit tag"
  if count.val > maxReturnBytes then return .exportError "return data exceeds the configured export limit"
  let entries ← match mappingEntries memory with
    | .ok entries => pure entries
    | .error error => return .exportError error
  let bytes := (List.range count.val).map fun index =>
    UInt8.ofNat (Memory.lookupByte entries (Core.Word.ofNatModulo (offset.val + index))).val
  if exit.val = 2 then return .reverted bytes
  match mappingEntries storage with
  | .ok storage => return .returned bytes storage
  | .error error => return .exportError error

private def finish (maxReturnBytes : Nat) (result : Core.Value) : Receipt := Id.run do
  let .pair status (.pair exit (.pair offset (.pair count
      (.pair memory (.pair storage (.pair logs (.pair cursor balances))))))) := result |
    return ⟨.exportError "invalid runtime receipt shape", [], []⟩
  let outcome := finishOutcome maxReturnBytes
    (.pair status (.pair exit (.pair offset (.pair count (.pair memory storage)))))
  match outcome with
  | .returned _ _ =>
      match Logs.decodeValues logs cursor 4096 maxReturnBytes, mappingEntries balances with
      | .ok events, .ok balances => return ⟨outcome, events, balances⟩
      | .error error, _ | _, .error error => return ⟨.exportError error, [], []⟩
  | _ => return ⟨outcome, [], []⟩

def resumeWithReceipt (state : Core.State) (fuel : Nat := 10000000)
    (maxReturnBytes : Nat := 1048576) : Receipt :=
  match Core.runStateful fuel state with
  | .done value _ => finish maxReturnBytes value
  | .outOfFuel state => ⟨.outOfFuel state, [], []⟩
  | .fault error _ => ⟨.coreFault error, [], []⟩

def runWithReceipt (prepared : Prepared) (fuel : Nat := 10000000)
    (maxReturnBytes : Nat := 1048576) : Receipt :=
  resumeWithReceipt (.initial prepared.expression) fuel maxReturnBytes

def resume (state : Core.State) (fuel : Nat := 10000000) (maxReturnBytes : Nat := 1048576) : Outcome :=
  (resumeWithReceipt state fuel maxReturnBytes).outcome

def run (prepared : Prepared) (fuel : Nat := 10000000) (maxReturnBytes : Nat := 1048576) : Outcome :=
  resume (.initial prepared.expression) fuel maxReturnBytes

end Solcore.Frontend.RustHull.Contract
