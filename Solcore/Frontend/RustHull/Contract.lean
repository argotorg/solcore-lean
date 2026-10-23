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
  ambient : Ambient.Context := {}
  /-- Concrete account records available to nested execution. -/
  world : List AccountState.Account := []
  /-- An omitted account is known empty only for an explicitly complete world. -/
  completeWorld : Bool := false
  nonce : Core.Word := Core.Word.ofNatModulo 1
  created : Bool := false
  deploying : Bool := false
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
  /-- Root image first, followed by the compiler's catalog order. -/
  codeImages : List (Option (List UInt8)) := []
  deriving Repr

def contextType : Core.Ty := AccountRuntime.contextType

private def calldataEntries (bytes : List UInt8) : Core.WordMapping.Entries :=
  Memory.packBytes bytes

def compileObject (program : Program) (objectPath : List String)
    (fuel : Nat := 4096) (codeBytes : Option (List UInt8) := none)
    (catalog : List AccountRuntime.CodeDefinition := []) : LowerM CompiledObject := do
  let expression ← AccountRuntime.compileObject program objectPath fuel codeBytes catalog
  return {
    expression := expression
    codeImages := codeBytes :: catalog.map (some ∘ AccountRuntime.CodeDefinition.bytes)
  }

private def codeIdentity (images : List (Option (List UInt8))) (code : Option (List UInt8)) : Nat :=
  match code with
  | none => 0
  | some bytes => ((images.zipIdx).find? fun (image, _) => image == some bytes).map
      (fun (_, index) => index + 1) |>.getD 0

def CompiledObject.instantiate (compiled : CompiledObject) (context : Context := {}) : Prepared :=
  let address (value : Core.Word) := Core.Word.ofNatModulo (value.val % 2 ^ 160)
  let world := context.world.foldl (fun accounts account =>
    let account := {account with address := address account.address}
    if accounts.any (·.address == account.address) then accounts else accounts ++ [account]) []
  let context := {context with
    address := address context.address, caller := address context.caller,
    accounts := context.accounts.map fun (key, value) => (address key, value),
    emptyAccounts := (context.emptyAccounts.map address).eraseDups,
    world := world}
  let rootCode := if context.selfCodeAvailable then compiled.codeImages.head?.getD none else some []
  let current := {((context.world.find? (·.address == context.address)).getD
      {address := context.address}) with
    storage := context.storage, nonce := context.nonce, code := rootCode, created := context.created}
  let supplied := context.world.filter (·.address != context.address)
  let empty := context.emptyAccounts.filterMap fun account =>
    if account == context.address || supplied.any (·.address == account) then none
    else some ({address := account} : AccountState.Account)
  let world := (current :: (supplied ++ empty)).map fun account =>
    let identity := if account.address == context.address then
      (if context.selfCodeAvailable then 1 else 0)
      else codeIdentity compiled.codeImages account.code
    (account, identity)
  let availableGas := match context.availableGas with
    | none => Core.Expr.inLeft .word .unit
    | some gas => .inRight .unit (.word gas)
  let argument := bundle [Core.WordMapping.literal (calldataEntries context.calldata),
    .word (Core.Word.ofNatModulo context.calldata.length),
    .word context.value, .word context.caller, .word context.address, availableGas,
    Core.WordMapping.literal (Core.WordMapping.insertEntries context.address context.balance context.accounts),
    AccountState.literal world, .bool context.isStatic, .bool context.completeWorld,
    Ambient.contextExpression context.ambient, .bool context.deploying]
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
  world : List AccountState.Account := []
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
      (.pair memory (.pair storage (.pair logs (.pair cursor (.pair balances world)))))))) := result |
    return ⟨.exportError "invalid runtime receipt shape", [], [], []⟩
  let outcome := finishOutcome maxReturnBytes
    (.pair status (.pair exit (.pair offset (.pair count (.pair memory storage)))))
  match outcome with
  | .returned _ _ =>
      match Logs.decodeValues logs cursor 4096 maxReturnBytes, mappingEntries balances,
          AccountState.decode world with
      | .ok events, .ok balances, .ok world => return ⟨outcome, events, balances, world⟩
      | .error error, _, _ | _, .error error, _ | _, _, .error error =>
          return ⟨.exportError error, [], [], []⟩
  | _ => return ⟨outcome, [], [], []⟩

def resumeWithReceipt (state : Core.State) (fuel : Nat := 10000000)
    (maxReturnBytes : Nat := 1048576) : Receipt :=
  match Core.runStateful fuel state with
  | .done value _ => finish maxReturnBytes value
  | .outOfFuel state => ⟨.outOfFuel state, [], [], []⟩
  | .fault error _ => ⟨.coreFault error, [], [], []⟩

def runWithReceipt (prepared : Prepared) (fuel : Nat := 10000000)
    (maxReturnBytes : Nat := 1048576) : Receipt :=
  resumeWithReceipt (.initial prepared.expression) fuel maxReturnBytes

def resume (state : Core.State) (fuel : Nat := 10000000) (maxReturnBytes : Nat := 1048576) : Outcome :=
  (resumeWithReceipt state fuel maxReturnBytes).outcome

def run (prepared : Prepared) (fuel : Nat := 10000000) (maxReturnBytes : Nat := 1048576) : Outcome :=
  resume (.initial prepared.expression) fuel maxReturnBytes

end Solcore.Frontend.RustHull.Contract
