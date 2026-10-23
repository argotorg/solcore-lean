import Solcore.Frontend.RustHull.Lowering

/-! Execute a selected Hull runtime object on Core with byte calldata and
contract-local storage. Deployment, account transactions and external calls
remain separate from this runtime-object boundary. -/
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
  deriving Repr

def snapshotType : Core.Ty :=
  bundleType [.word, .word, .word, Core.WordMapping.type, Core.WordMapping.type]

def resultType : Core.Ty := .product (Core.LanguageResult.resultType .unit) snapshotType

structure Prepared where
  expression : Core.Expr
  context : Context
  deriving Repr

/-- One checked runtime object, reusable across independent call contexts. -/
structure CompiledObject where
  expression : Core.Expr
  deriving Repr

def contextType : Core.Ty :=
  bundleType [Core.WordMapping.type, .word, Core.WordMapping.type, .word, .word, .word, .sum .unit .word]

private def select : List Object → List String → LowerM CodeBlock
  | _, [] => fail "an explicit Hull object path is required"
  | objects, name :: rest =>
      let candidates := objects.filter fun (.object candidate _ _ _) => candidate == name
      match candidates with
      | [.object _ code children _] => if rest.isEmpty then pure code else select children rest
      | [] => fail s!"unknown Hull object: {name}"
      | _ => fail s!"ambiguous Hull object: {name}"

private def calldataEntries (bytes : List UInt8) : Core.WordMapping.Entries :=
  Memory.packBytes bytes

private def initializer (context : Core.Expr) (code : Option (List UInt8)) (name : String) : Core.Expr :=
  match name with
  | "memory" | "transient" | "returnData" => Core.WordMapping.empty
  | "calldata" => projectArgument 0 7 context
  | "calldataSize" => projectArgument 1 7 context
  | "storage" => projectArgument 2 7 context
  | "callvalue" => projectArgument 3 7 context
  | "caller" => projectArgument 4 7 context
  | "address" => projectArgument 5 7 context
  | "availableGas" => projectArgument 6 7 context
  | "code" => Core.WordMapping.literal (calldataEntries (code.getD []))
  | "codeSize" => .word (Core.Word.ofNatModulo (code.getD []).length)
  | _ => .word Core.Word.zero

def compileObject (program : Program) (objectPath : List String)
    (fuel : Nat := 4096) (codeBytes : Option (List UInt8) := none) : LowerM CompiledObject := do
  let code ← select program.objects objectPath
  let entry := "$lean$object$entry"
  if (program.functions ++ code.functions).any (·.name == entry) then
    fail "reserved runtime entry name"
  let function : Function := {name := entry, args := [], ret := .unit, body := code.stmts}
  let slots := Effects.slots ++ (if codeBytes.isSome then Effects.codeSlots else [])
  let runtime : Scope := slots.reverse.map fun (name, type) =>
    ⟨some (Effects.slotName name), type, false⟩
  let (_, body) ← assemble (program.functions ++ code.functions ++ [function]) entry runtime fuel
  let scope := runtime.temporary (Core.LanguageResult.resultType .unit)
  let snapshot ← [("exit", Core.Ty.word), ("returnOffset", .word), ("returnSize", .word),
      ("memory", Core.WordMapping.type), ("storage", Core.WordMapping.type)].mapM fun (name, type) => do
    return Core.Expr.loadCell (← Effects.reference scope name type)
  let completed := Core.Expr.letE body (.pair (.var 0) (bundle snapshot))
  let allocated := slots.zipIdx.foldr (fun ((name, type), index) body =>
    Core.Expr.letE (.newCell type (initializer (.var (index + 1)) codeBytes name)) body) completed
  let expression := Core.Expr.lambda contextType resultType (.letE .unit allocated)
  let type ← (Core.inferDetailed [] [] expression Memory.definitions).mapError fun error =>
    ⟨s!"Core runtime object validation: {reprStr error}", none⟩
  expectType (.function contextType resultType) type
  pure ⟨expression⟩

def CompiledObject.instantiate (compiled : CompiledObject) (context : Context := {}) : Prepared :=
  let availableGas := match context.availableGas with
    | none => Core.Expr.inLeft .word .unit
    | some gas => .inRight .unit (.word gas)
  let argument := bundle [Core.WordMapping.literal (calldataEntries context.calldata),
    .word (Core.Word.ofNatModulo context.calldata.length), Core.WordMapping.literal context.storage,
    .word context.value, .word context.caller, .word context.address, availableGas]
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

private def finish (maxReturnBytes : Nat) (result : Core.Value) : Outcome := Id.run do
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

def resume (state : Core.State) (fuel : Nat := 10000000) (maxReturnBytes : Nat := 1048576) : Outcome :=
  match Core.runStateful fuel state with
  | .done value _ => finish maxReturnBytes value
  | .outOfFuel state => .outOfFuel state
  | .fault error _ => .coreFault error

def run (prepared : Prepared) (fuel : Nat := 10000000) (maxReturnBytes : Nat := 1048576) : Outcome :=
  resume (.initial prepared.expression) fuel maxReturnBytes

end Solcore.Frontend.RustHull.Contract
