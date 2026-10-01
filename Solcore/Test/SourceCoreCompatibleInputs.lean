import Solcore.Frontend.SourceCoreCompatibleInputs
import Solcore.Frontend.SourceCoreCompatibleFunctions
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCompatibleInputs.encodeRaw

/-! Public validation precedes injection below cached, installed globals.
The fixtures compile source bodies once; invocations reuse the cached closures.
Only global/builtin source leaves pass the existing validator, even inside
nominal payloads, products and ordered mappings. Source heap export is separate. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleInputs
open Solcore Solcore.Frontend SourceInference
abbrev SourceValue := SourceTypedRuntime.Value
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared := SourceCoreCompatibleFunctions.Prepared

private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def assertTrue (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Holder { Hold(function(Word) returns (Word)) }",
    "function inc(value: Word) returns (Word) { return value + 1; }",
    "function consume(f: function(Word) returns (Word), value: Word) returns (Word) { return f(value); }",
    "function nominal(value: Holder, n: Word) returns (Word) { match (value) { case .Hold(f) { return f(n); } } }",
    "function product(value: (Word, function(Word) returns (Word))) returns (Word) { match (value) { case (n, f) { return f(n); } } }",
    "function table(values: mapping(Word => function(Word) returns (Word)), n: Word) returns (Word) { return values[7](n); }",
    "function keyTable(values: mapping(function(Word) returns (Word) => Word), f: function(Word) returns (Word)) returns (Word) { return values[f]; }",
    "function builtin(f: function(Word) returns (integer), n: Word) returns (integer) { return f(n); }",
    "function wideData(values: mapping(Word => Word)) returns (mapping(Word => Word)) { return values; }",
    "function alias(values: mapping(@Word => Word)) returns (mapping(@Word => Word)) { return values; }",
    "function outsider(value: Word) returns (Word) { return value; }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO Key := do
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"compatible input fixture missing: {name}")

example {context : Solcore.Frontend.SourceCoreCompatibleInputs.Context} {expected : List TypeSystem.Ty} {arguments : List SourceValue}
    {fuel : Nat} (encoded : Solcore.Frontend.SourceCoreCompatibleInputs.Encoded context expected arguments fuel) :
    Core.HasType context.coreContext encoded.expression (Core.LanguageResult.resultType encoded.type)
      context.definitions := encoded.typed

example {context : Solcore.Frontend.SourceCoreCompatibleInputs.Context} {expected : List TypeSystem.Ty} {arguments : List SourceValue}
    {fuel : Nat} (encoded : Solcore.Frontend.SourceCoreCompatibleInputs.Encoded context expected arguments fuel) :
    SourceTypedRuntime.validateInputs context.values.checked.signatures context.validationPlan
      fuel expected arguments = none := encoded.validated

private def inputContext {checked : Checked} (prepared : Prepared checked)
    (validationPlan : SourceSpecializationWorklist.Plan) : IO Solcore.Frontend.SourceCoreCompatibleInputs.Context := do
  match Solcore.Frontend.SourceCoreCompatibleInputs.prepare (SourceCoreCompatibleValues.Context.initial checked) prepared.plan prepared.globals
      (prepared.callableContext.map (·.table)) checked.catalog.definitions (w 900) (some validationPlan) with
  | .ok context => pure context
  | .error error => throw (IO.userError s!"compatible cached input context failed: {reprStr error}")

private def check {checked : Checked} (prepared : Prepared checked) (context : Solcore.Frontend.SourceCoreCompatibleInputs.Context)
    (owner : Key) (arguments : List SourceValue) (expected : Core.Value) (validationFuel : Nat := 256) : IO Unit := do
  let function ← match prepared.functions.find? (fun function => decide (function.signature.key = owner)) with
    | some found => pure found | none => throw (IO.userError "compatible input root absent")
  let encoded ← match Solcore.Frontend.SourceCoreCompatibleInputs.encode context (function.inputs.map (fun pair => pair.1.scheme.body)) arguments validationFuel with
    | .ok encoded => pure encoded | .error error => throw (IO.userError s!"compatible source input rejected: {reprStr error}")
  let body ← match SourceCoreGeneralFunctions.assembleCall prepared.globals prepared.functions prepared.closures
      owner ⟨encoded.type, encoded.expression⟩ with
    | .ok body => pure body | .error error => throw (IO.userError s!"compatible source call assembly failed: {reprStr error}")
  let program : Core.Program := ⟨Core.LanguageResult.resultType function.signature.resultType, body, context.definitions⟩
  assertTrue program.check "compatible expression injection failed actual closed Core checker"
  let native ← match SourceCoreGeneralEntry.NativeEntry.compile context.definitions [] function.signature.resultType body with
    | .ok native => pure native | .error error => throw (IO.userError s!"compatible input typed checkpoint check failed: {reprStr error}")
  let checkpoint ← match native.start [] with
    | .ok checkpoint => pure checkpoint | .error error => throw (IO.userError s!"compatible input typed checkpoint start failed: {reprStr error}")
  for fuel in [0, 7, 37, 150000] do
    let result := checkpoint.resume fuel
    let result := match result.checkpoint? with
      | some next => next.resume 150000
      | none => result
    match result.observation with
    | .succeeded value store =>
        assertTrue (value == expected) s!"compatible source input result changed: {reprStr value}"
        assertTrue (prepared.globals.length ≤ store.length) "compatible globals world shrank"
    | observation => throw (IO.userError s!"compatible source input execution failed: {reprStr observation}")

private def sameRejection (context : Solcore.Frontend.SourceCoreCompatibleInputs.Context) (expected : List TypeSystem.Ty)
    (arguments : List SourceValue) (validationFuel : Nat := 256) : IO Unit := do
  let old := SourceTypedRuntime.validateInputs context.values.checked.signatures context.validationPlan
    validationFuel expected arguments
  match old, Solcore.Frontend.SourceCoreCompatibleInputs.encode context expected arguments validationFuel with
  | some old, .error (.source actual) =>
      assertTrue (reprStr old == reprStr actual) s!"compatible input error/order changed: {reprStr actual}"
  | _, _ => throw (IO.userError "compatible input rejection did not preserve pure public validator")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok checked => pure checked | .error error => throw (IO.userError s!"compatible input source rejected: {reprStr error}")
  let roots := (program.signatures.functions.filter (·.name != "outsider")).map (fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request))
  let original ← match SourceSpecializationWorklist.run program roots 300 with
    | .ok (.complete plan) => pure plan | result => throw (IO.userError s!"compatible input plan failed: {reprStr result}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program original 500 with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"compatible input cached factory failed: {reprStr error}")
  let prepared := automatic.prepared
  let context ← inputContext prepared original
  let inc ← key program "inc"
  let named : SourceValue := .global inc []
  let functionType := TypeSystem.Ty.function .word .word
  let consume ← key program "consume"
  check prepared context consume [named, .word (w 8)] (.word (w 9))
  let holder ← match program.signatures.dataTypes.find? (·.name == "Holder") with
    | some holder => pure holder | none => throw (IO.userError "compatible input Holder absent")
  let constructor ← match holder.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "compatible input Hold absent")
  let instantiation : DataConstructorInstantiation := ⟨constructor.id, [], [functionType], .nominal holder.id []⟩
  check prepared context (← key program "nominal") [.constructed instantiation [named], .word (w 8)] (.word (w 9))
  check prepared context (← key program "product") [.product (.word (w 8)) named] (.word (w 9))
  check prepared context (← key program "table")
    [.mapping .word functionType [(.word (w 7), named)], .word (w 8)] (.word (w 9))
  check prepared context (← key program "table")
    [.mapping (.comptime .word) (.comptime functionType) [(.word (w 7), named)], .word (w 8)] (.word (w 9))
  check prepared context (← key program "keyTable")
    [.mapping functionType .word [(named, .word (w 12)), (named, .word (w 19))], named] (.word (w 12))
  check prepared context (← key program "builtin") [.builtin .wordToInteger, .word (w 15)] (.integer 15)
  let incBody ← match original.specializations.find? (fun specialized => decide (specialized.key = inc)) with
    | some specialized => pure specialized.function.typedBody | none => throw (IO.userError "compatible inc body absent")
  let raw : SourceValue := .closure incBody.inputs .word
    (incBody.roots.filterMap fun | .statement id => some id | _ => none) incBody inc [] []
  sameRejection context [functionType] [raw]
  sameRejection context [functionType] [.instantiated [] [] named]
  sameRejection context [.product .word functionType] [.product (.word (w 8)) raw]
  sameRejection context [.mapping .word functionType] [.mapping .word functionType [(.word (w 7), raw)]]
  sameRejection context [.nominal holder.id []] [.constructed instantiation [raw]]
  sameRejection context [functionType] [.global (← key program "outsider") []]
  sameRejection context [functionType] [.global consume []]
  sameRejection context [functionType] [.builtin .wordToInteger]
  sameRejection context [.word, functionType] [.bool true, named, .unit]
  sameRejection context [functionType, .word] [named]
  sameRejection context [functionType] [named] 0
  sameRejection context [.word] [.word (w 1)] 0
  sameRejection context [.nominal holder.id []]
    [.constructed {instantiation with payloadTypes := [.bool]} [.bool true]]
  let entries := (List.range 100).map (fun index => (.word (w index), .word (w (index + 1))))
  let dataRoot ← key program "wideData"
  let dataFunction ← match prepared.functions.find? (fun function => decide (function.signature.key = dataRoot)) with
    | some found => pure found | none => throw (IO.userError "compatible wide input function absent")
  let wide ← match Solcore.Frontend.SourceCoreCompatibleInputs.encode context [TypeSystem.Ty.mapping .word .word] [.mapping .word .word entries] 2 with
    | .ok encoded => pure encoded | .error error => throw (IO.userError s!"accepted wide input ran out of encoding budget: {reprStr error}")
  assertTrue (wide.type == dataFunction.signature.parameterType) "compatible wide input projected type changed"
  let ordinary : SourceCoreCompatibleValues.Value := .mapping .word .word
    ((List.range 100).map (fun index => (.word (w index), .word (w (index + 1)))))
  let dataEncoded ← match SourceCoreCompatibleValues.encode 500 context.values (.mapping .word .word) ordinary with
    | .ok encoded => pure encoded | .error error => throw (IO.userError s!"compatible expected wide data encode failed: {reprStr error}")
  check prepared context dataRoot [.mapping .word .word entries] dataEncoded.value 2
  let aliasRaw : SourceCoreCompatibleValues.Value := .mapping (.proxy (.comptime .word)) (.comptime .word)
    [(.proxy (.comptime .word), .word (w 4)), (.proxy .word, .word (w 7))]
  let aliasEncoded ← match SourceCoreCompatibleValues.encode 500 context.values
      (.mapping (.proxy .word) .word) aliasRaw with
    | .ok encoded => pure encoded | .error error => throw (IO.userError s!"compatible raw input expected encode failed: {reprStr error}")
  check prepared context (← key program "alias")
    [.mapping (.proxy (.comptime .word)) (.comptime .word)
      [(.proxy (.comptime .word), .word (w 4)), (.proxy .word, .word (w 7))]] aliasEncoded.value
  match Solcore.Frontend.SourceCoreCompatibleInputs.prepare context.values prepared.plan prepared.globals.reverse (prepared.callableContext.map (·.table)) context.definitions with
  | .error .globalsOrderMismatch => pure ()
  | _ => throw (IO.userError "compatible input accepted foreign slot ordering")
  match Solcore.Frontend.SourceCoreCompatibleInputs.prepare context.values prepared.plan prepared.globals none context.definitions with
  | .error (.missingContract _) => pure ()
  | _ => throw (IO.userError "compatible input lost actual staged descriptor ownership")
  match Solcore.Frontend.SourceCoreCompatibleInputs.prepare context.values prepared.plan
      (prepared.globals.map (fun signature => {signature with resultType := .unit}))
      (prepared.callableContext.map (·.table)) context.definitions with
  | .error (.globalTypeMismatch _) => pure ()
  | _ => throw (IO.userError "compatible input accepted altered cached signatures")
  let ambient ← match Solcore.Frontend.SourceCoreCompatibleInputs.prepare context.values prepared.plan prepared.globals
      (prepared.callableContext.map (·.table)) (context.definitions ++ [⟨[.unit]⟩]) (w 900) (some original) with
    | .ok context => pure context | .error error => throw (IO.userError s!"compatible ambient context failed: {reprStr error}")
  check prepared ambient consume [named, .word (w 8)] (.word (w 9))
  let extendedPlan ← match SourceSpecializationWorklist.run program
      ((program.signatures.functions.map (fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)))) 300 with
    | .ok (.complete plan) => pure plan | result => throw (IO.userError s!"compatible extended plan failed: {reprStr result}")
  let extended ← match SourceCoreCompatibleFunctions.prepare program extendedPlan 500 with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"compatible extended cached factory failed: {reprStr error}")
  let retained ← inputContext extended.prepared original
  let outsider : SourceValue := .global (← key program "outsider") []
  sameRejection retained [functionType] [outsider]
  assertTrue (SourceTypedRuntime.validateInputs retained.values.checked.signatures extendedPlan 256 [functionType] [outsider]).isNone
    "compatible extended-plan fixture did not distinguish original public admission"
  IO.println "compatible public source function inputs, deep carriers, exact validation and cached/resumed Core GREEN"

end Tests.SourceCoreCompatibleInputs
