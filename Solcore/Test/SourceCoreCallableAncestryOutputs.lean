import Solcore.Frontend.SourceCoreCompatibleOutputs
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCompatibleOutputs.Recipe.mk

/-! Cached compatible calls export global/builtin values at every data depth.
Core-only tampering keeps native typing while changing descriptors or closure
payloads; the reverse adapter must still reject it. Lambda export is an explicit
ledger boundary, independent of the typed native execution succeeding. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryOutputs
open Solcore Solcore.Frontend SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared := SourceCoreCallableAncestryPrograms.Prepared
abbrev Recipe := Solcore.Frontend.SourceCoreCompatibleOutputs.Recipe
abbrev SourceValue := SourceTypedRuntime.Value
abbrev Key := SourceSpecialization.SpecializationKey

private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Holder { Hold(function(Word) returns (Word)) }",
    "trait Marker<T> {}", "impl Marker<Word> {}",
    "function keep<T>(value: T) returns (T) where T: Marker { return value; }",
    "function inc(value: Word) returns (Word) { return value + 1; }",
    "function dec(value: Word) returns (Word) { return value - 1; }",
    "function getNamed() returns (function(Word) returns (Word)) { return inc; }",
    "function getBuiltin() returns (function(Word) returns (integer)) { return wordToInteger; }",
    "function getQualified() returns (function(Word) returns (Word)) { return keep; }",
    "function getNominal() returns (Holder) { return .Hold(inc); }",
    "function getTuple() returns (function(Word) returns (Word), function(Word) returns (integer)) { return (inc, wordToInteger); }",
    "function mappingReturn(value: mapping(function(Word) returns (Word) => function(Word) returns (Word))) returns (mapping(function(Word) returns (Word) => function(Word) returns (Word))) { return value; }",
    "function alias(value: mapping(@Word => function(Word) returns (Word))) returns (mapping(@Word => function(Word) returns (Word))) { return value; }",
    "function make(value: Word) returns (function(Word) returns (Word)) { return lam(delta: Word) -> Word { value = value + delta; return value; }; }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO Key := do
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"compatible output function missing: {name}")

private structure Projected (checked : Checked) (source : TypeSystem.Ty) (native : Core.Ty) : Type where
  eq : checked.catalog.project source = .ok native
private def project (checked : Checked) (source : TypeSystem.Ty) (native : Core.Ty) : IO (Projected checked source native) := do
  match projected : checked.catalog.project source with
  | .error error => throw (IO.userError s!"compatible output projection failed: {reprStr error}")
  | .ok actual =>
      if same : actual = native then pure ⟨by simpa only [same] using projected⟩
      else throw (IO.userError "compatible output actual native projection changed")

private def check {checked : Checked} (prepared : SourceCoreCallableAncestryPrograms.Prepared checked)
    (recipe : Solcore.Frontend.SourceCoreCompatibleOutputs.Recipe checked prepared.layouts.definitions)
    (owner : Key) (arguments : List SourceValue) (expected : SourceValue) : IO Unit := do
  for fuel in [0, 7, 37, 150000] do
    let completion ← match prepared.runSource owner arguments fuel with
      | .ok completion => pure (completion.resume 150000)
      | .error error => throw (IO.userError s!"marked output source run failed: {reprStr error}")
    let projection ← project checked completion.entry.sourceResultType completion.entry.native.resultType
    let exported ← match SourceCoreCompatibleOutputs.decodeSuccess recipe completion.result.context
        completion.result.contextOwner completion.entry.sourceResultType projection.eq completion.result.native with
      | .ok exported => pure exported
      | .error error => throw (IO.userError s!"marked output reverse failed: {reprStr error}")
    assertTrue (reprStr exported.decoded.source == reprStr expected)
      s!"marked output source metadata/order changed: {reprStr exported.decoded.source}"

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"ancestry output source rejected: {reprStr error}")
  let seeds := (program.signatures.functions.filter (·.name != "keep")).map fun signature =>
    (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program seeds 300 with
    | .ok (.complete plan) => pure plan | result => throw (IO.userError s!"ancestry output plan failed: {reprStr result}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 500 with
    | .ok automatic => pure automatic | .error error => throw (IO.userError s!"ancestry output base failed: {reprStr error}")
  let prepared ← match SourceCoreCallableAncestryPrograms.prepare automatic.prepared 500 with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"ancestry output factory failed: {reprStr error}")
  let recipe ← match SourceCoreCompatibleOutputs.prepareAncestry prepared with
    | .ok recipe => pure recipe | .error error => throw (IO.userError s!"ancestry output recipe failed: {reprStr error}")
  let inc ← key program "inc"
  let dec ← key program "dec"
  let named : SourceValue := .global inc []
  let getNamed ← key program "getNamed"
  let getBuiltin ← key program "getBuiltin"
  check prepared recipe getNamed [] named
  check prepared recipe getBuiltin [] (.builtin .wordToInteger)
  let qualified ← match prepared.base.functions.filter (fun function => function.specialized.assumptions != []) with
    | [function] => pure function
    | _ => throw (IO.userError "compatible qualified output specialization absent")
  let evidence ← match SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program qualified.signature.key
      qualified.specialized.assumptions with
    | .ok evidence => pure evidence | .error error => throw (IO.userError s!"compatible expected qualified evidence failed: {reprStr error}")
  assertTrue (!evidence.isEmpty) "compatible qualified output test lacked evidence"
  check prepared recipe (← key program "getQualified") [] (.global qualified.signature.key evidence)
  let holder ← match program.signatures.dataTypes.find? (·.name == "Holder") with
    | some holder => pure holder | none => throw (IO.userError "compatible output Holder absent")
  let constructor ← match holder.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "compatible output Hold absent")
  let functionType := TypeSystem.Ty.function .word .word
  let instantiation : DataConstructorInstantiation := ⟨constructor.id, [], [functionType], .nominal holder.id []⟩
  check prepared recipe (← key program "getNominal") [] (.constructed instantiation [named])
  check prepared recipe (← key program "getTuple") [] (.product named (.builtin .wordToInteger))
  let mapping : SourceValue := .mapping (.comptime functionType) functionType
    [(named, named), (named, .global dec [])]
  check prepared recipe (← key program "mappingReturn") [mapping] mapping
  let alias : SourceValue := .mapping (.proxy (.comptime .word)) (.comptime functionType)
    [(.proxy (.comptime .word), named), (.proxy .word, .global dec [])]
  check prepared recipe (← key program "alias") [alias] alias
  let made ← match prepared.runSource (← key program "make") [.word (w 3)] 150000 with
    | .ok made => pure made | .error error => throw (IO.userError s!"ancestry lambda run failed: {reprStr error}")
  let projection ← project automatic.checked made.entry.sourceResultType made.entry.native.resultType
  match SourceCoreCompatibleOutputs.decodeSuccess recipe made.result.context made.result.contextOwner
      made.entry.sourceResultType projection.eq made.result.native with
  | .error {code := .lambdaExportRequiresLedger (.lambda _ _ _), ..} => pure ()
  | .error error => throw (IO.userError s!"ancestry lambda ledger boundary changed: {reprStr error}")
  | .ok _ => throw (IO.userError "ancestry lambda exported without authentic capture ledger")
  IO.println "frame-aware source output ownership and deep raw callable metadata GREEN"

end Tests.SourceCoreCallableAncestryOutputs
