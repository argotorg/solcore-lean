import Solcore.SourceSemantics.CoreLowering.CompatibleMappingVirtualRoot
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Real checked assignment metadata reaches describe's literal generator.
The root stays absent while virtual defaults and generated helpers execute. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleMappingVirtualRoot
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open CompatiblePayload CompatibleEquality CompatibleMapping CompatibleMapping.VirtualRoot

private def w (value : Nat) : Word := Word.ofNatModulo value
private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Item(Word) }",
    "function scalar() returns (Word) { let table: mapping(Word => Word); table[1] = 7; return 0; }",
    "function nested() returns (Word) { let table: mapping(Word => mapping(Word => @Word)); let other: mapping(Word => @Word); table[1] = other; return 0; }",
    "function missing() returns (Word) { let table: mapping(Word => Box); table[1] = .Item(7); return 0; }"
  ]}] }
private def sourceFor (program : CheckedProgram) (name : String) : IO TypedSource := do
  let signature ← match program.signatures.functions.find? (·.name == name) with
    | some signature => pure signature | none => throw (IO.userError "virtual-root function missing")
  match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 100 with
  | .ok (.complete plan) => match plan.specializations with
    | [specialized] => pure specialized.function.typedBody
    | _ => throw (IO.userError "virtual-root specialization count changed")
  | other => throw (IO.userError s!"virtual-root specialization failed: {reprStr other}")
private def assignmentFor (source : TypedSource) : IO (StatementNode × AssignmentResolution) :=
  match source.nodes.filterMap (fun
    | .statement node => match node.form with | .assignValue assignment _ _ => some (node, assignment) | _ => none
    | _ => none) with
  | [assignment] => pure assignment
  | _ => throw (IO.userError "virtual-root assignment count changed")
private def encode (context : SourceCoreCompatibleValues.Context) (type : TypeSystem.Ty) (value : SourceCoreDataValues.Value) :
    IO (SourceCoreCompatibleValues.Encoded 500 context type value) :=
  match SourceCoreCompatibleValues.encode 500 context type value with
  | .ok encoded => pure encoded | .error error => throw (IO.userError s!"virtual-root encode failed: {reprStr error}")
private def decode (context : SourceCoreCompatibleValues.Context) (type : TypeSystem.Ty) (value : Value) (expected : SourceCoreDataValues.Value) : IO Unit :=
  match SourceCoreCompatibleValues.decode 500 context type value with
  | .ok decoded => assertTrue (decoded == expected) "virtual-root raw/default value changed"
  | .error error => throw (IO.userError s!"virtual-root decode failed: {reprStr error}")
private def completed (code : Expr) (environment : Environment) (before : Store) : IO (Value × Store) := do
  let result ← match runStateful 200000 (.initial code environment before) with
    | .done value store => pure (value, store)
    | other => throw (IO.userError s!"virtual-root run failed: {reprStr other}")
  assertTrue (result.2.take before.length == before) "virtual-root materialized the absent source cell"
  match runStateful 1 (.initial code environment before) with
  | .outOfFuel checkpoint =>
    match runStateful 200000 checkpoint with
    | .done value store => assertTrue (value == result.1 && store == result.2) "virtual-root resume changed result"
    | _ => throw (IO.userError "virtual-root resume failed")
  | _ => throw (IO.userError "virtual-root fixture omitted checkpoint")
  pure result

private def exercise (initial : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (expectedRead : Option SourceCoreDataValues.Value) (replacement : SourceCoreDataValues.Value) : IO Unit := do
  let (node, assignment) ← assignmentFor source
  match binding : SourceCoreCompatibleDataPlaces.rootBinder source assignment.target.root with
  | .error error => throw (IO.userError s!"virtual-root binder failed: {reprStr error}")
  | .ok binder =>
    match declared : binder.scheme.body with
    | .mapping key value =>
      let empty ← encode initial (.mapping key value) (.mapping key value [])
      let context := empty.context
      match described : SourceCoreCompatibleDataPlaces.describe context context.checked.signatures source (.occurrence node.id.occurrence) assignment with
      | .error error => throw (IO.userError s!"virtual-root describe failed: {reprStr error}")
      | .ok route =>
        have receipt := generated_of_describe binding declared described
        let absent := Value.inLeft route.rootType .unit
        let before := [absent, Value.integer (-123)]
        let prepared ← match SourceCoreCompatibleDataPlaces.prepare context 200 route (w 900) (fun _ => w 1000) with
          | .ok prepared => pure prepared | .error error => throw (IO.userError s!"virtual-root prepare failed: {reprStr error}")
        -- The proof consumer takes the actual describe equation; no literal
        -- evaluation or alternative default implementation is supplied.
        have _normalizes := generated_normalizes (prepared := ⟨route, [], [], w 900⟩) receipt
          (noFunctions context.checked.catalog) [] [] [absent] before (.var 0) (.var rfl)
        let normalization := SourceCoreCompatibleDataPlaces.normalizeRoot prepared (.var 0)
        assertTrue (infer? [OptionalCell.cellType route.rootType] normalization context.checked.catalog.definitions == some (OptionalCell.cellType route.rootType)) "virtual-root normalization checker failed"
        let (normalized, sameStore) ← completed normalization [absent] before
        assertTrue (sameStore == before) "normalization allocated or wrote a cell"
        match normalized with
        | .inRight .unit raw => decode context (.mapping key value) raw (.mapping key value [])
        | _ => throw (IO.userError "normalization left mapping absent")
        let header ← match empty.value with
          | .pair (.word header) _ => pure header | _ => throw (IO.userError "virtual-root raw header missing")
        assertTrue (context.registry.lookup header == some (.mapping key value)) "virtual-root header metadata changed"
        let replacementSource := replacement
        let replacement ← encode context value replacement
        let getter := SourceCoreCompatibleDataPlaces.getter prepared .word
        let setter := SourceCoreCompatibleDataPlaces.setter prepared .word
        assertTrue (infer? [] getter context.checked.catalog.definitions == some (.function (.product (OptionalCell.cellType route.rootType) .word) (LanguageResult.resultType prepared.optionalLeaf))) "virtual-root getter checker failed"
        assertTrue (infer? [] setter context.checked.catalog.definitions == some (.function (.product (OptionalCell.cellType route.rootType) (.product .word route.leafType)) (LanguageResult.resultType route.rootType))) "virtual-root setter checker failed"
        let (read, readStore) ← completed (.apply getter (.var 0)) [.pair absent (.word (w 1))] before
        assertTrue (readStore.length == before.length + context.checked.catalog.entries.length + 1) "virtual-root getter administrative count changed"
        match expectedRead, read with
        | some expected, .inRight .word (.inRight .unit selected) => decode context value selected expected
        | none, .inLeft _ (.word token) => assertTrue (token == (w 1000).add header) "virtual-root missing-default token changed"
        | _, _ => throw (IO.userError "virtual-root getter result mismatch")
        let (updated, updateStore) ← completed (.apply setter (.var 0)) [.pair absent (.pair (.word (w 1)) replacement.value)] before
        match expectedRead, updated with
        | some _, .inRight .word raw =>
          match SourceCoreCompatibleValues.decode 500 replacement.context (.mapping key value) raw with
          | .ok (.mapping actualKey actualValue entries) =>
            assertTrue (actualKey == key && actualValue == value && entries == [(.word (w 1), replacementSource)]) "virtual-root setter changed raw metadata or replacement"
          | _ => throw (IO.userError "virtual-root setter carrier invalid")
          assertTrue (updateStore.length == before.length + 2 * (context.checked.catalog.entries.length + 1)) "virtual-root setter administrative count changed"
        | none, .inLeft _ (.word token) =>
          assertTrue (token == (w 1000).add header) "virtual-root setter missing-default token changed"
          assertTrue (updateStore.length == before.length + context.checked.catalog.entries.length + 1) "virtual-root setter inserted after missing-default"
        | _, _ => throw (IO.userError "virtual-root setter result mismatch")
    | _ => throw (IO.userError "virtual-root fixture binder stopped being bare mapping")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"virtual-root source rejected: {reprStr error}")
  let box ← match program.signatures.dataTypes.find? (·.name == "Box") with
    | some box => pure box | none => throw (IO.userError "virtual-root Box missing")
  let constructor ← match box.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "virtual-root constructor missing")
  let boxType := TypeSystem.Ty.nominal box.id []
  let item : DataConstructorInstantiation := ⟨constructor.id, [], [.word], boxType⟩
  let nested := TypeSystem.Ty.mapping .word (.proxy .word)
  let checked ← match SourceCoreCompatibleCatalog.prepare program.signatures 300 [.mapping .word .word, .mapping .word nested, .mapping .word boxType] with
    | .ok checked => pure checked | .error error => throw (IO.userError s!"virtual-root catalog rejected: {reprStr error}")
  let context := SourceCoreCompatibleValues.Context.initial checked
  exercise context (← sourceFor program "scalar") (some (.word Word.zero)) (.word (w 7))
  exercise context (← sourceFor program "nested") (some (.mapping .word (.proxy .word) [])) (.mapping .word (.proxy .word) [])
  exercise context (← sourceFor program "missing") none (.constructed item [.word (w 7)])
  IO.println "compatible mapping virtual-root proofs GREEN"

end Tests.SourceCoreCompatibleMappingVirtualRoot
