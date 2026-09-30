import Solcore.Frontend.SourceCoreDataMatches
import Solcore.Frontend.SourceCoreGeneralEntry
import Solcore.Frontend.SourceCoreLoops

#check_failure Solcore.Frontend.SourceTypedRuntime.run

set_option autoImplicit false
namespace Tests.SourceCoreDataMatches
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.Frontend.SourceCoreGeneralEntry

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def w (value : Nat) : Word := Word.ofNatModulo value
private def present (value : Value) : Value := .inRight .unit value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Tree { Leaf(Word), Pair(Tree, Tree) }",
    "function choose(tree: Tree) returns (Word) {",
    "  match (tree) {",
    "    case .Pair(.Leaf(left), .Leaf(0)) { return left; }",
    "    case .Pair(.Leaf(left), .Leaf(right)) { left = left + right; return left; }",
    "    case .Leaf(value) { return value; }",
    "    default { return 99; }",
    "  }",
    "}",
    "function tuple(value: (Tree, (Bool, Word))) returns (Word) {",
    "  match (value) {",
    "    case (.Leaf(left), (flag, right)) { return flag ? left + right : right; }",
    "    default { return 99; }",
    "  }",
    "}",
    "function integerCase(value: integer) returns (integer) {",
    "  match (value) { case 0 { return 5; } case (1) { return 6; } case other { return other; } }",
    "}",
    "function wildcard(value: Word) returns (Word) {",
    "  match (value) { case _ { return 3; } default { let absent: Word; return absent; } }",
    "}",
    "function unitCase(value: Unit) returns (Word) { match (value) { case () { return 7; } } }",
    "function nestedFailure(value: Tree) returns (Word) {",
    "  match (value) { case .Leaf(bound) { let absent: Word; return absent; } default { return 8; } }",
    "}",
    "function none(value: Word) returns (Unit) { match (value) { case 0 { return; } default {} } }",
    "function once(value: Tree, marker: Word) returns (Word) {",
    "  match ((lam() -> Tree { marker = marker + 1; return value; })()) {",
    "    case .Leaf(bound) { return marker + bound; } default { return marker; }",
    "  }",
    "}",
    "function scrutineeFailure(value: Tree) returns (Word) {",
    "  match ((lam() -> Tree { let missing: Tree; return missing; })()) {",
    "    case .Leaf(bound) { return bound; } default { return 9; }",
    "  }",
    "}",
    "function functionBinder(marker: Word) returns (Word) {",
    "  match (lam(x: Word) -> Word { marker = marker + x; return marker; }) {",
    "    case f { let first: Word = f(2); return f(3); }",
    "  }",
    "}",
    "function moduloPattern(value: Word) returns (Word) {",
    "  match (value) { case 115792089237316195423570985008687907853269984665640564039457584007913129639936 { return 1; } default { return 2; } }",
    "}"
  ] }]
}

private def request (program : CheckedProgram) (name : String) : IO SourceSpecializationWorklist.Request :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure { declaration := signature.id, parameterSubstitution := [] }
  | _ => throw (IO.userError s!"match function missing: {name}")

private def planFor (program : CheckedProgram) (name : String) : IO Plan := do
  let selected ← request program name
  match SourceSpecializationWorklist.run program [selected] 100 with
  | .ok (.complete plan) => pure plan
  | result => throw (IO.userError s!"match worklist failed: {reprStr result}")

private def rootMatch (source : TypedSource) : Except SourceCoreBasic.Error (StatementId × StatementNode × MatchResolution) := do
  let [.statement root] := source.roots | throw (.missingReturn .unit)
  let node ← match source.lookupStatement? root with
    | some node => pure node
    | none => throw (.missingStatement root)
  match node.form with
  | .matchWith resolution => pure (root, node, resolution)
  | _ => throw (.unsupportedStatement root node.form)

private def flowPolicy (checked : Checked) (expression : SourceCoreFunctions.ExpressionLowerer) : SourceCoreLoops.Policy := {
  lowerExpression := expression
  readStatement := SourceCoreGeneralTypes.readStatement checked
  lowerBinder := SourceCoreGeneralTypes.lowerBinder checked
  lowerAssignment := SourceCoreGeneralTypes.lowerAssignment checked
}

private def lambdaBody (checked : Checked) : SourceCoreFunctions.BodyLowerer :=
  fun expression fuel source scope statements result reasonAt fellThrough escaped =>
    SourceCoreLoops.lowerStatementsWithPolicy (flowPolicy checked expression)
      fuel source scope statements result reasonAt fellThrough escaped

private def lowering (program : CheckedProgram) (checked : Checked) : BodyLowerer checked SourceCoreBasic.Error :=
  fun fuel request => do
    let source := request.specialized.function.typedBody
    let (id, _, resolution) ← rootMatch source
    let table ← (SourceCoreFaultSites.prepare source request.sourceResultType).mapError
      (fun _ => SourceCoreBasic.Error.missingReturn request.result.type)
    let context : SourceCoreCalls.Context := {
      plan := request.plan, owner := request.specialized.key, globals := [], administrativePrefix := 0,
      solvedRequirements := request.specialized.function.solvedRequirements, internalReason := w 250
    }
    let expression : SourceCoreFunctions.ExpressionLowerer := fun budget source scope id reasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy (SourceCoreGeneralTypes.policy checked program.signatures)
        (lambdaBody checked) budget context source scope id reasonAt
    let nested : SourceCoreDataMatches.BodyLowerer := fun fuel source scope statements result reasonAt escaped =>
      SourceCoreLoops.lowerFlowStatementsWithPolicy (flowPolicy checked expression)
        fuel source scope statements result reasonAt false escaped
    let compiled ← SourceCoreDataMatches.lowerChecked
      ⟨checked, program.signatures, request.specialized.function.solvedRequirements⟩ expression nested fuel source
      (inputScope request.inputs) (inputContext request.inputs) id resolution request.result.type table.reasonAt (w 250)
    let fallback := if request.result.type = .unit then LanguageResult.success .unit
      else LanguageResult.failure request.result.type (.word Word.zero)
    pure ⟨LocalControl.finish request.result.type (LocalLoop.toControl request.result.type compiled.expression (w 251)) fallback, table⟩

private def entryFor (program : CheckedProgram) (checked : Checked) (name : String) : IO (Entry checked) := do
  let plan ← planFor program name
  match prepare program plan checked 100 (lowering program checked) with
  | .ok prepared => match prepared.entries with
      | [entry] => pure entry
      | _ => throw (IO.userError "match seed mismatch")
  | .error error => throw (IO.userError s!"match compile {name} failed: {reprStr error}")

private def execute {checked : Checked} (entry : Entry checked) (arguments : List Value) : IO LanguageResult.Observation :=
  match entry.run arguments 100000 with
  | .ok result => pure result.observation
  | .error error => throw (IO.userError s!"match inputs failed: {reprStr error}")

private def rejected {α : Type} : Except SourceCoreBasic.Error α → Bool
  | .error _ => true
  | .ok _ => false

private def metadataTests (program : CheckedProgram) (checked : Checked) : IO Unit := do
  let plan ← planFor program "choose"
  let specialized ← match plan.specializations with
    | [specialized] => pure specialized
    | _ => throw (IO.userError "choose specialization mismatch")
  let source := specialized.function.typedBody
  let (id, node, resolution) ← match rootMatch source with
    | .ok root => pure root
    | .error error => throw (IO.userError s!"match root failed: {reprStr error}")
  let first ← match resolution.cases[0]? with
    | some arm => pure arm
    | none => throw (IO.userError "literal constructor arm missing")
  let second ← match resolution.cases[1]? with
    | some arm => pure arm
    | none => throw (IO.userError "binder constructor arm missing")
  let context : SourceCoreDataMatches.Context := ⟨checked, program.signatures, specialized.function.solvedRequirements⟩
  let scope ← source.inputs.foldlM (fun scope binder => do
    match SourceCoreGeneralTypes.lowerBinder checked source scope binder with
    | .ok type => pure ((binder.id, type) :: scope)
    | .error error => throw (IO.userError s!"match input scope: {reprStr error}")) []
  let scope := (resolution.hiddenScrutinee, (checked.catalog.project first.pattern.type).toOption.getD .unit) :: scope
  let compile := fun (pattern : TypedMatchPattern) => SourceCoreDataMatches.compilePattern context 100 source scope
    id node.span first.pattern.type pattern
  assertTrue (!rejected (compile first.pattern)) "valid pattern metadata rejected"
  assertTrue (rejected (SourceCoreDataMatches.compilePattern context 0 source scope id node.span
    first.pattern.type first.pattern)) "zero pattern compile fuel accepted"
  let .constructor constructor instructions := first.pattern.resolution
    | throw (IO.userError "constructor resolution missing")
  assertTrue (rejected (compile {first.pattern with requirements := []})) "detached pattern requirements accepted"
  assertTrue (rejected (compile {first.pattern with type := .word})) "wrong pattern result type accepted"
  let wrongPayload := {constructor with payloadTypes := []}
  let wrongIdentity := {constructor with constructor := {constructor.constructor with constructorIndex := 999}}
  assertTrue (rejected (compile {first.pattern with resolution := .constructor wrongPayload instructions}))
    "forged constructor payload metadata accepted"
  assertTrue (rejected (compile {first.pattern with resolution := .constructor wrongIdentity instructions}))
    "forged constructor identity accepted"
  assertTrue (rejected (compile {first.pattern with resolution := .constructor constructor (instructions ++ [.wildcard])}))
    "unconsumed pattern instruction accepted"
  let .constructor span dot qualifiers name count := first.pattern.source
    | throw (IO.userError "constructor source root missing")
  assertTrue (rejected (compile {first.pattern with source := .constructor span dot qualifiers name (count + 1)}))
    "wrong retained root arity accepted"
  assertTrue (rejected (compile {first.pattern with source := .constructor span dot qualifiers "Forged" count}))
    "wrong constructor source spelling accepted"
  let changedLiteral := instructions.map fun
    | .integerLiteral raw literal => .integerLiteral raw {literal with rawValue := literal.rawValue + 1}
    | instruction => instruction
  assertTrue (rejected (compile {first.pattern with resolution := .constructor constructor changedLiteral}))
    "literal raw value mismatch accepted"
  let noEvidence := {context with solvedRequirements := []}
  assertTrue (rejected (SourceCoreDataMatches.compilePattern noEvidence 100 source scope id node.span
    first.pattern.type first.pattern)) "unproved literal pattern accepted"
  let .constructor secondConstructor secondInstructions := second.pattern.resolution
    | throw (IO.userError "second constructor pattern missing")
  let binders := secondInstructions.filterMap fun | .binder binder => some binder | _ => none
  let [left, right] := binders | throw (IO.userError "nested binders missing")
  let changeRight := fun (replacement : TypedBinder) =>
    let instructions := secondInstructions.map fun
      | .binder binder => .binder (if binder.id = right.id then replacement else binder)
      | instruction => instruction
    {second.pattern with resolution := .constructor secondConstructor instructions}
  assertTrue (rejected (compile (changeRight {right with id := left.id}))) "duplicate binder identity accepted"
  assertTrue (rejected (compile (changeRight {right with name := left.name}))) "duplicate binder name accepted"
  assertTrue (rejected (compile (changeRight {right with id := resolution.hiddenScrutinee}))) "hidden-cell alias accepted"
  assertTrue (rejected (compile (changeRight {right with comptime := true}))) "comptime pattern binding accepted"
  assertTrue (rejected (compile (changeRight {right with scheme := .mono .bool}))) "wrong binder source type accepted"
  let tuplePlan ← planFor program "tuple"
  let tupleFunction ← match tuplePlan.specializations with
    | [specialized] => pure specialized.function
    | _ => throw (IO.userError "tuple specialization mismatch")
  let (tupleId, tupleNode, tupleResolution) ← match rootMatch tupleFunction.typedBody with
    | .ok root => pure root
    | .error error => throw (IO.userError s!"tuple root failed: {reprStr error}")
  let [tupleArm] := tupleResolution.cases | throw (IO.userError "tuple arm missing")
  let tupleContext : SourceCoreDataMatches.Context := ⟨checked, program.signatures, tupleFunction.solvedRequirements⟩
  let plain ← match SourceCoreDataMatches.compilePattern tupleContext 100 tupleFunction.typedBody []
      tupleId tupleNode.span tupleArm.pattern.type tupleArm.pattern with
    | .ok compiled => pure compiled
    | .error error => throw (IO.userError s!"plain tuple pattern failed: {reprStr error}")
  let grouped ← match SourceCoreDataMatches.compilePattern tupleContext 100 tupleFunction.typedBody []
      tupleId tupleNode.span tupleArm.pattern.type
      {tupleArm.pattern with source := .group tupleNode.span (.group tupleNode.span tupleArm.pattern.source)} with
    | .ok compiled => pure compiled
    | .error error => throw (IO.userError s!"grouped tuple pattern failed: {reprStr error}")
  assertTrue (grouped.pattern.matcher == plain.pattern.matcher && grouped.pattern.bindings == plain.pattern.bindings)
    "tuple grouping changed its generated matcher or binder order"

example {context : SourceCoreDataMatches.Context} {environment : Core.Context} {type : Ty}
    (compiled : SourceCoreDataMatches.Certified context environment type) :
    HasType environment compiled.expression (LocalLoop.resultType type) context.checked.catalog.definitions := compiled.typed

example {definitions : DataEnvironment} (pattern : SourceCoreDataMatches.CertifiedPattern definitions) :
    HasType [] pattern.pattern.matcher pattern.pattern.functionType definitions := pattern.typed

/-- A binder matcher is pure even when its value contains shared cells. -/
example (environment : Environment) (store : Store) (type : Ty) (location : Location) :
    Evaluates (.cellRef type location :: environment) store
      (.apply (.lambda (.cell type) (.sum .unit (.cell type)) (.inRight .unit (.var 0))) (.var 0))
      (.inRight .unit (.cellRef type location)) store :=
  SourceCoreDataMatches.binder_evaluates environment store (.cell type) (.cellRef type location)

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"match source rejected: {reprStr errors}")
  let tree ← match program.signatures.dataTypes.find? (·.name == "Tree") with
    | some signature => pure signature
    | none => throw (IO.userError "Tree missing")
  let treeType := TypeSystem.Ty.nominal tree.id []
  let checked ← match SourceCoreDataCatalog.prepare program.signatures 100 [treeType] with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"match catalog rejected: {reprStr error}")
  let treeId := (checked.catalog.identity? treeType).getD ⟨999⟩
  let leaf := fun value => Value.constructed ⟨treeId, 0⟩ (.word (w value))
  let pair := fun left right => Value.constructed ⟨treeId, 1⟩ (.pair left right)
  let choose ← entryFor program checked "choose"
  let nested := pair (leaf 7) (leaf 8)
  assertTrue ((← execute choose [nested]) == .succeeded (.word (w 15))
    [present nested, present nested, present (.word (w 15)), present (.word (w 8))])
    "failed partial pattern allocated a binder or successful bindings were not source ordered"
  let first := pair (leaf 7) (leaf 0)
  assertTrue ((← execute choose [first]) == .succeeded (.word (w 7)) [present first, present first, present (.word (w 7))])
    "first matching arm or literal selection changed"
  let single := leaf 4
  assertTrue ((← execute choose [single]) == .succeeded (.word (w 4)) [present single, present single, present (.word (w 4))])
    "constructor mismatch did not skip to later arm"
  let unmatched := pair nested nested
  assertTrue ((← execute choose [unmatched]) == .succeeded (.word (w 99)) [present unmatched, present unmatched])
    "default arm should allocate no pattern bindings"
  let tuple ← entryFor program checked "tuple"
  let input := Value.pair (leaf 10) (.pair (.bool true) (.word (w 20)))
  assertTrue ((← execute tuple [input]) == .succeeded (.word (w 30))
    [present input, present input, present (.word (w 10)), present (.bool true), present (.word (w 20))])
    "nested tuple and constructor binding order changed"
  let integerCase ← entryFor program checked "integerCase"
  assertTrue ((← execute integerCase [.integer 0]) == .succeeded (.integer 5) [present (.integer 0), present (.integer 0)])
    "Integer literal pattern rejected zero"
  assertTrue ((← execute integerCase [.integer 1]) == .succeeded (.integer 6) [present (.integer 1), present (.integer 1)])
    "grouped Integer literal changed meaning"
  assertTrue ((← execute integerCase [.integer (-3)]) == .succeeded (.integer (-3))
    [present (.integer (-3)), present (.integer (-3)), present (.integer (-3))]) "Integer binder changed signed value"
  let wildcard ← entryFor program checked "wildcard"
  assertTrue ((← execute wildcard [.word (w 8)]) == .succeeded (.word (w 3))
    [present (.word (w 8)), present (.word (w 8))]) "wildcard did not skip faulting default"
  let unitCase ← entryFor program checked "unitCase"
  assertTrue ((← execute unitCase [.unit]) == .succeeded (.word (w 7)) [present .unit, present .unit]) "unit pattern failed"
  let noMatchEntry ← entryFor program checked "none"
  assertTrue ((← execute noMatchEntry [.word (w 8)]) == .succeeded .unit
    [present (.word (w 8)), present (.word (w 8))]) "nonmatching Unit match did not fall through"
  let failure ← entryFor program checked "nestedFailure"
  match ← execute failure [single] with
  | .failed reason store =>
      assertTrue (failure.failureDiagnostic? reason |>.isSome) "arm fault lost source diagnostic"
      assertTrue (store == [present single, present single, present (.word (w 4)), .inLeft .word .unit])
        "arm failure lost initialized binders or executed fallback"
  | other => throw (IO.userError s!"arm failure changed: {reprStr other}")
  match choose.run [nested] 20 with
  | .ok suspended => match suspended.checkpoint? with
    | some checkpoint =>
      let resumed := checkpoint.resume 100000
      assertTrue (resumed.observation == (← execute choose [nested])) "typed match checkpoint changed result/store"
    | none => throw (IO.userError "match checkpoint completed unexpectedly")
  | .error error => throw (IO.userError s!"match checkpoint rejected: {reprStr error}")
  let once ← entryFor program checked "once"
  assertTrue ((← execute once [single, .word (w 10)]) == .succeeded (.word (w 15))
    [present single, present (.word (w 11)), present single, present (.word (w 4))])
    "scrutinee effect was duplicated or binding observed an old store"
  let scrutineeFailure ← entryFor program checked "scrutineeFailure"
  match ← execute scrutineeFailure [single] with
  | .failed reason store =>
    assertTrue (scrutineeFailure.failureDiagnostic? reason |>.isSome) "scrutinee failure lost exact diagnostic"
    assertTrue (store == [present single, .inLeft (.namedData treeId) .unit])
      "failed scrutinee allocated hidden or arm cells"
  | other => throw (IO.userError s!"scrutinee failure changed: {reprStr other}")
  let functionBinder ← entryFor program checked "functionBinder"
  match ← execute functionBinder [.word (w 10)] with
  | .succeeded (.word value) store =>
    assertTrue (value == w 15 && store[0]? == some (present (.word (w 15))))
      "function pattern binder cloned or lost shared captured cell"
    assertTrue (store.length == 6) "function pattern binder parameter/let allocation count changed"
  | other => throw (IO.userError s!"function pattern binder changed: {reprStr other}")
  let modulo ← entryFor program checked "moduloPattern"
  assertTrue ((← execute modulo [.word Word.zero]) == .succeeded (.word (w 1))
    [present (.word Word.zero), present (.word Word.zero)]) "Word pattern modulo semantics changed"
  metadataTests program checked
  IO.println "source Core data matches GREEN"

end Tests.SourceCoreDataMatches
