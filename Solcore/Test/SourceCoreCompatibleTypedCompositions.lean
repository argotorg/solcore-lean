import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTypedCompositions
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualIndices
import Solcore.Frontend.SourceCoreCompatibleFunctions
import Solcore.Frontend.ProgramChecking
import Solcore.Frontend.SourceCoreCallableIndexedFrames

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! One-level heads compose concrete, typed index children. The closed
consumers have no runtime child derivation or universal child meaning premise.
The runtime cases use real contextual compilation and full ambient definitions;
actual root-to-head extraction is supplied by the recursive compiler layer. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleTypedCompositions
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionTypedCompositions CompatibleExpressionIndices CompatiblePayload GeneralHeap ReadOnly

variable {values : ValuesContext} {readFuel : Nat} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag → faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension valid unique uninitialized missing in
/-- Arbitrary certified index children discharge the head's preservation
obligations, including native comparator allocation under the inserted slot. -/
theorem head_preserves :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (Head values.checked source (CompatibleExpressionIndices.Tree readFuel values source context solved reasonAt)) faults :=
  Head.preserves functions program evidence unique
    (CompatibleExpressionIndices.preserves functions extension program evidence valid unique uninitialized missing)

include extension valid uninitialized missing in
/-- Completed native heads construct their independent source result without
being given source child traces in advance. -/
theorem head_reflects :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (Head values.checked source (CompatibleExpressionIndices.Tree readFuel values source context solved reasonAt)) faults :=
  Head.reflects functions program evidence
    (CompatibleExpressionIndices.reflects functions extension program evidence valid uninitialized missing)

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function strict() returns (Word) { let m: mapping(Bool => Word); let n: mapping(Bool => Word); return m[true] + n[false]; }",
    "function left_fault() returns (Word) { let missing: Word; let other: mapping(Bool => Word); return missing + other[true]; }",
    "function right_fault() returns (Word) { let m: mapping(Bool => Word); let missing: Word; return m[true] + missing; }",
    "function and_skip() returns (Bool) { let other: mapping(Bool => Bool); return false && other[true]; }",
    "function or_skip() returns (Bool) { let other: mapping(Bool => Bool); return true || other[true]; }",
    "function and_evaluate() returns (Bool) { let m: mapping(Bool => Bool); return true && m[true]; }",
    "function or_evaluate() returns (Bool) { let m: mapping(Bool => Bool); return false || m[true]; }",
    "function true_branch() returns (Bool) { let m: mapping(Bool => Bool); let other: mapping(Bool => Bool); return true ? m[true] : other[true]; }",
    "function unary() returns (Bool) { let m: mapping(Bool => Bool); return !m[true]; }",
    "function conditional() returns (Bool) { let m: mapping(Bool => Bool); let other: mapping(Bool => Bool); let n: mapping(Bool => Bool); return m[true] ? other[true] : n[false]; }",
    "function branch_fault() returns (Bool) { let m: mapping(Bool => Bool); let other: mapping(Bool => Bool); let missing: Bool; return m[true] ? other[true] : missing; }",
    "function condition_fault() returns (Bool) { let missing: Bool; let other: mapping(Bool => Bool); return missing ? other[true] : other[false]; }",
    "function pair() returns ((Bool, Bool)) { let m: mapping(Bool => Bool); let n: mapping(Bool => Bool); return (m[true], n[false]); }",
    "function grouped() returns (Bool) { let m: mapping(Bool => Bool); return (m[true]); }"
  ]}] }
private def reached : Nat → TypedSource → ExpressionId → List ExpressionNode
  | 0, _, _ => []
  | budget + 1, source, id => match source.lookupExpression? id with
    | none => []
    | some node => node :: (match node.form with
      | .index base key => reached budget source base ++ reached budget source key
      | .group inner | .unary _ inner => reached budget source inner
      | .binary left _ right => reached budget source left ++ reached budget source right
      | .conditional condition first second => reached budget source condition ++ reached budget source first ++ reached budget source second
      | .tuple ids => ids.flatMap (reached budget source)
      | _ => [])

def run : IO Unit := do
  let program ← get "typed head checker" (checkProgram workspace)
  let roots := program.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program roots 300 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"typed head specialization: {reprStr other}")
  let prepared ← get "typed head real compiler" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let checked := prepared.checked
  let mut count := 0
  for function in prepared.prepared.functions do
    let name := (program.signatures.functions.find? (·.id == function.signature.key.declaration)).map (·.name) |>.getD ""
    let source := function.specialized.function.typedBody
    let returnId : ExpressionId ← match source.nodes.findSome? fun
      | .statement node => match node.form with | .returnStmt (some id) => some id | _ => none
      | _ => none with
      | some id => pure id | none => throw (IO.userError "typed head return missing")
    let nodes := reached 30 source returnId
    let binderIds := (nodes.filterMap fun node => match node.form with | .reference _ (.local id) => some id | _ => none).eraseDups
    let mut values := SourceCoreCompatibleValues.Context.initial checked
    let mut bindings : List (TypedBinder × Ty × Option Value) := []
    for id in binderIds do
      let binder ← get "typed head binder" (SourceCoreDataPlaces.rootBinder source id)
      let native ← get "typed head binder projection" (checked.catalog.project binder.scheme.body)
      let expected ← match binder.scheme.body with
        | .mapping key result => do
          let encoded ← get "typed head expected mapping" (SourceCoreCompatibleValues.encode 100 values binder.scheme.body (.mapping key result []))
          values := encoded.context
          pure (some encoded.value)
        | _ => pure none
      bindings := bindings ++ [(binder, native, expected)]
    let diagnostics ← match prepared.prepared.diagnostics with
      | some diagnostics => pure diagnostics.program | none => throw (IO.userError "typed head diagnostics missing")
    let owner := function.signature.key
    let own ← match diagnostics.base.find? owner with
      | some own => pure own | none => throw (IO.userError "typed head owner missing")
    let compilation : SourceCoreFunctions.Context := {
      plan := prepared.prepared.plan, owner, globals := prepared.prepared.globals, administrativePrefix := 1,
      solvedRequirements := function.specialized.function.solvedRequirements, internalReason := Word.zero }
    let scope := bindings.map fun (binder, type, _) => (binder.id, type)
    let representation := SourceCoreCompatibleFunctions.representation values 150
    let lowered ← get "typed head actual contextual compiler" (
      SourceCoreGeneralFunctions.lowerContextualExpression program representation checked.signatures prepared.prepared.locals
        prepared.prepared.contexts own.assignments diagnostics compilation prepared.prepared.callableContext none none 150 source scope returnId (diagnostics.reasonAt owner))
    let frame : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
    let adminType := Ty.function .unit frame.type
    let adminExpr := Expr.lambda .unit frame.type (SourceCoreCallableIndexedFrames.empty frame)
    let body := bindings.foldl (fun body (_, type, _) => Expr.letE (OptionalCell.allocate type) body)
      (.letE (.integer 99) (lowered.expression.weakenAt 0))
    let native : Core.Program := ⟨LanguageResult.resultType lowered.type,
      .letE (.newCell adminType adminExpr) body, checked.catalog.definitions ++ [frame.definition]⟩
    assertTrue native.check s!"typed head {name} failed Core checker"
    for fuel in [0, 5, 50, 1000] do
      let completed := match native.runStateful fuel with
        | .outOfFuel checkpoint => Core.runStateful 30000 checkpoint
        | other => other
      match completed with
      | .done result store =>
        assertTrue (store[0]? == some (.closure .unit frame.type (SourceCoreCallableIndexedFrames.empty frame) []))
          "typed head changed administrative closure"
        let shouldAllocate := !(name == "left_fault" || name == "and_skip" || name == "or_skip" || name == "condition_fault")
        assertTrue ((store.length > bindings.length + 1) == shouldAllocate) "typed head evaluated a skipped helper or lost a reached helper"
        if name.endsWith "fault" then
          let missing ← match nodes.find? (fun node => match node.form with | .reference "missing" (.local _) => true | _ => false) with
            | some node => pure node | none => throw (IO.userError "typed head failure node missing")
          assertTrue (result == .inLeft lowered.type (.word (diagnostics.reasonAt owner missing.id))) "typed head changed first fault"
        else
          let expected : Value := if name == "strict" then .word Word.zero
            else if name == "pair" then .pair (.bool false) (.bool false)
            else .bool (name == "unary" || name == "or_skip")
          assertTrue (result == .inRight .word expected) "typed head returned the wrong primitive/selected branch result"
        for ((binder, type, expected), position) in bindings.zipIdx do
          let expectedCell := if binder.name == "other" || binder.name == "missing" then Value.inLeft type .unit
            else match expected with | some value => .inRight .unit value | none => .inLeft type .unit
          assertTrue (store[bindings.length - position]? == some expectedCell) "typed head lost prefix or evaluated skipped tail"
      | other => throw (IO.userError s!"typed head {name} failed: {reprStr other}")
    count := count + 1
  assertTrue (count == 14) "typed head cases missing"
  IO.println "typed heads: real contextual index operands, group/pair, strict and short-circuit operators, lazy conditional branches, typed temporary slots, first faults and resume GREEN"

end Tests.SourceCoreCompatibleTypedCompositions
