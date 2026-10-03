import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralRuntimeExtraction
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! A real whole-root Functions acceptance now constructs all leaf support.
No separate leaf, child-tree or runtime-meaning callback is supplied. Native
reflection starts from completion alone; full-ledger and static source/type
conditions stay explicit. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleGeneralRuntimeExtraction
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatiblePayload GeneralHeap ReadOnly CompatibleExpressionGeneral

section Accepted
variable
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
  {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word}
  {sourceContext : SourceSemantics.Context}
  (unique : NodeOccurrencesUnique source)
  (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
  (signatures : sourceContext.signatures = values.checked.signatures)
  (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source sourceContext (Syntax source))
  (policyFor : PolicyFor policy context readFuel values source scope reasonAt)
  (coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
  {id : ExpressionId} (syntaxTree : Syntax source id) {node : ExpressionNode}
  (found : source.lookupExpression? id = some node)
  (typed : ExpressionHasType source sourceContext id node.type)
  {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
  (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered)

include unique declarations signatures constructorValid policyFor coercions syntaxTree found typed accepted

/-- Actual accepted root code fixes every child and ordered literal occurrence. -/
theorem accepted_support :
    CompatibleExpressionGeneralRuntime.Certificate readFuel values source sourceContext context.solvedRequirements reasonAt scope id lowered :=
  CompatibleExpressionGeneralRuntimeExtraction.of_functions unique declarations signatures constructorValid policyFor
    coercions syntaxTree found typed accepted

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment)
  (sameLedger : sourceContext.solvedRequirements = context.solvedRequirements)
  (runtime : RuntimeRequirementLedgerValid sourceContext) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ child location, faults (.uninitializedLocation location) (reasonAt child))
  (missing : ∀ child key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt child).add tag))

include extension faithful functionLeaves functionTypes sameLedger runtime uninitialized missing

theorem accepted_preserves :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program sourceContext evidence source (fun s i code => s = scope ∧ i = id ∧ code = lowered) faults := by
  have receipt := accepted_support unique declarations signatures constructorValid policyFor coercions syntaxTree found typed accepted
  intro s i code selected
  obtain ⟨rfl, rfl, rfl⟩ := selected
  exact CompatibleExpressionGeneralRuntime.preserves functions extension faithful functionLeaves functionTypes
    program evidence sameLedger runtime unique uninitialized missing receipt

theorem accepted_reflects :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program sourceContext evidence source (fun s i code => s = scope ∧ i = id ∧ code = lowered) faults := by
  have receipt := accepted_support unique declarations signatures constructorValid policyFor coercions syntaxTree found typed accepted
  intro s i code selected
  obtain ⟨rfl, rfl, rfl⟩ := selected
  exact CompatibleExpressionGeneralRuntime.reflects functions extension faithful functionLeaves functionTypes
    program evidence sameLedger runtime uninitialized missing receipt
end Accepted

private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def word (value : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo value)
private def content : String := String.intercalate "\n" [
  "function compound() returns (Word) { return (false ? (1 / 0) : ((5 + 7) * 3)) + 2; }",
  "function pairRoot() returns ((Word, Word)) { return (13 + 17, 19 * 23); }",
  "function lazyRoot() returns (Bool) { return true || (29 / 0 == 31); }",
  "function faultLeft() returns (Word) { let prior = 41; let absent: Word; return absent + (43 / 0); }",
  "function faultRight() returns (Word) { let prior = 47; let absent: Word; return (prior + 53) + absent; }",
  "function mappingRoot() returns (Word) { let table: mapping(Word => Word); table[59] = 61; return table[59] + table[67]; }"
]

private def native (code : Core.Expr) (expected : Core.Value) : IO Unit := do
  let captured := Core.Value.closure .unit .word (.var 0) [.word (Word.ofNatModulo 101)]
  let store : Store := [captured, .word (Word.ofNatModulo 103)]
  for fuel in [0, 1, 17, 300000] do
    let first := Core.runStateful fuel (.initial code [captured] store)
    let result := match first with
      | .outOfFuel checkpoint => Core.runStateful 300000 checkpoint
      | result => result
    match result with
    | .done value after =>
      require (value == .inRight .word expected && after == store)
        "whole-root value/captures/full native store changed"
    | other => throw (IO.userError s!"whole-root did not finish: {reprStr other}")

private def lower (values : SourceCoreCompatibleValues.Context) (context : SourceCoreFunctions.Context)
    (source : TypedSource) (id : ExpressionId) : IO SourceCoreBasic.LoweredExpr := do
  let found ← match source.lookupExpression? id with
    | some node => pure node
    | none => throw (IO.userError "whole-root lookup missing")
  let policy := SourceCoreCompatibleDataExpressions.functionPolicy 1000 values
  let noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ =>
    .error (.unsupportedExpression id found.form)
  get "actual whole-root Functions compiler"
    (SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 1000 context source [] id (fun _ => Word.zero))

/-- Real complete roots retain their original ordered ledger. The extra
assumption variants and repeated pair below are explicit retained-IR mutations. -/
private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  for name in ["compound", "pairRoot", "lazyRoot"] do
    let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
    let named ← match compiled.indexed.base.functions.filter (·.signature.key == key) with
      | [named] => pure named
      | _ => throw (IO.userError "whole-root function missing")
    let actual ← get "whole-root full specialization"
      (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan key)
    require (actual == named.specialized) "whole-root full record changed"
    let source := actual.function.typedBody
    let ids := source.nodes.filterMap fun
      | .statement node => match node.form with | .returnStmt (some id) => some id | _ => none
      | _ => none
    let id ← match ids with | [id] => pure id | _ => throw (IO.userError "whole-root return not singleton")
    let ledger := actual.function.solvedRequirements
    let predicate := ProgramSignatures.builtinIntPredicate .word
    let fresh : RequirementId := ⟨(ledger.map (·.id.index)).foldl max 0 + 1⟩
    let unrelated : SolvedRequirement := ⟨fresh, predicate, .assumption predicate⟩
    let values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
    let base : SourceCoreFunctions.Context := {
      plan := compiled.indexed.base.plan, owner := key, globals := compiled.indexed.base.globals,
      administrativePrefix := 1, solvedRequirements := ledger, internalReason := Word.zero }
    let expected : Core.Value := if name == "compound" then .word (Word.ofNatModulo 38)
      else if name == "pairRoot" then .pair (.word (Word.ofNatModulo 30)) (.word (Word.ofNatModulo 437))
      else .bool true
    let original ← lower values base source id
    for rows in [ledger, unrelated :: ledger, ledger ++ [unrelated]] do
      let code ← lower values {base with solvedRequirements := rows} source id
      require (code == original) "unused full-ledger row changed whole-root code"
      native code.expression expected
    if name == "pairRoot" then
      let node ← match source.lookupExpression? id with | some node => pure node | none => throw (IO.userError "pair missing")
      match node.form with
      | .tuple [left, _] =>
        let changed := SourceCoreEvidence.withNode source {node with form := .tuple [left, left]}
        let code ← lower values base changed id
        native code.expression (.pair (.word (Word.ofNatModulo 30)) (.word (Word.ofNatModulo 30)))
      | _ => throw (IO.userError "pair root form changed")

/-- A real checked template-bearing source supplies a closed arithmetic
subtree to Functions lowering. No whole callable compilation is claimed. -/
private def template_root : IO Unit := do
  let workspace : Workspace.RawWorkspace := {
    entry := "main.solc", externalLibraries := []
    mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
      "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
      "function qualified(flag: Bool) returns (Word, Bool) {",
      " let initial: Word = 61 + 67; let f = lam(item) { return keep(item); }; return (f(1), f(flag)); }"
    ]}] }
  let program ← get "template checked program" (checkProgram workspace)
  let signature ← match program.signatures.functions.filter (·.name == "qualified") with
    | [signature] => pure signature
    | _ => throw (IO.userError "template signature missing")
  let generic ← match program.functions.filter (·.declaration == signature.id) with
    | [generic] => pure generic
    | _ => throw (IO.userError "template function missing")
  let actual ← get "template actual specialization" (SourceSpecialization.specializeFunction signature generic [])
  let source := actual.function.typedBody
  let ledger := actual.function.solvedRequirements
  require (!source.localSchemeTemplateIds.isEmpty && ledger.map (·.id) == generic.solvedRequirements.map (·.id))
    "template IDs or complete ordered ledger changed"
  for id in source.localSchemeTemplateIds do
    match ledger.filter (·.id == id) with
    | [row] => match row.evidence with
      | .assumption predicate =>
        require (predicate == row.predicate && !actual.assumptions.contains predicate)
          "template assumption was promoted"
      | _ => throw (IO.userError "template implementation fabricated")
    | _ => throw (IO.userError "template row missing or duplicated")
  let checked ← get "template compatible catalog" (SourceCoreCompatibleCatalog.prepare program.signatures 100 [.word, .bool])
  let values := SourceCoreCompatibleValues.Context.initial checked
  let context : SourceCoreFunctions.Context := {
    plan := ⟨[actual.key], [actual], [], []⟩, owner := actual.key, globals := [],
    administrativePrefix := 1, solvedRequirements := ledger, internalReason := Word.zero }
  let candidates := source.nodes.filterMap fun
    | .expression node => match node.form with | .binary _ _ _ => some node.id | _ => none
    | _ => none
  let id ← match candidates with | [id] => pure id | _ => throw (IO.userError "template arithmetic root not singleton")
  let code ← lower values context source id
  native code.expression (.word (Word.ofNatModulo 128))

private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"whole-root ordered source cells changed: {reprStr state.heap}"

def run : IO Unit := do
  let names := ["compound", "pairRoot", "lazyRoot", "faultLeft", "faultRight", "mappingRoot"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "general runtime extraction" content names
  inspect compiled
  template_root
  for fuel in [0, 37, 151, 300000] do
    for name in names do
      let started ← SourceCoreUnifiedCorpusSupport.execute compiled name [] fuel
      let finished ← get "whole-root public resume" (started.resume 300000)
      match name, finished.observation with
      | "compound", .done value state => require (reprStr value == reprStr (word 38)) "compound result"; cells state []
      | "pairRoot", .done value state =>
        require (reprStr value == reprStr (SourceTypedRuntime.Value.product (word 30) (word 437))) "pair result"
        cells state []
      | "lazyRoot", .done (.bool true) state => cells state []
      | "mappingRoot", .done value state =>
        require (reprStr value == reprStr (word 61)) "mapping result"
        cells state [(.mapping .word .word, some (.mapping .word .word [(word 59, word 61)]))]
      | "faultLeft", .fault (.uninitializedLocal binder) state
      | "faultRight", .fault (.uninitializedLocal binder) state =>
        let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
        let named ← match compiled.indexed.base.functions.filter (·.signature.key == key) with
          | [named] => pure named
          | _ => throw (IO.userError "fault function missing")
        let expected ← match (SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody).filter (·.name == "absent") with
          | [binder] => pure binder.id
          | _ => throw (IO.userError "fault binder missing")
        require (binder == expected) "first fault identity changed"
        cells state [(.word, some (word (if name == "faultLeft" then 41 else 47))), (.word, none)]
      | _, other => throw (IO.userError s!"whole-root unexpected {name}: {reprStr other}")
  IO.println "whole Functions root / same-tree literals / full template ledger / ordered duplicates / fault heaps / resume GREEN"

end Tests.SourceCoreCompatibleGeneralRuntimeExtraction
