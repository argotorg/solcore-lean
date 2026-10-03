import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeForReflection
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinRuntime
import Solcore.Test.SourceCoreRecursiveNamedImperativeMatchBounds
import Solcore.Test.SourceCoreRecursiveNamedLexicalRuntimeBounds

/-! Actual builtin expression receipts close the shared finite Match/For/While
statement proof using the same complete runtime context. Selected arm contexts
come only from their actual ordered source binders. Header construction and the
catalog mutual theorem remain separate boundaries. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedImperativeRuntimeBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
#check_failure SourceTypedRuntime.run
section Concrete
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error} {values : ValuesContext}
  {source : TypedSource} {solved : List SolvedRequirement} {fuel : Nat} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (bindings : ProtectedExpressionMeaning.Binds entry)

include definitions registered extension faithful observations runtimeViews uninitialized missing transport bindings in
/-- The complete concrete expression family closes the sole statement induction. -/
theorem runtime_preserves_at (unique : NodeOccurrencesUnique source)
    (budget size : Nat) (bounded : size ≤ budget) {administrative : Core.Context}
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    {expressionSyntax : ExpressionId → Prop}
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt)
      ambient.definitions administrative context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeMatch.Tree.CatalogSites .reachable registry faults tree) :
    RecursiveNamedLoopContracts.PreservesAtFor functions program evidence
      (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
      (administrative := administrative) (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
      size (scope := scope) mode statements expected type code := by
  apply RecursiveNamedImperativeFor.preservesAt_match_with
    (validity := fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
    (extend := fun valid extended => valid.extend extended) (runtimeOf := fun _ valid => valid)
    (functions := functions) (definitions := definitions) (registered := registered) (extension := extension)
    (program := program) (evidence := evidence) (transport := transport) (bindings := bindings)
    (budget := budget) (faithful := faithful) (observations := observations)
    (meaningMost := ?_) .reachable unique tree errors size bounded
  intro context valid child _
  exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
    (ProtectedExpressionMeaning.preserves_of_typed entry
      (CompatibleExpressionBuiltinRuntime.preserves functions extension faithful observations runtimeViews
        program evidence valid.ledger valid.runtime unique uninitialized missing)) child

include definitions registered extension faithful observations runtimeViews uninitialized missing transport bindings in
/-- The complete concrete expression family closes the sole statement induction. -/
theorem runtime_reflects_at (unique : NodeOccurrencesUnique source)
    (budget size : Nat) (bounded : size < budget) {administrative : Core.Context}
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    {expressionSyntax : ExpressionId → Prop}
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt)
      ambient.definitions administrative context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeMatch.Tree.CatalogSites .reachable registry faults tree) :
    RecursiveNamedLoopContracts.ReflectsAtFor functions program evidence
      (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
      (administrative := administrative) (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
      size (scope := scope) mode statements expected type code := by
  apply RecursiveNamedImperativeFor.reflectsAt_match_with
    (validity := fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
    (extend := fun valid extended => valid.extend extended) (runtimeOf := fun _ valid => valid)
    (functions := functions) (definitions := definitions) (registered := registered) (extension := extension)
    (program := program) (evidence := evidence) (transport := transport) (bindings := bindings)
    (budget := budget) (faithful := faithful) (observations := observations)
    (reflection := ?_) .reachable runtimeViews unique tree errors size bounded
  intro context valid child _
  exact RecursiveNamedBoundedContracts.reflects_at_of_unbounded
    (ProtectedExpressionMeaning.reflects_of_typed entry
      (CompatibleExpressionBuiltinRuntime.reflects functions extension faithful observations runtimeViews
        program evidence valid.ledger valid.runtime uninitialized missing)) child

end Concrete

/-- A stronger condition is transported from the original parent through only
actual source binders. Runtime validity is never used to invent this condition. -/
theorem selected_context {source : TypedSource} (condition : SourceSemantics.Context → Prop)
    (extend : ∀ {context next binder}, condition context →
      BinderExtends source.owner context binder next → condition next)
    {context next : SourceSemantics.Context} {hiddenIds : List Resolved.LocalId}
    {scrutineeType : TypeSystem.Ty} {cases : List TypedMatchCase}
    {fallback : Option (List StatementId)} {request : GenericMatchChildren.Request}
    (valid : condition context)
    (related : GenericMatchChildren.ScopedContextFor source context hiddenIds
      scrutineeType cases fallback request next) : condition next :=
  RecursiveNamedImperativeFor.ContextTransport.scoped_context condition extend valid related

/-- The default request retains the exact parent condition. -/
theorem default_context {source : TypedSource} {condition : SourceSemantics.Context → Prop}
    {context : SourceSemantics.Context} {hiddenIds : List Resolved.LocalId}
    {scrutineeType : TypeSystem.Ty} {cases : List TypedMatchCase}
    {request : GenericMatchChildren.Request} (valid : condition context)
    (scopeIds : request.scope.map Prod.fst = hiddenIds) :
    GenericMatchChildren.ScopedContextFor source context hiddenIds scrutineeType cases
      (some request.statements) request context ∧ condition context :=
  ⟨.default rfl scopeIds, valid⟩

abbrev actual_frame := @SourceCoreRecursiveNamedLexicalRuntimeBounds.frame_runtime_valid
abbrev unused_ledger := SourceCoreRecursiveNamedLexicalRuntimeBounds.runtime_not_ordinary


private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

/-- The original reached blocks are compiled with the real recursive flow and
match callbacks. Their enclosing qualified lambda remains outside this family. -/
private def template_blocks : IO Unit := do
  let program ← get "upper template source" (checkProgram {
    entry := "main.solc", externalLibraries := []
    mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
      "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
      "function qualified(flag: Bool) returns (Word, Bool) {",
      " { match ((61, 7)) { case (61, picked) { let chosen: Word = picked; } default {} } }",
      " { if (true) { match (62) { case 61 { let skipped: Word = 1; } default { let reached: Word = 11; } } } else { let skipped: Word = 2; } }",
      " { let missing: Word; match (61) { case 61 { let fault: Word = missing; } default {} } let skipped: Word = 13; }",
      " let f = lam(item) { return keep(item); }; return (f(1), f(flag)); }"
    ]}] })
  let signature ← match program.signatures.functions.filter (·.name == "qualified") with
    | [signature] => pure signature | _ => throw (IO.userError "upper template signature missing")
  let generic ← match program.functions.filter (·.declaration == signature.id) with
    | [generic] => pure generic | _ => throw (IO.userError "upper template function missing")
  let actual ← get "upper template specialization" (SourceSpecialization.specializeFunction signature generic [])
  let source := actual.function.typedBody
  let ledger := actual.function.solvedRequirements
  require (!source.localSchemeTemplateIds.isEmpty && ledger == generic.solvedRequirements)
    "upper complete ordered template ledger changed"
  for id in source.localSchemeTemplateIds do
    match ledger.filter (·.id == id) with
    | [row] => match row.evidence with
      | .assumption predicate =>
        require (predicate == row.predicate && !actual.assumptions.contains predicate)
          "upper unused template assumption promoted"
      | _ => throw (IO.userError "upper template implementation fabricated")
    | _ => throw (IO.userError "upper template row missing/duplicated")
  let checked ← get "upper template catalog" (SourceCoreCompatibleCatalog.prepare program.signatures 100 [.word, .bool])
  let compilation : SourceCoreCompatibleDataMatches.Context := ⟨.initial checked, ledger, none, none⟩
  let functions : SourceCoreFunctions.Context := {
    plan := ⟨[actual.key], [actual], [], []⟩,
    owner := actual.key, globals := [], administrativePrefix := 1, solvedRequirements := ledger, internalReason := Word.zero}
  let noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ =>
    .error (.traversalExhausted (.declaration actual.function.declaration))
  let expression : SourceCoreLoops.ExpressionLowerer := fun fuel source scope id reasonAt =>
    SourceCoreFunctions.lowerExpressionWithReasons noBody fuel functions source scope id reasonAt
  let policy : SourceCoreLoops.Policy := {
    lowerExpression := expression
    lowerMatch := some (SourceCoreCompatibleDataMatches.lowerWithReasons compilation) }
  let roots := source.roots.filterMap fun
    | .statement id => (source.lookupStatement? id).bind fun node => match node.form with
      | .block _ => some node | _ => none
    | _ => none
  require (roots.length == 3) "upper original reached blocks changed"
  let reason := Word.ofNatModulo 941
  let word := fun n => Core.Value.word (Word.ofNatModulo n)
  let captured := Core.Value.closure .word .word (.var 0) [word 947]
  let before : Core.Store := [.integer (-953), captured, .cellRef .integer 0]
  let expectedCells : List Core.Store := [
    [.inRight .unit (.pair (word 61) (word 7)), .inRight .unit (word 7), .inRight .unit (word 7)],
    [.inRight .unit (word 62), .inRight .unit (word 11)],
    [.inLeft .word .unit, .inRight .unit (word 61)] ]
  for ((node, cells), index) in (roots.zip expectedCells).zipIdx do
    let code ← get "upper actual recursive flow"
      (SourceCoreLoops.lowerFlowStatementsWithPolicy policy 200 source [] [node.id] .unit
        (fun _ => reason) false reason)
    require (Core.infer? [] code compilation.definitions == some (LocalLoop.resultType .unit))
      "upper recursive flow type changed"
    let expected := if index == 2 then Core.Value.inLeft (LocalLoop.controlType .unit) (.word reason)
      else LocalLoop.fallthroughValue .unit
    for fuel in [0, 1, 23, 10000] do
      let done := match Core.runStateful fuel (.initial code [captured] before) with
        | .outOfFuel state => Core.runStateful 10000 state | other => other
      match done with
      | .done value after =>
        require (value == expected && after == before ++ cells)
          s!"upper original block full ordered store/fault/resume changed at {index}: {reprStr value} / {reprStr after}"
      | other => throw (IO.userError s!"upper original block unfinished {reprStr other}")

def run : IO Unit := do
  template_blocks
  SourceCoreRecursiveNamedImperativeMatchBounds.run
  IO.println "runtime imperative bounds: actual whole recursive Match/For/While / same reached template ledger / stronger context transport / full ordered store and fault/resume GREEN"

end Tests.SourceCoreRecursiveNamedImperativeRuntimeBounds
