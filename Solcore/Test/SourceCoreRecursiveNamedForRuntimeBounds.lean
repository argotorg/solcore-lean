import Solcore.SourceSemantics.CoreLowering.ProtectedForGenericEndpoint
import Solcore.Test.SourceCoreRecursiveNamedForHeaderRuntimeBounds
import Solcore.Test.SourceCoreRecursiveNamedWhileRuntimeBounds
import Solcore.Test.SourceCoreRecursiveNamedForBounds

/-! Fixed-budget for loops accept the same complete runtime context as their
condition, body and post. Concrete builtin certificates and the empty body
close every semantic child here; the post is the actual protected header Tree.
The original source/native measures remain independent. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedForRuntimeBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
section Concrete
variable {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {fuel : Nat} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  (unique : NodeOccurrencesUnique source)
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (bindings : ProtectedExpressionMeaning.Binds entry)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))


include definitions registered extension faithful observations runtimeViews uninitialized missing transport bindings unique in
theorem runtime_preserves_at {context : SourceSemantics.Context} {scope : Scope}
    {administrative : Core.Context} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {expected : TypeSystem.Ty} {type : Ty} {conditionCode postCode : Expr} {post : List ForItemForm} {reason : Word}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionReceipt : CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt
      scope condition ⟨.bool, conditionCode⟩)
    (postTree : ProtectedForHeader.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt)
      ambient.definitions administrative type (TypedForHeader.Fallthrough type) context scope post postCode)
    (postErrors : GenericForHeader.Tree.ReachableErrors registry faults postTree)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode (LocalLoop.fallthrough type) postCode reason)
      (LocalLoop.resultType type) ambient.definitions)
    (budget size : Nat) (bounded : size ≤ budget) :
    RecursiveNamedForContracts.LoopPreservesAtFor functions program evidence
      (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) size
      (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frame) (globals := globals) (administrative := administrative) (scope := scope)
      condition post [] expected type
      (LocalLoop.iterate type conditionCode (LocalLoop.fallthrough type) postCode reason) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  exact ProtectedFor.Body.loop_preserves_bounded_for functions program evidence transport
    (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) budget
    (fun child _ => RecursiveNamedBoundedContracts.preserves_at_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed entry
        (CompatibleExpressionBuiltinRuntime.preserves functions extension faithful observations runtimeViews
          program evidence valid.ledger valid.runtime unique uninitialized missing)) child)
    conditionFound conditionReceipt typed unique
    (fun child _ => SourceCoreRecursiveNamedWhileRuntimeBounds.empty_preserves_at functions program evidence _ child)
    (fun agrees reference currentValid child smaller =>
      SourceCoreRecursiveNamedForHeaderRuntimeBounds.runtime_post_preserves functions definitions registered extension
        faithful observations runtimeViews evidence unique transport bindings uninitialized missing
        postTree currentValid agrees reference budget child (Nat.le_of_lt smaller))
    (fun agrees reference currentValid child smaller =>
      SourceCoreRecursiveNamedForHeaderRuntimeBounds.runtime_post_faults functions definitions registered extension
        faithful observations runtimeViews evidence unique transport bindings uninitialized missing
        postTree postErrors currentValid agrees reference budget child (Nat.le_of_lt smaller))
    size bounded valid environments heaps locals agrees actualTyped reference read unmapped installed trace

include definitions registered extension faithful observations runtimeViews uninitialized missing transport bindings in
theorem runtime_reflects_at {context : SourceSemantics.Context} {scope : Scope}
    {administrative : Core.Context} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {expected : TypeSystem.Ty} {type : Ty} {conditionCode postCode : Expr} {post : List ForItemForm} {reason : Word}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionReceipt : CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt
      scope condition ⟨.bool, conditionCode⟩)
    (postTree : ProtectedForHeader.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt)
      ambient.definitions administrative type (TypedForHeader.Fallthrough type) context scope post postCode)
    (postErrors : GenericForHeader.Tree.ReachableErrors registry faults postTree)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode (LocalLoop.fallthrough type) postCode reason)
      (LocalLoop.resultType type) ambient.definitions)
    (budget size : Nat) (bounded : size ≤ budget) :
    RecursiveNamedForContracts.LoopReflectsAtFor functions program evidence
      (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) size
      (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frame) (globals := globals) (administrative := administrative) (scope := scope)
      condition post [] expected type
      (LocalLoop.iterate type conditionCode (LocalLoop.fallthrough type) postCode reason) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  exact ProtectedFor.Body.loop_reflects_bounded_for functions program evidence transport
    (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence) budget
    (fun child _ => RecursiveNamedBoundedContracts.reflects_at_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed entry
        (CompatibleExpressionBuiltinRuntime.reflects functions extension faithful observations runtimeViews
          program evidence valid.ledger valid.runtime uninitialized missing)) child)
    conditionFound conditionReceipt typed
    (fun child _ => SourceCoreRecursiveNamedWhileRuntimeBounds.empty_reflects_at functions program evidence _ child)
    (fun trace => by obtain ⟨_, impossible, _⟩ := ScalarStatementViews.nil_view false trace; cases impossible)
    (fun agrees reference currentValid child smaller =>
      SourceCoreRecursiveNamedForHeaderRuntimeBounds.runtime_post_reflects functions definitions registered extension
        faithful observations runtimeViews evidence transport bindings uninitialized missing
        postTree postErrors currentValid agrees reference budget child (Nat.le_of_lt smaller))
    size bounded valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
end Concrete

/-- The original native entry and condition remain strictly below the outer
budget; no regenerated completion witness is substituted. -/
abbrev original_condition := @SourceCoreRecursiveNamedForBounds.native_condition_below

/-- Post retains its actual six-slot evaluation and original cost. -/
abbrev original_post := @SourceCoreRecursiveNamedForBounds.native_post_below

/-- A later fault keeps the complete ordered condition/body/post prefix. -/
abbrev later_fault := @SourceCoreRecursiveNamedForBounds.next_fault_children

/-- Runtime coverage does not imply ordinary validity of unused rows. -/
abbrev runtime_not_ordinary := SourceCoreRecursiveNamedForHeaderRuntimeBounds.runtime_not_ordinary

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

/-- The actual checked/specialized source retains unresolved template rows.
Only its original for roots are compiled here; no enclosing qualified callable
compilation is claimed. Exact phase code and every native cell are checked. -/
private def template_for : IO Unit := do
  let program ← get "runtime for template source" (checkProgram {
    entry := "main.solc", externalLibraries := []
    mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
      "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
      "function qualified(flag: Bool) returns (Word, Bool) {",
      " for (; false; let skipped: Bool, skipped) {}",
      " for (; true; let skipped: Bool, skipped) { break; }",
      " for (; true; let failed: Bool, failed) { continue; }",
      " for (; true;) { let failed: Bool; failed; }",
      " for (let looping = true; looping; looping = false) {}",
      " for (let looping = true; looping; looping = false) { continue; }",
      " let f = lam(item) { return keep(item); }; return (f(1), f(flag)); }"
    ]}] })
  let signature ← match program.signatures.functions.filter (·.name == "qualified") with
    | [signature] => pure signature | _ => throw (IO.userError "for template signature missing")
  let generic ← match program.functions.filter (·.declaration == signature.id) with
    | [generic] => pure generic | _ => throw (IO.userError "for template body missing")
  let specialized ← get "for template specialization" (SourceSpecialization.specializeFunction signature generic [])
  let source := specialized.function.typedBody
  let rows := specialized.function.solvedRequirements
  require (!source.localSchemeTemplateIds.isEmpty && rows.map (·.id) == generic.solvedRequirements.map (·.id))
    "for full template ledger changed"
  for id in source.localSchemeTemplateIds do
    match rows.filter (·.id == id) with
    | [row] => match row.evidence with
      | .assumption predicate =>
        require (predicate == row.predicate && !specialized.assumptions.contains predicate)
          "for template assumption promoted"
      | _ => throw (IO.userError "for template implementation fabricated")
    | _ => throw (IO.userError "for template row missing or duplicated")
  let roots := source.roots.filterMap fun
    | .statement id => (source.lookupStatement? id).bind fun node => match node.form with
      | .forLoop _ _ _ _ => some node | _ => none
    | _ => none
  require (roots.length == 6) "for original root inventory changed"
  let lower := SourceCoreControl.lowerExpressionWithReasons
  let policy : SourceCoreLoops.Policy := { lowerExpression := lower }
  let reason := Word.ofNatModulo 911
  let captured := Core.Value.closure .word .word (.var 0) [.word (Word.ofNatModulo 919)]
  let initial : Store := [.integer (-929), captured]
  for (node, index) in roots.zipIdx do
    match node.form with
    | .forLoop initializers condition post statements =>
      let loopScope ← match initializers with
        | [] => pure []
        | [.letDecl binder (some _)] => pure [(binder.id, Core.Ty.bool)]
        | _ => throw (IO.userError "for initializer shape changed")
      let conditionCode ← get "for original condition"
        (lower 199 source loopScope condition (fun _ => reason))
      let bodyCode ← get "for original body"
        (SourceCoreLoops.lowerFlowStatementsWithPolicy policy 199 source loopScope statements .unit (fun _ => reason) false reason)
      let postCode ← get "for original post"
        (SourceCoreLoops.lowerForItems policy (.occurrence node.id.occurrence) 199 source loopScope post .unit
          (fun _ => reason) (fun _ => .ok (LocalLoop.fallthrough .unit)))
      let head ← get "for original initialization"
        (SourceCoreLoops.lowerForItems policy (.occurrence node.id.occurrence) 199 source [] initializers .unit
          (fun _ => reason) (fun scope => if scope == loopScope then
            .ok (LocalLoop.iterate .unit conditionCode.expression bodyCode postCode reason)
            else .error (.unsupportedStatement node.id node.form)))
      let code ← get "for actual whole loop"
        (SourceCoreLoops.lowerFlowStatementsWithPolicy policy 200 source [] [node.id] .unit (fun _ => reason) false reason)
      require (code == LocalLoop.sequence .unit head (LocalLoop.fallthrough .unit))
        "for actual whole original phases/suffix differ"
      require (Core.infer? [] code [] == some (LocalLoop.resultType .unit)) "for actual code type"
      let localCell := Core.Value.inRight .unit (.bool true)
      let beforeLoop := if loopScope.isEmpty then initial else initial ++ [localCell]
      let actual := if loopScope.isEmpty then [captured]
        else [Core.Value.cellRef (.sum .unit .bool) initial.length, .bool true, captured]
      let conditionActual := if loopScope.isEmpty then conditionCode.expression else conditionCode.expression.weakenAt 1
      let bodyActual := if loopScope.isEmpty then bodyCode else bodyCode.weakenAt 1
      let postActual := if loopScope.isEmpty then postCode else postCode.weakenAt 1
      let installed := TypedLexicalWhile.installedStore beforeLoop .unit conditionActual bodyActual postActual reason actual
      let expectedStore := if index == 2 || index == 3 then installed ++ [.inLeft .bool .unit]
        else if index ≥ 4 then installed.set initial.length (.inRight .unit (.bool false)) else installed
      let expectedValue := if index == 2 || index == 3 then
          Core.Value.inLeft (LocalLoop.controlType .unit) (.word reason)
        else LocalLoop.fallthroughValue .unit
      for fuel in [0, 1, 29, 10000] do
        let first := Core.runStateful fuel (.initial code [captured] initial)
        let completed := match first with
          | .outOfFuel checkpoint => Core.runStateful 10000 checkpoint | result => result
        match completed with
        | .done value after =>
          require (value == expectedValue && after == expectedStore)
            s!"for full ordered store/result/resume changed at root {index}"
        | other => throw (IO.userError s!"for actual loop unfinished {reprStr other}")
    | _ => throw (IO.userError "for original root form changed")

def run : IO Unit := do
  template_for
  SourceCoreRecursiveNamedForBounds.run
  IO.println "runtime for bounds: supported condition / concrete body / actual protected post / original strict children GREEN"

end Tests.SourceCoreRecursiveNamedForRuntimeBounds
