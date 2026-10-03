import Solcore.SourceSemantics.CoreLowering.ProtectedWhileGenericEndpoint
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralRuntime
import Solcore.SourceSemantics.CoreLowering.ProtectedLexicalStatementControl
import Solcore.Test.SourceCoreRecursiveNamedWhileBounds

/-! The sole finite while proof accepts a context predicate. These consumers
specialize it to the complete runtime ledger and actual dictionary, then close
atomic conditions and empty bodies with concrete existing semantics. Template
rows stay present; Header, for and lexical contracts remain unchanged. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedWhileRuntimeBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
open RecursiveNamedLoopContracts (Below PreservesAtFor ReflectsAtFor)
#check_failure SourceTypedRuntime.run

section EmptyBody
variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} {frame : SourceCoreCallableIndexedFrames.Layout}
  {globals : Nat} {administrative : Core.Context} {scope : Scope} {expected : TypeSystem.Ty} {type : Ty}

/-- The empty body closes at every original source grade and every predicate. -/
theorem empty_preserves_at (validity : SourceSemantics.Context → Prop) (size : Nat) :
    PreservesAtFor functions program evidence validity (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
      (administrative := administrative) (scope := scope) size false [] expected type (LocalLoop.fallthrough type) := by
  intro _ mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals _ _ _ _ _ _ trace
  cases trace with
  | control executed =>
    obtain ⟨rfl, rfl, rfl⟩ := ScalarStatementViews.nil_view false executed.sound
    exact ⟨_, store, mapping, world, LocalLoop.fallthrough_evaluates _ _ _, .fallthrough environment,
      heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩
  | fault failed => exact False.elim (ScalarStatementViews.nil_cannot_fault false failed.sound)

/-- Reflection keeps the native grade and constructs a separate source grade. -/
theorem empty_reflects_at (validity : SourceSemantics.Context → Prop) (size : Nat) :
    ReflectsAtFor functions program evidence validity (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
      (administrative := administrative) (scope := scope) size false [] expected type (LocalLoop.fallthrough type) := by
  intro _ mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals _ _ _ _ _ _ evaluated
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.fallthrough_evaluates type actual store)
  have original := ProtectedLexicalStatements.nil_executes false program context evidence source environment before
  obtain ⟨sourceSize, trace⟩ := RecursiveNamedLoopContracts.ExecutesAt.has_size original
  exact ⟨sourceSize, context, _, before, mapping, world, trace, .fallthrough environment, heaps,
    .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩
end EmptyBody

section RuntimeWhile
variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {administrative : Core.Context}
  {scope : Scope} {type : Ty} {conditionCode : Expr} {selfReason : Word}

include transport in
/-- Runtime validity closes the condition law; the body needs no semantic IH. -/
theorem runtime_preserves_at {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition [])
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionReceipt : CompatibleExpressionLiteralRuntime.Certificate solved source condition ⟨.bool, conditionCode⟩)
    (unique : NodeOccurrencesUnique source)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode (LocalLoop.fallthrough type) selfReason) (LocalLoop.resultType type) ambient.definitions)
    (budget size : Nat) (bounded : size ≤ budget) :
    ProtectedWhile.HeadPreservesAtFor functions program evidence
      (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
      (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frame) (globals := globals) (administrative := administrative) (scope := scope)
      size id expected type (LocalLoop.whileLoop type conditionCode (LocalLoop.fallthrough type) selfReason) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  exact ProtectedWhile.Body.while_preserves_bounded_for
    (certificate := fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code)
    (validity := fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
    functions program evidence transport budget
    (fun child _ => RecursiveNamedBoundedContracts.preserves_at_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed entry
        (TypedGenericExpressionMeaning.preserves_of_unrestricted
          (CompatibleExpressionLiteralRuntime.preserves functions program context evidence valid.ledger valid.runtime unique faults))) child)
    found form conditionFound conditionReceipt typed unique
    (fun child _ => empty_preserves_at functions program evidence _ child) size bounded valid environments heaps locals agrees actualTyped reference read unmapped installed trace

include transport in
/-- Native completion reflects without source execution or preservation input. -/
theorem runtime_reflects_at {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition [])
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionReceipt : CompatibleExpressionLiteralRuntime.Certificate solved source condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode (LocalLoop.fallthrough type) selfReason) (LocalLoop.resultType type) ambient.definitions)
    (budget size : Nat) (bounded : size ≤ budget) :
    ProtectedWhile.HeadReflectsAtFor functions program evidence
      (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
      (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frame) (globals := globals) (administrative := administrative) (scope := scope)
      size id expected type (LocalLoop.whileLoop type conditionCode (LocalLoop.fallthrough type) selfReason) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  exact ProtectedWhile.Body.while_reflects_bounded_for
    (certificate := fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code)
    (validity := fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
    functions program evidence transport budget
    (fun child _ => RecursiveNamedBoundedContracts.reflects_at_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed entry
        (TypedGenericExpressionMeaning.reflects_of_unrestricted
          (CompatibleExpressionLiteralRuntime.reflects functions program context evidence valid.ledger valid.runtime source faults))) child)
    found form conditionFound conditionReceipt typed
    (fun child _ => empty_reflects_at functions program evidence _ child)
    (fun trace => by obtain ⟨_, impossible, _⟩ := ScalarStatementViews.nil_view false trace; cases impossible)
    size bounded valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
end RuntimeWhile


section Frame
variable {program : SourceSemantics.Program} {instantiation : DeclarationInstantiation}
  {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {context : SourceSemantics.Context}
  {types : List TypeSystem.Ty} {solved : List SolvedRequirement}

/-- The real frame supplies the same complete dictionary and ledger, with no
empty-template or ordinary-validity condition. -/
theorem frame_runtime_valid
    (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (programTyped : ProgramWellFormed program) (sameLedger : function.context.solvedRequirements = solved) :
    CompatibleRuntimeContextValidity.Valid solved context function.evidence :=
  CompatibleRuntimeContextValidity.of_frame frame extended programTyped sameLedger

/-- Every retained row, including an unused template, is kept by the consumer. -/
theorem full_ledger_retained {row : SolvedRequirement}
    (valid : CompatibleRuntimeContextValidity.Valid solved context function.evidence) (member : row ∈ solved) :
    row ∈ context.solvedRequirements := by rw [valid.ledger]; exact member
end Frame

section Boundary
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def goal : ProgramPredicate := ProgramSignatures.builtinIntPredicate .word
private def row : SolvedRequirement := ⟨⟨0⟩, goal, .assumption goal⟩
private def context : SourceSemantics.Context := (Context.ofSignatures signatures).withSolvedRequirements [row]

/-- Runtime validity cannot supply the old ordinary premise for an unused row. -/
theorem runtime_not_ordinary :
    CompatibleRuntimeContextValidity.Valid [row] context [] ∧
      ¬ CompatibleExpressionLiterals.ContextValid [row] context [] := by
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · refine ⟨?_, ?_⟩
    · change ([⟨0⟩] : List RequirementId).Nodup; decide
    · intro item evidence member implementation
      have same : item = row := by simpa [context, Context.withSolvedRequirements] using member
      subst item
      cases implementation
  · constructor
    · intro predicate evidence found; cases found
    · intro predicate member; cases member
  · intro ordinary
    have valid := ordinary.valid.entriesValid row (by simp [context, Context.withSolvedRequirements])
    cases valid with
    | intro retained =>
      cases retained with
      | intro represents valid =>
        cases represents
        cases valid with
        | assumption member => cases member
end Boundary

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

/-- The enclosing checked source has a real qualified local. We compile the
reached bare while separately with its original complete node table and rows.
This audit does not claim compilation of the enclosing qualified body. -/
private def template_while : IO Unit := do
  let workspace : Workspace.RawWorkspace := {
    entry := "main.solc", externalLibraries := []
    mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
      "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
      "function qualified(flag: Bool) returns (Word, Bool) {",
      " while (false) {} let f = lam(item) { return keep(item); }; return (f(1), f(flag)); }"
    ]}] }
  let program ← get "runtime while checked template source" (checkProgram workspace)
  let signature ← match program.signatures.functions.filter (·.name == "qualified") with
    | [signature] => pure signature
    | _ => throw (IO.userError "runtime while qualified signature missing")
  let generic ← match program.functions.filter (·.declaration == signature.id) with
    | [generic] => pure generic
    | _ => throw (IO.userError "runtime while qualified body missing")
  let specialized ← get "runtime while actual template specialization"
    (SourceSpecialization.specializeFunction signature generic [])
  let source := specialized.function.typedBody
  let ids := source.localSchemeTemplateIds
  let rows := specialized.function.solvedRequirements
  require (!ids.isEmpty && signature.scheme.predicates.isEmpty && specialized.assumptions.isEmpty)
    "runtime while template ledger boundary disappeared"
  require (rows.map (·.id) == generic.solvedRequirements.map (·.id))
    "runtime while specialization removed or reordered ledger rows"
  for id in ids do
    let row ← match rows.filter (·.id == id) with
      | [row] => pure row
      | _ => throw (IO.userError "runtime while unique template row missing")
    match row.evidence with
    | .assumption predicate =>
      require (predicate == row.predicate && !(specialized.assumptions.contains predicate))
        "runtime while template was promoted to a declaration assumption"
    | _ => throw (IO.userError "runtime while template evidence changed")
  let heads := source.nodes.filterMap fun
    | .statement node => match node.form with
      | .whileLoop condition [] => some (node, condition)
      | _ => none
    | _ => none
  let (node, condition) ← match heads with
    | [pair] => pure pair
    | _ => throw (IO.userError "runtime while actual empty head missing")
  let conditionNode ← match source.lookupExpression? condition with
    | some node => pure node
    | none => throw (IO.userError "runtime while condition lookup missing")
  require (conditionNode.form == .reference "false" (.builtinBoolean false)) "runtime while source condition changed"
  let reason : Word := Word.ofNatModulo 811
  let lower := SourceCoreControl.lowerExpressionWithReasons
  let conditionCode ← get "runtime while original condition lower" (lower 100 source [] condition (fun _ => reason))
  match accepted : SourceCoreLoops.lowerFlowStatementsWithExpression lower 101 source [] [node.id] .unit (fun _ => reason) false reason with
  | .error error => throw (IO.userError s!"runtime while actual compiler failed: {reprStr error}")
  | .ok code =>
    let _issued := accepted
    let expected := LocalLoop.sequence .unit
      (LocalLoop.whileLoop .unit conditionCode.expression (LocalLoop.fallthrough .unit) reason)
      (LocalLoop.fallthrough .unit)
    require (code == expected) "runtime while full original head/empty suffix code changed"
    require (source.localSchemeTemplateIds == ids && specialized.function.solvedRequirements == rows)
      "runtime while compiler filtered the complete source ledger"
    let captured := Core.Value.closure .word .word (.var 0) [.word (Word.ofNatModulo 821)]
    let initial : Store := [.word (Word.ofNatModulo 823), captured]
    let mut baseline : Option (Core.Value × Store) := none
    for fuel in [10000, 0, 1, 19] do
      let first := runStateful fuel (.initial code [] initial)
      let completed := match first with
        | .outOfFuel checkpoint => runStateful 10000 checkpoint
        | result => result
      match completed with
      | .done value store =>
        require (value == .inRight .word (.inLeft LocalLoop.transferType (.inLeft .unit .unit))) "runtime while zero-iteration flow changed"
        require (decide (store.take initial.length = initial)) "runtime while changed complete initial prefix"
        require (store.length == initial.length + 1) "runtime while installed self cell missing"
        match baseline with
        | none => baseline := some (value, store)
        | some pair => require (decide (pair = (value, store))) "runtime while complete closure/store resume changed"
      | other => throw (IO.userError s!"runtime while native completion failed: {reprStr other}")

def run : IO Unit := do
  template_while
  SourceCoreRecursiveNamedWhileBounds.run
  IO.println "runtime while bounds: complete template-bearing checked ledger, original bare while compiler/code, full self-cell store and resume GREEN"

end Tests.SourceCoreRecursiveNamedWhileRuntimeBounds
