import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewSemanticReceipt
import Solcore.SourceSemantics.CoreLowering.BuiltinNamedBodyMeaning
import Solcore.Test.SourceCoreCallableLambdaViewBuiltinBodyTree

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody.SemanticReceipt.mk
#check_failure Solcore.SourceSemantics.CoreLowering.CallableLambdaViewSemanticReceipt.Receipt.mk
/-! Actual view compilation supplies a certificate; independent canonical
source traces and completed native runs consume its transported semantic
receipt. No canonical compiler equation or body meaning is supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCallableLambdaViewSemanticReceipt
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatiblePayload GeneralHeap ReadOnly CompatibleExpressionBuiltins CallableIndexedHistory
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"lambda_view_semantics", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "lambda_view_semantics.solc"⟩, 0, 1⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def literalNode : ExpressionNode := {
  id := id 0, span, type := .word, form := .literal (.decimal "7")}
private def toNode : ExpressionNode := {
  id := id 1, span, type := BuiltinFunctionId.wordToInteger.type,
  form := .reference "wordToInteger" (.builtinFunction .wordToInteger)}
private def innerNode : ExpressionNode := {
  id := id 2, span, type := .integer, form := .call (id 1) [id 0] (.builtinFunction .wordToInteger)}
private def fromNode : ExpressionNode := {
  id := id 3, span, type := BuiltinFunctionId.wordFromInteger.type,
  form := .reference "wordFromInteger" (.builtinFunction .wordFromInteger)}
private def outerNode : ExpressionNode := {
  id := id 4, span, type := .word, form := .call (id 3) [id 2] (.builtinFunction .wordFromInteger)}
private def groupNode : ExpressionNode := {id := id 5, span, type := .word, form := .group (id 4)}
private def returned : StatementNode := ⟨⟨⟨owner, 10⟩⟩, span, .word, .returnStmt (some (id 5))⟩
private def parent : ExpressionNode := {
  id := id 6, span, type := .function .unit .word,
  form := .lambda [] .word [returned.id]}
private def source : TypedSource := {
  owner, inputs := [], roots := [.statement returned.id], nodes := [.expression literalNode, .expression toNode,
    .expression innerNode, .expression fromNode, .expression outerNode, .expression groupNode, .statement returned, .expression parent]}
private theorem checkExists : (SourceCoreCompatibleCatalog.prepare signatures 10 [.word, .integer]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [.word, .integer]).toOption.get checkExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reasonAt : ExpressionId → Word := fun _ => Word.zero
private def policy (native : SourceCoreGeneralFunctions.CallableContext) : SourceCoreFunctions.Policy :=
  {SourceCoreCompatibleDataExpressions.functionPolicy 100 values with callables := SourceCoreGeneralFunctions.callablePolicy (some native) []}
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private def view : TypedSource := SourceCoreEvidence.withNode source {parent with type := .unit}
private theorem edited : CallableLambdaViewEdits.LocalView source view [parent.id] :=
  CallableLambdaViewEdits.withNode unique (by cbv) rfl rfl
private def footprint : List NodeId := [.expression (id 0), .expression (id 1), .expression (id 2),
  .expression (id 3), .expression (id 4), .expression (id 5), .statement returned.id]
private theorem avoids : CallableLambdaBodyReachability.Avoids source [.statement returned.id] [parent.id] := by
  have subset {node : NodeId} (reached : CallableLambdaBodyReachability.Reaches source [.statement returned.id] node) :
      node ∈ footprint := by
    induction reached with
    | root member =>
      simp only [List.mem_singleton] at member
      subst_vars
      simp [footprint]
    | expression _ found edge ih =>
      simp [footprint] at ih
      rcases ih with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        have selected := Option.some.inj ((by rfl : source.lookupExpression? _ = some _).symm.trans found)
        subst_vars
        simp only [literalNode, toNode, innerNode, fromNode, outerNode, groupNode,
          ExpressionForm.references, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at edge <;>
          rcases edge with rfl | rfl <;> simp [footprint, id]
    | statement _ found edge ih =>
      simp [footprint] at ih
      subst_vars
      have selected := Option.some.inj ((by rfl : source.lookupStatement? returned.id = some returned).symm.trans found)
      subst_vars
      simp [returned, StatementForm.references] at edge
      subst_vars
      simp [footprint]
  intro expression member reached
  simp only [List.mem_singleton] at member
  subst expression
  have impossible := subset reached
  simp [footprint, parent, id] at impossible
private theorem wordAdmitted : TypeAdmissible context .word := .word (.ofSignatures signatures)
private theorem integerAdmitted : TypeAdmissible context .integer := .integer (.ofSignatures signatures)
private theorem literalTyped : ExpressionHasType source context (id 0) .word := by
  apply ExpressionHasType.ofOrdinary (node := literalNode) (rawType := .word) (lookupExpression?_sound (by rfl))
    (.literal (.intro (numericLiteralValue?_sound (value := 7) (by rfl)))) wordAdmitted wordAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem innerTyped : ExpressionHasType source context (id 2) .integer := by
  apply ExpressionHasType.ofOrdinary (node := innerNode) (rawType := .integer) (lookupExpression?_sound (by cbv))
    (.builtinCall (.intro (lookupExpression?_sound (node := toNode) (by cbv)) rfl rfl rfl rfl)
      (.cons literalTyped (.nil _))) integerAdmitted integerAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem outerTyped : ExpressionHasType source context (id 4) .word := by
  apply ExpressionHasType.ofOrdinary (node := outerNode) (rawType := .word) (lookupExpression?_sound (by cbv))
    (.builtinCall (.intro (lookupExpression?_sound (node := fromNode) (by cbv)) rfl rfl rfl rfl)
      (.cons innerTyped (.nil _))) wordAdmitted wordAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem groupTyped : ExpressionHasType source context (id 5) .word := by
  apply ExpressionHasType.ofOrdinary (node := groupNode) (rawType := .word) (lookupExpression?_sound (by cbv))
    (.group outerTyped) wordAdmitted wordAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem literalSyntax : CompatibleExpressionGeneral.Syntax source (id 0) :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := literalNode) (by rfl) (.word _)))))))
private theorem innerSyntax : Syntax source (id 2) :=
  .builtin (node := innerNode) (by cbv) rfl (by intro child member; simp only [List.mem_singleton] at member; subst child; exact .fragment literalSyntax)
private theorem outerSyntax : Syntax source (id 4) :=
  .builtin (node := outerNode) (by cbv) rfl (by intro child member; simp only [List.mem_singleton] at member; subst child; exact innerSyntax)
private theorem syntaxTree : Syntax source (id 5) := .group (node := groupNode) (by cbv) rfl outerSyntax
private theorem noCoercions : ∀ expression node, view.lookupExpression? expression = some node → node.coercions = [] := by
  intro expression node found
  have member := (lookupExpression?_sound found).1
  have shape : view.nodes = [.expression literalNode, .expression toNode, .expression innerNode,
    .expression fromNode, .expression outerNode, .expression groupNode, .statement returned,
    .expression {parent with type := .unit}] := by rfl
  simp only [shape, List.mem_cons, List.not_mem_nil, or_false, Node.expression.injEq, reduceCtorEq, false_or] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private def functions (ambient : AmbientDefinitions checked.catalog.definitions) : FunctionModel checked.catalog ambient where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def identities : Dynamic.Value → Word → Prop := fun _ _ => False
private theorem faithful : DataEquality.IdentityFaithful identities := ⟨fun impossible => False.elim impossible, fun impossible => False.elim impossible⟩
private theorem functionLeaves (ambient : AmbientDefinitions checked.catalog.definitions) : CompatibleEquality.FunctionObservations checked.catalog (functions ambient) identities := fun impossible => False.elim impossible
private theorem functionTypes (ambient : AmbientDefinitions checked.catalog.definitions) : FunctionRuntimeViews (functions ambient) := fun impossible => False.elim impossible
private def faults : FunctionCalls.FaultRep := fun reason token =>
  (∃ location, reason = .uninitializedLocation location ∧ token = Word.zero) ∨
  (∃ key value tag, MetadataRep values.registry (.mapping key value) tag ∧ reason = .missingMappingDefault value ∧ token = Word.zero.add tag)
private theorem uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id) :=
  fun _ location => .inl ⟨location, rfl, rfl⟩
private theorem missing : ∀ id key value tag, MetadataRep values.registry (.mapping key value) tag →
  faults (.missingMappingDefault value) ((reasonAt id).add tag) :=
  fun _ key value tag owned => .inr ⟨key, value, tag, owned, rfl, rfl⟩
private theorem valid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, Context.ofSignatures]
  · intro requirement member; cases member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member; cases member
private theorem innerTrace : Dynamic.ExpressionEvaluatesOutcome program context [] source [] ⟨[]⟩ (id 2) (.value (.integer 7)) ⟨[]⟩ :=
  BuiltinCalls.source_intro (checked := checked) (type := .integer) ⟨by cbv, rfl, rfl, rfl, rfl⟩ rfl
    (.apply (.cons (.intro (lookupExpression?_sound (node := literalNode) (by rfl))
      (.literal rfl (.word (numericLiteralValue?_sound (value := 7) (by rfl)))) .nil) .nil)
      (.value (.builtin (.wordToInteger (Word.ofNatModulo 7)))))
private theorem outerTrace : Dynamic.ExpressionEvaluatesOutcome program context [] source [] ⟨[]⟩ (id 4) (.value (.word (Word.ofNatModulo 7))) ⟨[]⟩ := by
  cases innerTrace with
  | value evaluated =>
    exact BuiltinCalls.source_intro (checked := checked) (type := .word)
      ⟨by cbv, rfl, rfl, rfl, rfl⟩ rfl (.apply (.cons evaluated .nil) (.value (.builtin (.wordFromInteger 7))))
private theorem sourceTrace : Dynamic.ExpressionEvaluatesOutcome program context [] source [] ⟨[]⟩ (id 5) (.value (.word (Word.ofNatModulo 7))) ⟨[]⟩ := by
  cases outerTrace with
  | value evaluated => exact .value (.intro (lookupExpression?_sound (node := groupNode) (by cbv)) (.group rfl evaluated) .nil)

private def statements : List StatementId := [returned.id]
private theorem statementSyntax : BuiltinLexicalStatements.Syntax source context true statements .word :=
  .returnValue (node := returned) [] (by cbv) rfl rfl (by cbv) rfl groupTyped syntaxTree
private theorem viewSyntax : BuiltinLexicalStatements.Syntax view context true statements .word :=
  CallableLambdaViewSourceTyping.body_syntax edited avoids unique statementSyntax

private def onError (_ : SourceCoreAllocationLayouts.Error) : SourceCoreBasic.Error := .traversalExhausted (.declaration owner)
private def loopPolicy (native : SourceCoreGeneralFunctions.CallableContext)
    (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat) : SourceCoreLoops.Policy := {
  lowerExpression := fun fuel source scope id reasonAt => SourceCoreFunctions.lowerExpressionWithPolicy (policy native) noBody fuel compilation source scope id reasonAt
  readStatement := SourceCoreCompatibleDataExpressions.readStatement checked
  lowerBinder := SourceCoreCompatibleDataExpressions.lowerBinder checked
  sourceCells := some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt ⟨owner, []⟩ [] onError)) }

private theorem certified (native : SourceCoreGeneralFunctions.CallableContext)
    {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout} {globals fuel : Nat} {code : Expr}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (loopPolicy native layouts frame globals) fuel view []
      statements .word reasonAt true Word.zero = .ok code) :
    BuiltinLexicalStatements.Tree layouts ⟨owner, []⟩ [] frame globals onError 100 values view [] reasonAt context [] true statements .word .word code := by
  apply GenericLexicalStatements.tree_of_flow rfl (by intros; rfl) rfl ?_ viewSyntax rfl rfl rfl
    (by intro actual declared index native selected; cases selected) rfl accepted
  intro current currentClosed currentResidual currentSignatures scope budget expression expressionNode lowered declarations syntaxValue found typed generated
  exact CompatibleExpressionBuiltins.tree_of_functions (edited.metadata.unique unique) declarations currentSignatures currentClosed currentResidual
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ native [] rfl
    (fun _ _ _ found => noCoercions _ _ found) syntaxValue found typed generated

private theorem statementTrace : TypedScopedStatements.Executes true program context [] source [] ⟨[]⟩
    statements context (.returned (.word (Word.ofNatModulo 7))) ⟨[]⟩ := by
  cases sourceTrace with
  | value child =>
    exact TypedScopedStatements.terminal_intro true [] (lookupStatement?_sound (node := returned) (by cbv))
      (by intro expression; simp [returned]) (.returnValue (lookupStatement?_sound (by cbv)) rfl child) (.returned _)

private def closure : Dynamic.Closure := ⟨[], .word, statements, source, [], context, []⟩
private theorem bodyTrace : FunctionCallBody.Trace program closure context [] ⟨[]⟩
    (.value (.word (Word.ofNatModulo 7))) ⟨[]⟩ := by
  cases statementTrace with
  | control executed => exact .returned executed

/-- The real finish/body traversal supplies the sealed static certificate.
The independent source trace is not a field of that certificate. -/
theorem accepted_view_certificate (native : SourceCoreGeneralFunctions.CallableContext)
    {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (loopPolicy native layouts frame globals) fuel
      view [] statements .word reasonAt Word.zero Word.zero = .ok code) :
    Nonempty (BuiltinNamedBody.Certificate layouts ⟨owner, []⟩ [] frame globals onError 100 values view context []
      reasonAt [] statements .word .word (loopPolicy native layouts frame globals) fuel Word.zero Word.zero code) := by
  have original := accepted
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  cases generated : SourceCoreLoops.lowerFlowStatementsWithPolicy (loopPolicy native layouts frame globals) fuel
      view [] statements .word reasonAt true Word.zero with
  | error error =>
    rw [generated] at accepted
    change (Except.error error : Except SourceCoreLoops.Error Expr) = .ok code at accepted
    cases accepted
  | ok flow =>
    simp [generated] at accepted
    cases accepted
    exact BuiltinNamedBody.of_tree original rfl viewSyntax rfl (certified native generated)

theorem accepted_view_preserves (native : SourceCoreGeneralFunctions.CallableContext)
    {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (loopPolicy native layouts frame globals) fuel
      view [] statements .word reasonAt Word.zero Word.zero = .ok code)
    {mapping world administrative actualContext canonical actual store ξ contextLocation current}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry (functions ambient) mapping world ⟨[]⟩ store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame current))
    (unmapped : contextLocation ∉ mapping) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked values.registry (functions ambient))
        finalMap finalWorld .word .word faults (.value (.word (Word.ofNatModulo 7))) value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry (functions ambient) finalMap finalWorld ⟨[]⟩ finalStore ∧
      AdministrativePreserved mapping store finalMap finalStore := by
  obtain ⟨actual⟩ := accepted_view_certificate native accepted
  let receipt := CallableLambdaViewSemanticReceipt.of_certificate (statements := statements) edited avoids unique actual
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, preserved, metadata, reached⟩ :=
    BuiltinNamedBody.SemanticReceipt.preserves (function := closure) (values := values) (ambient := ambient) (registry := values.registry) (functions ambient) (.refl _) definitions registered program valid unique uninitialized missing
      faithful (functionLeaves ambient) (functionTypes ambient) receipt.canonical environments heaps .nil agrees typed reference read unmapped bodyTrace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, preserved⟩

/-- Whole finish completion constructs its independent source body trace.
Neither a native child evaluation nor a universal body meaning is assumed. -/
theorem accepted_view_reflects (native : SourceCoreGeneralFunctions.CallableContext)
    {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (loopPolicy native layouts frame globals) fuel
      view [] statements .word reasonAt Word.zero Word.zero = .ok code)
    {mapping world administrative actualContext canonical actual store ξ contextLocation current value finalStore}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry (functions ambient) mapping world ⟨[]⟩ store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame current))
    (unmapped : contextLocation ∉ mapping)
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program closure context [] ⟨[]⟩ outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked values.registry (functions ambient))
        finalMap finalWorld .word .word faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry (functions ambient) finalMap finalWorld after finalStore ∧
      AdministrativePreserved mapping store finalMap finalStore := by
  obtain ⟨actual⟩ := accepted_view_certificate native accepted
  let receipt := CallableLambdaViewSemanticReceipt.of_certificate (statements := statements) edited avoids unique actual
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, preserved, metadata, reached⟩ :=
    BuiltinNamedBody.SemanticReceipt.reflects (function := closure) (values := values) (ambient := ambient) (registry := values.registry) (functions ambient) (.refl _) definitions registered program valid unique uninitialized missing
      faithful (functionLeaves ambient) (functionTypes ambient) receipt.canonical environments heaps .nil agrees typed reference read unmapped completed
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, preserved⟩


/-- The actual accepted equation is still at the changed view. -/
theorem actual_view_retained (native : SourceCoreGeneralFunctions.CallableContext)
    {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (loopPolicy native layouts frame globals) fuel
      view [] statements .word reasonAt Word.zero Word.zero = .ok code) :
    source ≠ view ∧ ∃ receipt : CallableLambdaViewSemanticReceipt.Receipt layouts ⟨owner, []⟩ [] frame globals onError
      100 values source view context [] reasonAt [] statements .word .word (loopPolicy native layouts frame globals)
      fuel Word.zero Word.zero code,
      SourceCoreLoops.lowerStatementsWithPolicy (loopPolicy native layouts frame globals) fuel
        view [] statements .word reasonAt Word.zero Word.zero = .ok code ∧
      receipt.canonical.flow = receipt.actual.flow := by
  obtain ⟨actual⟩ := accepted_view_certificate native accepted
  let receipt := CallableLambdaViewSemanticReceipt.of_certificate (statements := statements) edited avoids unique actual
  exact ⟨by decide, receipt, receipt.accepted, receipt.sameFlow⟩

def run : IO Unit := do
  Tests.SourceCoreCallableLambdaViewBuiltinBodyTree.run
  IO.println "lambda view semantic receipts: canonical builtin body preservation/reflection retain actual view acceptance GREEN"

end Tests.SourceCoreCallableLambdaViewSemanticReceipt
