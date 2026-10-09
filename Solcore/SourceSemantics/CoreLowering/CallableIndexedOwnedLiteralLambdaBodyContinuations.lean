import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenWordLiteralExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenNestedLambdaBodyContinuations
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedFunctionFinishBounds

/-! A genuine singleton return consumes the admitted Word literal at the same
chosen Support. The actual Source and native children retain their independent
grades and the reached state supplies readiness at the original tuple. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralLambdaBodyContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedPreparedMixedBodyCompilerFactory
open CallableIndexedOwnedPreparedMixedBodySiteInputs
open CallableIndexedOwnedLiteralReturnSiteShells
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedChosenWordLiteralExpressionBounds
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open TypedScopedStatements (head_fault terminal_intro)

section StaticReturn
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {statements : List StatementId} {statement : StatementId} {node : StatementNode} {expression : ExpressionId}
  {expected : TypeSystem.Ty} {type : Ty} {flow : Expr}

/-- Actual singleton Source metadata exposes the original tree child and flow.
No equality of emitted finish expressions is inverted. -/
private theorem return_child
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source
      expressionSyntax certificates definitions administrative context scope (.statements true statements) expected type flow)
    (singleton : statements = [statement])
    (found : source.lookupStatement? statement = some node)
    (form : node.form = .returnStmt (some expression)) :
    ∃ expressionNode lowered, source.lookupExpression? expression = some expressionNode ∧
      expressionNode.type = expected ∧ certificates context scope expression lowered ∧
      type = lowered.type ∧ flow = LocalLoop.returnValue lowered.type lowered.expression := by
  subst statements
  cases tree <;> simp_all
  rename_i syntaxTree body
  cases body <;> simp_all
  exact ⟨_, by assumption, rfl, rfl⟩

private theorem return_typed
    (syntaxTree : GenericImperativeMatch.Syntax source expressionSyntax context
      (.statements true statements) expected)
    (singleton : statements = [statement])
    (found : source.lookupStatement? statement = some node)
    (form : node.form = .returnStmt (some expression)) :
    ExpressionHasType source context expression expected := by
  subst statements
  cases syntaxTree <;> try simp_all
  rename_i body
  cases body <;> simp_all

private theorem return_transfers
    {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {finalContext : SourceSemantics.Context} {control : Dynamic.ControlOutcome} {size : Nat}
    {faults : FunctionCalls.FaultRep} {escaped : Word}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? statement = some node)
    (form : node.form = .returnStmt (some expression))
    (trace : RecursiveNamedLoopContracts.ExecutesAt size true program context evidence source
      environment before [statement] finalContext control after) :
    ImperativeFunctionFinish.TransferFaults faults escaped control := by
  obtain ⟨_, _, outcome, _, same, _⟩ :=
    RecursiveNamedLexicalTreeSourceBounds.returning unique found form trace
  rw [same]
  cases outcome <;> simp [ImperativeFunctionFinish.TransferFaults]

end StaticReturn

universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (literalRoot : LiteralRootReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (literalId : ExpressionId) (node : ExpressionNode)
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
    sourceContext evidence scope id lowered)
  (chosen : ChosenFactory literalRoot.root (approved literalId) receipt)
  (capturedEnvironment : Dynamic.Environment)
  (facts : WordNodeFacts (caller := caller) literalId node)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (currentContext : SourceSemantics.Context) (currentEvidence : Dynamic.EvidenceEnvironment)
  (ledger : currentContext.solvedRequirements = (context compiled.indexed caller.named).solvedRequirements)
  (runtime : RuntimeRequirementLedgerValid currentContext)
  {statement : StatementId} {statementNode : StatementNode}
  (found : (receipt.formation.function capturedEnvironment).source.lookupStatement? statement = some statementNode)
  (form : statementNode.form = .returnStmt (some literalId))
  {childScope : SourceCoreLocalCell.Scope} {child : SourceCoreBasic.LoweredExpr}
  (actual : (receipt.formation.support capturedEnvironment).certificates
    (receipt.formation.support capturedEnvironment).body.readFuel
    (receipt.formation.function capturedEnvironment).source currentContext childScope literalId child)
  (typed : ExpressionHasType (receipt.formation.function capturedEnvironment).source currentContext literalId node.type)
  {expected : TypeSystem.Ty} (valueType : node.type = expected)
  {administrative : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  (condition : Location → CallableIndexedHistory.NativeFrame → Prop)

include chosen facts ledger runtime found form actual typed valueType in
/-- The finite return joins one genuine admitted expression child. -/
theorem return_flow_preserves
    (unique : NodeOccurrencesUnique (receipt.formation.function capturedEnvironment).source) (size : Nat) :
    RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      callerProtocol (readiness bridge) condition (fun _ _ _ _ => True) functions
      (Program.ofChecked compiled.sourceProgram) currentEvidence (fun _ => True)
      (source := (receipt.formation.function capturedEnvironment).source) (context := currentContext)
      (registry := registry) (faults := faults) (administrative := administrative)
      (frameLayout := frameLayout) (globals := globals) size (scope := childScope) true [statement]
      expected child.type (LocalLoop.returnValue child.type child.expression) := by
  intro _valid _facts mapping world actualContext environment canonical native before after store ξ
    contextLocation nativeFrame outcome finalContext environments heaps locals agrees nativeTyped reference read unmapped
    initial _condition admitted trace
  obtain ⟨sameContext, childSize, childOutcome, childTrace, sameOutcome, _smaller⟩ :=
    RecursiveNamedLexicalTreeSourceBounds.returning unique found form trace
  subst finalContext
  subst outcome
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, transition⟩ :=
    CallableIndexedOwnedAdmittedLexicalReadiness.preserves_at bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (preserves_at_support (registry := registry) (faults := faults) literalRoot literalId node receipt chosen capturedEnvironment facts
        bridge functions currentContext currentEvidence ledger runtime unique childSize)
      actual facts.found typed environments heaps locals agrees nativeTyped initial admitted childTrace
  cases represented with
  | value payload =>
    exact ⟨_, finalStore, finalMap, finalWorld,
      by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_success _ evaluated,
      .returned (valueType ▸ payload), finalHeaps, maps, worlds, frame, metadata,
      ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩,
      ⟨transition.choose, transition.choose_spec.1, transition.choose_spec.2.1⟩⟩
  | fault matched =>
    cases childTrace with | fault _failed =>
      exact ⟨_, finalStore, finalMap, finalWorld,
        by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_failure _ evaluated,
        .fault matched, finalHeaps, maps, worlds, frame, metadata,
        ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, transition⟩

include chosen facts ledger runtime found form actual typed valueType in
/-- Native inversion uses the original strict child and constructs Source size
independently at the same reached state. -/
theorem return_flow_reflects (size : Nat) :
    RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      callerProtocol (readiness bridge) condition (fun _ _ _ _ => True) functions
      (Program.ofChecked compiled.sourceProgram) currentEvidence (fun _ => True)
      (source := (receipt.formation.function capturedEnvironment).source) (context := currentContext)
      (registry := registry) (faults := faults) (administrative := administrative)
      (frameLayout := frameLayout) (globals := globals) size (scope := childScope) true [statement]
      expected child.type (LocalLoop.returnValue child.type child.expression) := by
  intro _valid _facts mapping world actualContext environment canonical native before store finalStore ξ
    contextLocation nativeFrame value environments heaps locals agrees nativeTyped reference read unmapped
    initial _condition admitted evaluated
  rw [LoopRenaming.returnValue] at evaluated
  obtain ⟨childSize, middleStore, input, _smaller, childEvaluation⟩ := evaluated.bind_computation
  obtain ⟨sourceSize, childOutcome, after, finalMap, finalWorld, childTrace, represented,
      finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
    CallableIndexedOwnedAdmittedLexicalReadiness.reflects_at bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (reflects_at_support (registry := registry) (faults := faults) literalRoot literalId node receipt chosen capturedEnvironment facts
        bridge functions currentContext currentEvidence ledger runtime childSize)
      actual facts.found typed environments heaps locals agrees nativeTyped initial admitted childEvaluation
  cases represented with
  | fault matched =>
    cases childTrace with | fault failed =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.returnValue_failure _ childEvaluation.sound)
      have sourceTrace := head_fault true [] (.returnValue (lookupStatement?_sound found) form failed.sound)
      obtain ⟨flowSize, sized⟩ := RecursiveNamedLoopContracts.ExecutesAt.has_size sourceTrace
      exact ⟨flowSize, currentContext, _, after, finalMap, finalWorld, sized, .fault matched,
        finalHeaps, maps, worlds, frame, metadata,
        ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, transition⟩
  | value payload =>
    cases childTrace with | value childTrace =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.returnValue_success _ childEvaluation.sound)
      have sourceTrace := terminal_intro true [] (lookupStatement?_sound found)
        (by intro expression; simp [form]) (.returnValue (lookupStatement?_sound found) form childTrace.sound) (.returned _)
      obtain ⟨flowSize, sized⟩ := RecursiveNamedLoopContracts.ExecutesAt.has_size sourceTrace
      exact ⟨flowSize, currentContext, _, after, finalMap, finalWorld, sized, .returned (valueType ▸ payload),
        finalHeaps, maps, worlds, frame, metadata,
        ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩,
        ⟨transition.choose, transition.choose_spec.1, transition.choose_spec.2.1⟩⟩


section SupportReturn
variable
  (singleton : (receipt.formation.function capturedEnvironment).body = [statement])
  (bodyLedger : (receipt.formation.support capturedEnvironment).body.context.solvedRequirements =
    (context compiled.indexed caller.named).solvedRequirements)
  (bodyRuntime : RuntimeRequirementLedgerValid (receipt.formation.support capturedEnvironment).body.context)

include chosen facts found form singleton bodyLedger bodyRuntime in
/-- The genuine selected tree supplies its original child and Source typing. -/
theorem support_flow_preserves (size : Nat) :
    RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      callerProtocol (readiness bridge) condition (fun _ _ _ _ => True) functions
      (Program.ofChecked compiled.sourceProgram) (receipt.formation.function capturedEnvironment).evidence (fun _ => True)
      (source := (receipt.formation.function capturedEnvironment).source)
      (context := (receipt.formation.support capturedEnvironment).body.context)
      (registry := registry) (faults := faults) (administrative := administrative)
      (frameLayout := frameLayout) (globals := globals) size
      (scope := (receipt.formation.code capturedEnvironment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      true (receipt.formation.function capturedEnvironment).body (receipt.formation.function capturedEnvironment).resultType
      (receipt.formation.code capturedEnvironment).receipt.resultCore (receipt.formation.support capturedEnvironment).body.flow := by
  have tree := (receipt.formation.support capturedEnvironment).body.tree
  have syntaxTree := (receipt.formation.support capturedEnvironment).body.syntaxTree
  obtain ⟨other, output, outputFound, sourceType, certified, coreType, flowEq⟩ := return_child tree singleton found form
  have sameNode := Option.some.inj (outputFound.symm.trans facts.found)
  subst other
  have sourceTyped := return_typed syntaxTree singleton found form
  have expressionTyped : ExpressionHasType (receipt.formation.function capturedEnvironment).source
      (receipt.formation.support capturedEnvironment).body.context literalId node.type := by
    rw [sourceType]
    exact sourceTyped
  simpa only [singleton, coreType, flowEq] using return_flow_preserves literalRoot literalId node receipt chosen capturedEnvironment
    facts bridge functions (receipt.formation.support capturedEnvironment).body.context
    (receipt.formation.function capturedEnvironment).evidence bodyLedger bodyRuntime found form certified
    expressionTyped sourceType condition (receipt.formation.support capturedEnvironment).body.unique size

include chosen facts found form singleton bodyLedger bodyRuntime in
/-- The same static tree supplies native reflection at its original flow. -/
theorem support_flow_reflects (size : Nat) :
    RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      callerProtocol (readiness bridge) condition (fun _ _ _ _ => True) functions
      (Program.ofChecked compiled.sourceProgram) (receipt.formation.function capturedEnvironment).evidence (fun _ => True)
      (source := (receipt.formation.function capturedEnvironment).source)
      (context := (receipt.formation.support capturedEnvironment).body.context)
      (registry := registry) (faults := faults) (administrative := administrative)
      (frameLayout := frameLayout) (globals := globals) size
      (scope := (receipt.formation.code capturedEnvironment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      true (receipt.formation.function capturedEnvironment).body (receipt.formation.function capturedEnvironment).resultType
      (receipt.formation.code capturedEnvironment).receipt.resultCore (receipt.formation.support capturedEnvironment).body.flow := by
  have tree := (receipt.formation.support capturedEnvironment).body.tree
  have syntaxTree := (receipt.formation.support capturedEnvironment).body.syntaxTree
  obtain ⟨other, output, outputFound, sourceType, certified, coreType, flowEq⟩ := return_child tree singleton found form
  have sameNode := Option.some.inj (outputFound.symm.trans facts.found)
  subst other
  have sourceTyped := return_typed syntaxTree singleton found form
  have expressionTyped : ExpressionHasType (receipt.formation.function capturedEnvironment).source
      (receipt.formation.support capturedEnvironment).body.context literalId node.type := by
    rw [sourceType]
    exact sourceTyped
  simpa only [singleton, coreType, flowEq] using return_flow_reflects literalRoot literalId node receipt chosen capturedEnvironment
    facts bridge functions (receipt.formation.support capturedEnvironment).body.context
    (receipt.formation.function capturedEnvironment).evidence bodyLedger bodyRuntime found form certified
    expressionTyped sourceType condition size

section Entry
variable
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {mapping : LocationMap} {world : StoreTyping} {actualEnvironment : Environment}
  (captured : Captures compiled.indexed mapping world scope
    (receipt.formation.function capturedEnvironment).captured actualEnvironment)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) caller)
  (history : History (receipt.formation.code capturedEnvironment))
  (origin : SourceOrigin (receipt.formation.support capturedEnvironment) history)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (first : State headers keys ⟨callerScope, mapping, world, before, store, canonical⟩)
  (beforeTyped : Dynamic.HeapWellTyped (receipt.formation.function capturedEnvironment).context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes (receipt.formation.function capturedEnvironment).context
    before arguments (receipt.formation.support capturedEnvironment).body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows first)

include chosen facts found form singleton bodyLedger bodyRuntime origin observed beforeTyped argumentsTyped stable in
/-- Genuine parameter admission and the finite literal flow feed the original
finish once, retaining the same nested packet and whole pool. -/
theorem source_at_entry (size : Nat)
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt capturedEnvironment captured prefixContext) (receipt.formation.code capturedEnvironment) history (receipt.formation.support capturedEnvironment).body.toBody.toContext functions registry arguments nativeArguments before store owner.key.frameLocation
      (first.rows owner.position).authority.current (first.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = (receipt.formation.code capturedEnvironment).receipt.loweredParameters.length)
    (spine : entry.entry.canonical = added ++ captured.canonical)
    (reached : State headers keys ⟨((receipt.formation.code capturedEnvironment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope), entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) size (receipt.formation.function capturedEnvironment) (receipt.formation.support capturedEnvironment).body.context
      entry.entry.environment entry.entry.heap outcome after) :
    ∃ packet value finalStore finalMap finalWorld,
      Evaluates entry.entry.actualBody entry.entry.store ((receipt.formation.code capturedEnvironment).receipt.body.rename entry.entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld (receipt.formation.function capturedEnvironment).resultType (receipt.formation.code capturedEnvironment).receipt.resultCore faults outcome value ∧ CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.entry.mapping finalMap ∧ WorldExtends entry.entry.world finalWorld ∧
      AdministrativePreserved entry.entry.mapping entry.entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.entry.heap after ∧
      TypedMixedNamedBody.ReachedExit compiled.compatible.checked compiled.indexed.layouts.definitions finalMap finalWorld
        (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) (Program.ofChecked compiled.sourceProgram) (receipt.formation.function capturedEnvironment) (receipt.formation.support capturedEnvironment).body.context ((receipt.formation.code capturedEnvironment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
        entry.entry.environment entry.entry.heap after outcome ∧
      ProtectedStateTransition.FunctionFinish.Reached (readiness (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)) (receipt.formation.support capturedEnvironment).body.context outcome
        ⟨reached, packet⟩ ⟨((receipt.formation.code capturedEnvironment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope), finalMap, finalWorld, after, finalStore, entry.entry.canonical⟩ := by
  obtain ⟨packet, source, rows⟩ := CallableIndexedOwnedChosenNestedLambdaBodyContinuations.source_parameter_admission
    (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt capturedEnvironment captured prefixContext)
    (receipt.formation.code capturedEnvironment) history (receipt.formation.support capturedEnvironment) origin
    functions owner observed rfl first beforeTyped argumentsTyped stable entry added length spine reached
  let nested : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State _ := ⟨reached, packet⟩
  have admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)
      (receipt.formation.support capturedEnvironment).body.context nested := ⟨source.heapTyped, rows⟩
  have gate : CallableIndexedOwnedAllocationProducer.StableOwner keys owner.key.frameLocation entry.next :=
    ⟨owner.position, _, _, rfl, entry.nextHistory⟩
  have transfers : ∀ {sourceSize finalContext control after},
      RecursiveNamedLoopContracts.ExecutesAt sourceSize true (Program.ofChecked compiled.sourceProgram)
        (receipt.formation.support capturedEnvironment).body.context
        (receipt.formation.function capturedEnvironment).evidence
        (receipt.formation.function capturedEnvironment).source
        entry.entry.environment entry.entry.heap (receipt.formation.function capturedEnvironment).body finalContext control after →
      ImperativeFunctionFinish.TransferFaults faults (receipt.formation.code capturedEnvironment).compilation.internalReason control := by
    intro sourceSize finalContext control after executed
    have executed' : RecursiveNamedLoopContracts.ExecutesAt sourceSize true (Program.ofChecked compiled.sourceProgram)
        (receipt.formation.support capturedEnvironment).body.context
        (receipt.formation.function capturedEnvironment).evidence
        (receipt.formation.function capturedEnvironment).source entry.entry.environment entry.entry.heap [statement] finalContext control after := by
      simpa only [singleton] using executed
    exact return_transfers (receipt.formation.support capturedEnvironment).body.unique found form executed'
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, post⟩ :=
    RecursiveNamedFunctionFinishBounds.WithReady.preserves_at_emitted_with_state_when_with_transfers
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (functions := functions) (program := Program.ofChecked compiled.sourceProgram)
      (tree := (receipt.formation.support capturedEnvironment).body.tree)
      (projection := (receipt.formation.support capturedEnvironment).body.projection)
      (unique := (receipt.formation.support capturedEnvironment).body.unique)
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (readiness (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) (fun _ _ _ _ => True)
      (receipt.formation.support capturedEnvironment).body.emitted (fun _ => True) size
      (support_flow_preserves literalRoot literalId node receipt chosen capturedEnvironment facts
        (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) functions found form
        (CallableIndexedOwnedAllocationProducer.StableOwner keys) singleton bodyLedger bodyRuntime size)
      trivial trivial entry.entry.environments entry.entry.heaps entry.entry.locals entry.entry.lookups
      entry.entry.actualTyped entry.entry.reference entry.entry.read entry.entry.unmapped nested gate admitted transfers trace
  exact ⟨packet, value, finalStore, finalMap, finalWorld, evaluated, represented, heaps,
    maps, worlds, frame, metadata, exit, post⟩

include chosen facts found form singleton bodyLedger bodyRuntime origin observed beforeTyped argumentsTyped stable in
/-- Native finish exposes a strict real flow child, which reflects into an
independently sized Source body at the same reached packet. -/
theorem native_at_entry (size : Nat)
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt capturedEnvironment captured prefixContext) (receipt.formation.code capturedEnvironment) history (receipt.formation.support capturedEnvironment).body.toBody.toContext functions registry arguments before store owner.key.frameLocation
      (first.rows owner.position).authority.current)
    (reached : State headers keys ⟨((receipt.formation.code capturedEnvironment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope), entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size entry.actual entry.store ((receipt.formation.code capturedEnvironment).receipt.body.rename entry.embedding) value finalStore) :
    ∃ packet sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) sourceSize (receipt.formation.function capturedEnvironment) (receipt.formation.support capturedEnvironment).body.context
        entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld (receipt.formation.function capturedEnvironment).resultType (receipt.formation.code capturedEnvironment).receipt.resultCore faults outcome value ∧ CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit compiled.compatible.checked compiled.indexed.layouts.definitions finalMap finalWorld
        (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) (Program.ofChecked compiled.sourceProgram) (receipt.formation.function capturedEnvironment) (receipt.formation.support capturedEnvironment).body.context ((receipt.formation.code capturedEnvironment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
        entry.environment entry.heap after outcome ∧
      ProtectedStateTransition.FunctionFinish.Reached (readiness (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)) (receipt.formation.support capturedEnvironment).body.context outcome
        ⟨reached, packet⟩ ⟨((receipt.formation.code capturedEnvironment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope), finalMap, finalWorld, after, finalStore, entry.canonical⟩ := by
  obtain ⟨packet, source, rows⟩ := CallableIndexedOwnedChosenNestedLambdaBodyContinuations.native_parameter_admission
    (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt capturedEnvironment captured prefixContext)
    (receipt.formation.code capturedEnvironment) history (receipt.formation.support capturedEnvironment) origin
    functions owner observed rfl first beforeTyped argumentsTyped stable entry reached
  let nested : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State _ := ⟨reached, packet⟩
  have admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)
      (receipt.formation.support capturedEnvironment).body.context nested := ⟨source.heapTyped, rows⟩
  have gate : CallableIndexedOwnedAllocationProducer.StableOwner keys owner.key.frameLocation entry.next :=
    ⟨owner.position, _, _, rfl, entry.nextHistory⟩
  have transfers : ∀ {sourceSize finalContext control after},
      RecursiveNamedLoopContracts.ExecutesAt sourceSize true (Program.ofChecked compiled.sourceProgram)
        (receipt.formation.support capturedEnvironment).body.context
        (receipt.formation.function capturedEnvironment).evidence
        (receipt.formation.function capturedEnvironment).source
        entry.environment entry.heap (receipt.formation.function capturedEnvironment).body finalContext control after →
      ImperativeFunctionFinish.TransferFaults faults (receipt.formation.code capturedEnvironment).compilation.internalReason control := by
    intro sourceSize finalContext control after executed
    have executed' : RecursiveNamedLoopContracts.ExecutesAt sourceSize true (Program.ofChecked compiled.sourceProgram)
        (receipt.formation.support capturedEnvironment).body.context
        (receipt.formation.function capturedEnvironment).evidence
        (receipt.formation.function capturedEnvironment).source entry.environment entry.heap [statement] finalContext control after := by
      simpa only [singleton] using executed
    exact return_transfers (receipt.formation.support capturedEnvironment).body.unique found form executed'
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, post⟩ :=
    RecursiveNamedFunctionFinishBounds.WithReady.reflects_at_emitted_with_state_when_with_transfers
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (functions := functions) (program := Program.ofChecked compiled.sourceProgram)
      (tree := (receipt.formation.support capturedEnvironment).body.tree)
      (projection := (receipt.formation.support capturedEnvironment).body.projection)
      (unique := (receipt.formation.support capturedEnvironment).body.unique)
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (readiness (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) (fun _ _ _ _ => True)
      (receipt.formation.support capturedEnvironment).body.emitted (fun _ => True) (size+1) size (Nat.le_succ size)
      (fun child _ => support_flow_reflects literalRoot literalId node receipt chosen capturedEnvironment facts
        (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) functions found form
        (CallableIndexedOwnedAllocationProducer.StableOwner keys) singleton bodyLedger bodyRuntime child)
      trivial trivial entry.environments entry.heaps entry.locals entry.lookups
      entry.actualTyped entry.reference entry.read entry.unmapped nested gate admitted transfers completed
  exact ⟨packet, sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps,
    maps, worlds, frame, metadata, exit, post⟩

include chosen facts found form singleton bodyLedger bodyRuntime origin observed beforeTyped argumentsTyped stable in
/-- A finite projection retains the actual returned nested state and relates
its full pool to the original base continuation. -/
theorem source_continuation (budget : Nat) :
    CallableIndexedOwnedLambdaEntryBodyContracts.SourceContinuation
      (registry := registry) (faults := faults) (arguments := arguments) (nativeArguments := nativeArguments)
      (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt capturedEnvironment captured prefixContext)
      (receipt.formation.code capturedEnvironment) history
      (receipt.formation.support capturedEnvironment).body.toBody.toContext functions owner first budget := by
  intro entry added length spine reached size _strict outcome after trace
  obtain ⟨packet, value, finalStore, finalMap, finalWorld, evaluated, represented, heaps,
      maps, worlds, frame, metadata, exit, post⟩ :=
    source_at_entry (literalRoot := literalRoot) (literalId := literalId) (node := node) (receipt := receipt)
      (chosen := chosen) (capturedEnvironment := capturedEnvironment) (facts := facts) (functions := functions)
      (found := found) (form := form) (singleton := singleton) (bodyLedger := bodyLedger) (bodyRuntime := bodyRuntime)
      (owner := owner) (captured := captured) (prefixContext := prefixContext) (history := history)
      (origin := origin) (observed := observed) (first := first) (beforeTyped := beforeTyped)
      (argumentsTyped := argumentsTyped) (stable := stable) size entry added length spine reached trace
  obtain ⟨returned, related⟩ := post.forget
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps,
    maps, worlds, frame, metadata, exit, returned.val,
    (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller).related related⟩

include chosen facts found form singleton bodyLedger bodyRuntime origin observed beforeTyped argumentsTyped stable in
/-- The native continuation keeps its independently sized Source result and
projects the same returned nested state without changing protocol. -/
theorem native_continuation (budget : Nat) :
    CallableIndexedOwnedLambdaEntryBodyContracts.NativeContinuation
      (registry := registry) (faults := faults) (arguments := arguments)
      (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt capturedEnvironment captured prefixContext)
      (receipt.formation.code capturedEnvironment) history
      (receipt.formation.support capturedEnvironment).body.toBody.toContext functions owner first budget := by
  intro entry reached size _strict value finalStore completed
  obtain ⟨packet, sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps,
      maps, worlds, frame, metadata, exit, post⟩ :=
    native_at_entry (literalRoot := literalRoot) (literalId := literalId) (node := node) (receipt := receipt)
      (chosen := chosen) (capturedEnvironment := capturedEnvironment) (facts := facts) (functions := functions)
      (found := found) (form := form) (singleton := singleton) (bodyLedger := bodyLedger) (bodyRuntime := bodyRuntime)
      (owner := owner) (captured := captured) (prefixContext := prefixContext) (history := history)
      (origin := origin) (observed := observed) (first := first) (beforeTyped := beforeTyped)
      (argumentsTyped := argumentsTyped) (stable := stable) size entry reached completed
  obtain ⟨returned, related⟩ := post.forget
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps,
    maps, worlds, frame, metadata, exit, returned.val,
    (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller).related related⟩

end Entry
end SupportReturn
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralLambdaBodyContinuations
