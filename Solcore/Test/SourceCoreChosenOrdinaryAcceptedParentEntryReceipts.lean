import Solcore.Test.SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedPairArgumentBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryInitializedReadAdmission
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderScopeDeclarations
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualReads

/-! The retained parent and chosen closure share one original root. Its actual
argument acceptance supplies the pair, and its actual reference acceptance
supplies the initialized callee post at the current caller state. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedParentEntryReceipts
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open CallableIndexedNamedGeneration CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedLiteralReturnSiteShells CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission


private def named_compilation (fixture : AcceptedFixture) {named target : Named}
    (same : named = target)
    (compilation : Compilation fixture.packet.compiled.indexed named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode) :
    Compilation fixture.packet.compiled.indexed target
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode := by
  cases same
  exact compilation

private def named_root (fixture : AcceptedFixture) {named target : Named}
    (same : named = target)
    {compilation : Compilation fixture.packet.compiled.indexed named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
    (root : LiteralRootReceipt (compiled := fixture.packet.compiled) named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode compilation
      498 (source fixture.packet.named) (initialScope fixture.packet) (expressionId fixture.packet 1)
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) fixture.calls.initializer) :
    LiteralRootReceipt (compiled := fixture.packet.compiled) target
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode
      (named_compilation fixture same compilation)
      498 (source fixture.packet.named) (initialScope fixture.packet) (expressionId fixture.packet 1)
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) fixture.calls.initializer := by
  cases same
  exact root

private theorem named_policy (fixture : AcceptedFixture) {named target : Named}
    (same : named = target)
    {compilation : Compilation fixture.packet.compiled.indexed named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
    (root : LiteralRootReceipt (compiled := fixture.packet.compiled) named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode compilation
      498 (source fixture.packet.named) (initialScope fixture.packet) (expressionId fixture.packet 1)
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) fixture.calls.initializer) :
    (named_root fixture same root).root.selected.policy = root.root.selected.policy ∧
      (named_root fixture same root).root.selected.lowerBody = root.root.selected.lowerBody := by
  cases same
  exact ⟨rfl, rfl⟩

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  (atHeader : HeaderAt fixture caller)
  {compilation : Compilation fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller compilation)
  (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt fixture root)

/-- Only the authentic Header named index is transported. -/
def fixture_compilation : Compilation fixture.packet.compiled.indexed fixture.packet.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode :=
  named_compilation fixture atHeader.named compilation

/-- This is the supplied root after the same dependent named-index transport. -/
def fixture_root : LiteralRootReceipt (compiled := fixture.packet.compiled) fixture.packet.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode
    (fixture_compilation fixture atHeader (compilation := compilation))
    498 (source fixture.packet.named) (initialScope fixture.packet) (expressionId fixture.packet 1)
    (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) fixture.calls.initializer := named_root fixture atHeader.named root

private theorem action_eq (fuel : Nat) (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) :
    SourceCoreFunctions.lowerExpressionWithPolicy
      (fixture_root fixture atHeader root).root.selected.policy
      (fixture_root fixture atHeader root).root.selected.lowerBody fuel
      (context fixture.packet.compiled.indexed fixture.packet.named) (source fixture.packet.named) scope id
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) =
    SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody fuel
      (context fixture.packet.compiled.indexed caller.named) (source fixture.packet.named) scope id
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) := by
  obtain ⟨policy, body⟩ := named_policy fixture atHeader.named root
  rw [show (fixture_root fixture atHeader root).root.selected.policy = root.root.selected.policy from policy,
    show (fixture_root fixture atHeader root).root.selected.lowerBody = root.root.selected.lowerBody from body,
    congrArg (context fixture.packet.compiled.indexed) atHeader.named]

section Pair
universe u
variable {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (metadata : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture) (evidence : Dynamic.EvidenceEnvironment)

include metadata in
/-- Actual parent497 singleton acceptance identifies the same selected tuple.
Its admitted meanings retain the arbitrary actual receiving model. -/
theorem pair_at_chosen_parent :
    ∃ pair : SourceCoreChosenOrdinaryAcceptedPairArgumentBounds.PairReceipt fixture (fixture_root fixture atHeader root),
      chosen.parent.compiler.codes = [pair.tuple] ∧
      DataExpressionSequence.Tree (source fixture.packet.named)
        (SourceCoreChosenOrdinaryAcceptedPairArgumentBounds.Tuple fixture (fixture_root fixture atHeader root) pair) (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture)
        [expressionId fixture.packet 6] [parameterType] [pair.tuple] ∧
      (∀ size, CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
        (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named)
        (SourceCoreChosenOrdinaryAcceptedPairArgumentBounds.Tuple fixture (fixture_root fixture atHeader root) pair) faults size) ∧
      (∀ size, CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
        (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named)
        (SourceCoreChosenOrdinaryAcceptedPairArgumentBounds.Tuple fixture (fixture_root fixture atHeader root) pair) faults size) := by
  have accepted : SourceCoreFunctions.lowerExpressionWithPolicy
      (fixture_root fixture atHeader root).root.selected.policy
      (fixture_root fixture atHeader root).root.selected.lowerBody 498
      (context fixture.packet.compiled.indexed fixture.packet.named) (source fixture.packet.named)
      (SourceCoreChosenOrdinaryAcceptedPairArgumentBounds.parentScope fixture) (expressionId fixture.packet 5) (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) = .ok fixture.calls.parent := by
    exact (action_eq fixture atHeader root 498 (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture) (expressionId fixture.packet 5)).trans chosen.parent.accepted
  obtain ⟨pair, preserves, reflects⟩ := SourceCoreChosenOrdinaryAcceptedPairArgumentBounds.at_parent fixture (fixture_root fixture atHeader root)
    bridge functions metadata evidence (registry := registry) (faults := faults) accepted
  have tupleAccepted := pair.tupleAccepted
  change SourceCoreFunctions.lowerExpressionWithPolicy
    (fixture_root fixture atHeader root).root.selected.policy
    (fixture_root fixture atHeader root).root.selected.lowerBody 497
    (context fixture.packet.compiled.indexed fixture.packet.named) (source fixture.packet.named)
    (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture) (expressionId fixture.packet 6)
    (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) = .ok pair.tuple at tupleAccepted
  rw [action_eq fixture atHeader root 497 (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture) (expressionId fixture.packet 6)] at tupleAccepted
  have arguments := chosen.parent.compiler.argumentsAccepted
  simp only [List.mapM_cons, List.mapM_nil, tupleAccepted, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at arguments
  have tree := DataExpressionSequence.Tree.single fixture.graph.argumentFound
    (show SourceCoreChosenOrdinaryAcceptedPairArgumentBounds.Tuple fixture (fixture_root fixture atHeader root) pair (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture)
      (expressionId fixture.packet 6) pair.tuple from ⟨rfl, rfl, rfl⟩)
  exact ⟨pair, arguments.symm, by simpa only [metadata.argumentType] using tree, preserves, reflects⟩

end Pair

private theorem empty_owned : SourceCompilationPlan.ordinaryOwnedRequirements? fixture.graph.callee = some [] := by
  unfold SourceCompilationPlan.ordinaryOwnedRequirements?
  rw [fixture.parentRows.calleeRequirements, fixture.parentRows.calleeCoercions]
  rfl

include atHeader in
/-- Finite reference inversion retains the original root's fixed read fuel. -/
private theorem callee_read_receipts :
    SourceCoreCompatibleDataExpressions.readExpression fixture.packet.compiled.compatible.checked
      (source fixture.packet.named) (expressionId fixture.packet 9) =
        .ok (fixture.graph.callee, chosen.parent.compiler.calleeCode.type) ∧
    SourceCoreCompatibleDataExpressions.lowerRead fixture.packet.compiled.indexed.fuel
      (.initial fixture.packet.compiled.compatible.checked) (source fixture.packet.named)
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture) (expressionId fixture.packet 9)
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture (expressionId fixture.packet 9)) = .ok chosen.parent.compiler.calleeCode.expression := by
  let normalized := fixture_root fixture atHeader root
  have pointwise := SourceCoreChosenOrdinaryAcceptedStaticInventory.ordinary_policy normalized.root
    (childScope := SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture) fixture.graph.calleeFound
    (.inl ⟨_, _, fixture.graph.calleeForm, fixture.parentRows.generalized⟩)
    (empty_owned fixture) fixture.parentRows.calleeCoercions (.inl fixture.parentRows.calleeRequirements)
    fixture.parentRows.calleeOrdinary
  have accepted : SourceCoreFunctions.lowerExpressionWithPolicy normalized.root.selected.policy normalized.root.selected.lowerBody 497
      (context fixture.packet.compiled.indexed fixture.packet.named) (source fixture.packet.named)
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture) (expressionId fixture.packet 9)
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture) = .ok chosen.parent.compiler.calleeCode :=
    (action_eq fixture atHeader root 497 (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture) (expressionId fixture.packet 9)).trans chosen.parent.compiler.calleeAccepted
  have owner : (expressionId fixture.packet 9).occurrence.owner = (source fixture.packet.named).owner := rfl
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, fixture.graph.calleeFound, fixture.graph.calleeForm, bind, Except.bind,
    pure, Except.pure] at accepted
  have bypass := pointwise.special (fun budget childSource childScope childId childReasonAt =>
    SourceCoreFunctions.lowerExpressionWithPolicy normalized.root.selected.policy normalized.root.selected.lowerBody
      (min budget 496) (context fixture.packet.compiled.indexed fixture.packet.named)
      childSource childScope childId childReasonAt) 497
  cases hook : normalized.root.selected.policy.lowerSpecial? <;> simp only [hook] at accepted bypass
  all_goals simp only [SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason] at accepted bypass
  all_goals
    try rw [bypass] at accepted
    rw [pointwise.read] at accepted
    cases read : SourceCoreCompatibleDataExpressions.readExpression fixture.packet.compiled.compatible.checked
        (source fixture.packet.named) (expressionId fixture.packet 9) with
    | error error => simp [read] at accepted
    | ok pair =>
      obtain ⟨node, type⟩ := pair
      have same := Option.some.inj ((CompatibleExpressionReads.metadata_of_read read).found.symm.trans fixture.graph.calleeFound)
      subst node
      simp only [read, fixture.graph.calleeForm] at accepted
      rw [normalized.lowerRead] at accepted
      cases generated : SourceCoreCompatibleDataExpressions.lowerRead fixture.packet.compiled.indexed.fuel
          (.initial fixture.packet.compiled.compatible.checked) (source fixture.packet.named)
          (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture) (expressionId fixture.packet 9)
          (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason fixture (expressionId fixture.packet 9)) with
      | error error =>
        simp only [SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason] at generated
        simp [generated] at accepted
      | ok expression =>
        simp only [SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentReason] at generated
        simp only [generated, Except.ok.injEq] at accepted
        have typeEq := congrArg SourceCoreBasic.LoweredExpr.type accepted
        have exprEq := congrArg SourceCoreBasic.LoweredExpr.expression accepted
        exact ⟨congrArg (fun t => Except.ok (fixture.graph.callee, t)) typeEq, congrArg Except.ok exprEq⟩

private theorem binder_declared : fixture.graph.binder ∈ SourceCoreDataPlaces.declaredBinders (source fixture.packet.named) := by
  apply List.mem_append.mpr
  apply Or.inr
  apply List.mem_flatMap.mpr
  refine ⟨.statement fixture.graph.initialized, (lookupStatement?_sound fixture.graph.initializedFound).1, ?_⟩
  simp only [fixture.graph.initializedForm]
  exact List.mem_singleton_self _

include atHeader in
/-- The original Header parameter scope and genuine outer let extension supply
the actual reference declaration, independently of native projection. -/
theorem parent_declarations (metadata : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture) :
    CompatibleExpressionReads.ScopeDeclarations (source fixture.packet.named) (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture)
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) := by
  have initial := RecursiveNamedHeaderScopeDeclarations.header_scope
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed)
    (values := .initial fixture.packet.compiled.compatible.checked)
    (prepared := fixture.packet.compiled.indexed.ancestry)
    (program := Program.ofChecked fixture.packet.compiled.sourceProgram) caller
  have declarations : CompatibleExpressionReads.ScopeDeclarations (source fixture.packet.named)
      (initialScope fixture.packet) (runtimeContext fixture.packet) := by
    simpa only [atHeader.source, atHeader.context, atHeader.bindings,
      RecursiveNamedCatalogNativeContexts.bodyScope, initialScope] using initial
  exact RecursiveNamedHeaderScopeDeclarations.scope_bind fixture.calls.payload
    (binder_declared fixture) declarations metadata.extended

section Callee
universe u
variable {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (metadata : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture) (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
  (evidence : Dynamic.EvidenceEnvironment)
  {i : CallableIndexedOwnedPreparedRuntimeFamilyMembers.OrdinaryIndex fixture.packet.compiled}
  {history : History i.code} {administrative : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {location : Dynamic.Location}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial fixture.packet.compiled.compatible.checked).registry registry)
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog fixture.packet.compiled.compatible.checked.catalog)
    i.mapping i.world administrative (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture) environment canonical fixture.packet.compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry
    (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root
      (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts)
    i.mapping i.world heap store)
  (locals : Dynamic.EnvironmentAgrees heap (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture).locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (stored : CallableIndexedOwnedChosenOrdinaryStoredMembers.ChosenStoredAt root.root
    (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults i history heap store location)
  (lookup : Dynamic.Environment.LooksUp environment fixture.graph.binder.id location)
  (initial : callerProtocol.State ⟨SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture, i.mapping, i.world, heap, store, canonical⟩)
  (admitted : Admission bridge (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) initial)

include atHeader metadata extension environments heaps locals agrees stored lookup admitted in
/-- One original initialized-read producer returns the genuine callee trace,
full post and positive selection at the same input state and stored member. -/
theorem callee_at_parent :
    ∃ sourceSize,
      SourceExecutionSize.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram) sourceSize
        (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named) environment heap
        (expressionId fixture.packet 9) (.closure i.function) heap ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry) (actual := actual) (ξ := ξ)
        (calleeNode := chosen.parent.compiler.calleeNode) (context := SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
        bridge (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root
          (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts)
        chosen.parent.compiler initial (.closure i.function) heap
        (value i.code i.captured.embedding history.native i.capturedActual) store i.mapping i.world ∧
      CallableIndexedOwnedChosenOrdinaryLambdaValues.Selected
        (headers := headers) (keys := keys) (registry := registry) (faults := faults)
        (mapping := i.mapping) (world := i.world) (raw := chosen.parent.compiler.calleeNode.type)
        (function := i.function) (native := value i.code i.captured.embedding history.native i.capturedActual)
        (type := chosen.parent.compiler.calleeCode.type) root.root
        (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) ∧
      CallableIndexedOwnedChosenOrdinaryStoredMembers.ChosenStoredAt root.root
        (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults i history heap store location := by
  obtain ⟨read, generated⟩ := callee_read_receipts fixture atHeader root chosen
  have sourceTyped : ExpressionHasType (source fixture.packet.named) (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
      (expressionId fixture.packet 9) fixture.graph.callee.type := by
    simpa only [metadata.calleeType] using SourceCoreChosenOrdinaryAcceptedOuterTyping.callee_typed metadata
  obtain ⟨certificate, typeEq, binding⟩ := CompatibleExpressionReads.loweredRead_of_accepted generated read
    fixture.runtime.source_runtime.graph.nodeOccurrencesUnique (parent_declarations fixture atHeader metadata) sourceTyped
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans fixture.graph.calleeFound)
  have formEq := certificate.form.symm.trans (nodeEq ▸ fixture.graph.calleeForm)
  have binderEq := (ExpressionForm.reference.inj formEq).2
  have pointwise := SourceCoreChosenOrdinaryAcceptedStaticInventory.ordinary_policy
    (fixture_root fixture atHeader root).root (childScope := SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture) fixture.graph.calleeFound
    (.inl ⟨_, _, fixture.graph.calleeForm, fixture.parentRows.generalized⟩) (empty_owned fixture)
    fixture.parentRows.calleeCoercions (.inl fixture.parentRows.calleeRequirements) fixture.parentRows.calleeOrdinary
  have policyEq := (named_policy fixture atHeader.named root).1
  have actualRead := chosen.parent.compiler.calleeRead
  have readPolicy : root.root.selected.policy.readExpression (source fixture.packet.named) (expressionId fixture.packet 9) =
      SourceCoreCompatibleDataExpressions.readExpression fixture.packet.compiled.compatible.checked (source fixture.packet.named) (expressionId fixture.packet 9) := by
    rw [← policyEq]
    exact pointwise.read
  have sameRead := actualRead.symm.trans (readPolicy.trans read)
  have sameNode : chosen.parent.compiler.calleeNode = certificate.node :=
    (Prod.mk.inj (Except.ok.inj sameRead)).1.trans nodeEq.symm
  have actualLookup : Dynamic.Environment.LooksUp environment certificate.binder location := by
    have sameBinder := ReferenceResolution.local.inj binderEq
    exact sameBinder.symm ▸ lookup
  exact CallableIndexedOwnedChosenOrdinaryInitializedReadAdmission.callee_post
    root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) certificate inventory.contracts
    extension binding fixture.runtime.source_runtime.graph.nodeOccurrencesUnique environments heaps locals agrees stored actualLookup
    bridge chosen.parent.compiler initial rfl sameNode typeEq.symm (nodeEq.symm ▸ sourceTyped) admitted

end Callee
end Tests.SourceCoreChosenOrdinaryAcceptedParentEntryReceipts
