import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaValues
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryReadMembers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredFunctionModelReceipts

/-! An actual initialized local read uses the chosen function model and keeps
its known positive member. Callee association transports an already produced
tuple; it supplies no classifier for prior values or later heap mutations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryInitializedReadPosts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CompatibleExpressionReads
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedChosenOrdinaryStoredMembers (ChosenAt ChosenStoredAt extendIndex)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : CallableIndexedNamedGeneration.Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {i : OrdinaryIndex compiled} {history : History i.code}
  {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {reason : Word} {code : Expr}
  (certificate : Certificate fuel (.initial compiled.compatible.checked) source scope id reason code)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {location : Dynamic.Location}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  (binding : StaticBinding certificate context) (unique : NodeOccurrencesUnique source)
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    i.mapping i.world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
    i.mapping i.world heap store)
  (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (stored : ChosenStoredAt root expressionSyntax headers keys registry faults i history heap store location)
  (lookup : Dynamic.Environment.LooksUp environment certificate.binder location)

include extension binding unique environments heaps locals agrees stored lookup in
/-- The original generic read core runs once at the actual receiving model.
The initialized cell derives its reached empty-cell policy internally. -/
theorem read_member :
    Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compiled.sourceProgram) context evidence
      source environment heap id (.value (.closure i.function)) heap ∧
    Evaluates actual store (code.rename ξ)
      (.inRight .word (value i.code i.captured.embedding history.native i.capturedActual)) store ∧
    FunctionCalls.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile))
      i.mapping i.world certificate.node.type certificate.type faults (.value (.closure i.function))
      (.inRight .word (value i.code i.captured.embedding history.native i.capturedActual)) ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
      i.mapping i.world heap store ∧
    AdministrativePreserved i.mapping store i.mapping store ∧ Dynamic.HeapMetadataExtend heap heap ∧
    ChosenStoredAt root expressionSyntax headers keys registry faults i history heap store location := by
  have initialized := ChosenStoredAt.stored root expressionSyntax stored
  obtain ⟨_, sourceTrace, nativeTrace⟩ :=
    CallableIndexedOwnedPreparedOrdinaryReadMembers.initialized_traces certificate binding environments locals agrees initialized lookup
  obtain ⟨outcome, after, result, finalStore, actualSource, actualNative, related, finalHeaps, frame, metadata⟩ :=
    certificate.evaluates_with_diagnostics
      (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
      extension (Program.ofChecked compiled.sourceProgram) context evidence binding environments heaps locals agrees
      (CallableIndexedOwnedPreparedOrdinaryReadMembers.initialized_policy certificate initialized lookup)
  obtain ⟨sameResult, sameStore⟩ := evaluation_deterministic actualNative nativeTrace
  subst result
  subst finalStore
  obtain ⟨sameOutcome, sameHeap⟩ := source_outcome_unique unique
    (lookupExpression?_sound certificate.metadata.found) certificate.form certificate.metadata.coercions
    lookup initialized.2.choose_spec.2.1 rfl actualSource (.value sourceTrace)
  subst outcome
  subst after
  exact ⟨actualSource, actualNative, related, finalHeaps, frame, metadata, stored⟩

include evidence binding environments locals agrees stored lookup in
/-- The literal stored constructor supplies positive selection. Its nominal
cell type is related to the reported occurrence by the lexical certificate. -/
theorem selected_at_read :
    CallableIndexedOwnedChosenOrdinaryLambdaValues.Selected
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := i.mapping) (world := i.world) (raw := certificate.node.type)
      (function := i.function) (native := value i.code i.captured.embedding history.native i.capturedActual)
      (type := certificate.type) root expressionSyntax := by
  have view := CallableIndexedOwnedChosenOrdinaryReadMembers.occurrence_view
    root expressionSyntax certificate binding locals stored lookup
  obtain ⟨sameType, _, _⟩ := CallableIndexedOwnedPreparedOrdinaryReadMembers.initialized_traces
    (evidence := evidence) certificate binding environments locals agrees (ChosenStoredAt.stored root expressionSyntax stored) lookup
  rw [← sameType]
  exact ⟨_, _, view, .chosen_ordinary i history stored.1⟩

section Parent
universe u
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {childFuel : Nat}
  {parentCompilation : SourceCoreFunctions.Context} {parentId : ExpressionId} {ids : List ExpressionId}
  {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body childFuel parentCompilation source scope parentId id ids metadata reasonAt lowered)
  {calleeNode : ExpressionNode}
  (initial : callerProtocol.State ⟨scope, i.mapping, i.world, heap, store, canonical⟩)

include extension binding unique environments heaps locals agrees stored lookup in
/-- A real read supplies its whole callee post and current admission. Source
grading comes from that actual trace, independently of the native evaluation. -/
theorem callee_post
    (sameCode : compiler.calleeCode.expression = code)
    (sameNode : calleeNode = certificate.node) (sameType : compiler.calleeCode.type = certificate.type)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (covers : evidence.Covers context)
    (sourceTyped : ExpressionHasType source context id certificate.node.type)
    (admitted : Admission bridge context initial) :
    ∃ sourceSize,
      SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment heap id (.closure i.function) heap ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
        (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
        bridge (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
        compiler initial (.closure i.function) heap
        (value i.code i.captured.embedding history.native i.capturedActual) store i.mapping i.world ∧
      CallableIndexedOwnedChosenOrdinaryLambdaValues.Selected
        (headers := headers) (keys := keys) (registry := registry) (faults := faults)
        (mapping := i.mapping) (world := i.world) (raw := calleeNode.type)
        (function := i.function) (native := value i.code i.captured.embedding history.native i.capturedActual)
        (type := compiler.calleeCode.type) root expressionSyntax ∧
      ChosenStoredAt root expressionSyntax headers keys registry faults i history heap store location := by
  obtain ⟨sourceTrace, nativeTrace, represented, finalHeaps, frame, metadata, retained⟩ :=
    read_member root expressionSyntax certificate profile extension binding unique environments heaps locals agrees stored lookup
  have payload : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
      i.mapping i.world certificate.node.type (.closure i.function)
      (value i.code i.captured.embedding history.native i.capturedActual) certificate.type := by
    cases represented with
    | value related => exact related
  have admittedPost := after_expression initial initial admitted wellFormed runtime covers locals sourceTyped sourceTrace frame
  have selected := selected_at_read (evidence := evidence) root expressionSyntax certificate binding environments locals agrees stored lookup
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size sourceTrace
  cases sized with
  | value sized =>
    refine ⟨sourceSize, sized, ?_, ?_, retained⟩
    · unfold CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost
      rw [sameCode, sameNode, sameType]
      exact ⟨nativeTrace, payload, finalHeaps, ⟨[], by simp⟩, ⟨[], by simp⟩,
        frame, metadata, initial, callerProtocol.refl initial, admittedPost⟩
    · simpa only [sameNode, sameType] using selected

include binding unique environments locals agrees stored lookup in
/-- Association consumes the already produced callee tuple. Only the actual
read witnesses and deterministic payload equations transport its qualifier. -/
theorem at_value_post
    (sameCode : compiler.calleeCode.expression = code)
    {sourceSize : Nat} {calleeValue : Dynamic.Value} {after : Dynamic.Heap}
    {carrier : Value} {calleeStore : Store} {calleeMap : LocationMap} {calleeWorld : StoreTyping}
    (sourceTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment heap id calleeValue after)
    (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
      bridge (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
      compiler initial calleeValue after carrier calleeStore calleeMap calleeWorld) :
    CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
      bridge (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
      compiler initial calleeValue after carrier calleeStore calleeMap calleeWorld ∧
    calleeValue = .closure i.function ∧ after = heap ∧
    carrier = value i.code i.captured.embedding history.native i.capturedActual ∧ calleeStore = store ∧
    ChosenAt root expressionSyntax headers keys registry faults
      (extendIndex i post.2.2.2.1 post.2.2.2.2.1) history := by
  have initialized := ChosenStoredAt.stored root expressionSyntax stored
  obtain ⟨_, expectedSource, expectedNative⟩ :=
    CallableIndexedOwnedPreparedOrdinaryReadMembers.initialized_traces certificate binding environments locals agrees initialized lookup
  have actualNative := post.1
  rw [sameCode] at actualNative
  obtain ⟨sameResult, sameStore⟩ := evaluation_deterministic actualNative expectedNative
  have sameNative : carrier = value i.code i.captured.embedding history.native i.capturedActual := (Value.inRight.inj sameResult).2
  obtain ⟨sameSource, sameHeap⟩ := source_outcome_unique unique
    (lookupExpression?_sound certificate.metadata.found) certificate.form certificate.metadata.coercions
    lookup initialized.2.choose_spec.2.1 rfl (.value sourceTrace.sound) (.value expectedSource)
  exact ⟨post, Dynamic.ExpressionOutcome.value.inj sameSource, sameHeap, sameNative, sameStore,
    ChosenAt.extend root expressionSyntax stored.1 post.2.2.2.1 post.2.2.2.2.1⟩

end Parent
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryInitializedReadPosts
