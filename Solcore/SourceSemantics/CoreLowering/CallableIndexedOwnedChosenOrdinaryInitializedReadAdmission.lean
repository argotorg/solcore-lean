import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryInitializedReadPosts

/-! A known initialized closure read constructs success admission from the
actual deeply typed input heap. The occurrence's independent Source typing
supplies its nominal type; native runtime views do not supply that equality.
The original chosen read producer runs once and keeps the current tuple. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryInitializedReadAdmission
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


include evidence unique locals stored lookup in
/-- The actual Source judgment and initialized cell supply closure typing at
this occurrence. The original finite reference preservation lemma is reused. -/
theorem source_value_typed
    (typed : ExpressionHasType source context id certificate.node.type)
    (heapTyped : Dynamic.HeapWellTyped context heap) :
    Dynamic.ValueHasType context heap (.closure i.function) certificate.node.type := by
  generalize reportedEq : certificate.node.type = reported at typed
  cases typed with
  | @intro _ _ node raw plan contains formTyped rawEq _ _ requirements =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans certificate.metadata.found)
    subst node
    have path := requirements.outputPath
    rw [certificate.metadata.coercions] at path
    cases path
    rw [certificate.form] at formTyped
    have formTrace : Dynamic.ExpressionFormEvaluates (Program.ofChecked compiled.sourceProgram)
        context evidence source environment heap
        (.reference certificate.name (.local certificate.binder)) [] [] (.closure i.function) heap :=
      Dynamic.ExpressionFormEvaluates.local (coercions := []) rfl lookup stored.2.choose_spec.2.1 rfl rfl
    exact (Dynamic.ExpressionFormEvaluates.referencePreserves locals heapTyped formTyped formTrace).1

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

include evidence unique locals stored lookup in
/-- A pure initialized read preserves deep heap typing and every current row
at the same state. No whole-program preservation receipt is required. -/
theorem post_admission
    (typed : ExpressionHasType source context id certificate.node.type)
    (admitted : Admission bridge context initial) :
    PostAdmission bridge context certificate.node.type (.value (.closure i.function)) initial := by
  refine ⟨admitted.rows, ?_⟩
  intro result same
  cases same
  exact ⟨source_value_typed (evidence := evidence) root expressionSyntax certificate unique locals stored lookup
    typed admitted.heap, admitted.heap⟩

include extension binding unique environments heaps locals agrees stored lookup in
/-- One actual chosen read supplies the callee trace, ValuePost, positive
selection and initialized qualifier. Source and native grades stay separate. -/
theorem callee_post
    (sameCode : compiler.calleeCode.expression = code)
    (sameNode : calleeNode = certificate.node) (sameType : compiler.calleeCode.type = certificate.type)
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
    CallableIndexedOwnedChosenOrdinaryInitializedReadPosts.read_member root expressionSyntax certificate
      profile extension binding unique environments heaps locals agrees stored lookup
  have payload : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
      i.mapping i.world certificate.node.type (.closure i.function)
      (value i.code i.captured.embedding history.native i.capturedActual) certificate.type := by
    cases represented with
    | value related => exact related
  have admittedPost := post_admission (evidence := evidence) root expressionSyntax certificate unique locals stored lookup
    bridge initial sourceTyped admitted
  have selected := CallableIndexedOwnedChosenOrdinaryInitializedReadPosts.selected_at_read
    (evidence := evidence) root expressionSyntax certificate binding environments locals agrees stored lookup
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size sourceTrace
  cases sized with
  | value sized =>
    refine ⟨sourceSize, sized, ?_, ?_, retained⟩
    · unfold CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost
      rw [sameCode, sameNode, sameType]
      exact ⟨nativeTrace, payload, finalHeaps, ⟨[], by simp⟩, ⟨[], by simp⟩,
        frame, metadata, initial, callerProtocol.refl initial, admittedPost⟩
    · simpa only [sameNode, sameType] using selected

end Parent
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryInitializedReadAdmission
