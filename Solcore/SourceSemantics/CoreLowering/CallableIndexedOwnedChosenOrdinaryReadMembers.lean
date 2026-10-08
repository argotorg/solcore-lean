import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryStoredMembers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryReadMembers

/-! An initialized read and its already-produced callee post keep the positive
chosen factory at the same known index. Reported occurrence runtime views and
nominal stored Source types are related by genuine lexical receipts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryReadMembers
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CompatibleExpressionReads
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedLambdaGeneration CallableIndexedNamedGeneration
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedChosenOrdinaryStoredMembers
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)


variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {i : OrdinaryIndex compiled} {history : History i.code}
  {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {reason : Word} {code : Expr}
  (certificate : Certificate fuel (.initial compiled.compatible.checked) source scope id reason code)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {location : Dynamic.Location}
theorem read_chosen_member
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
    (binding : StaticBinding certificate context) (unique : NodeOccurrencesUnique source)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      i.mapping i.world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      i.mapping i.world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (stored : ChosenStoredAt root expressionSyntax headers keys registry faults i history heap store location)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location) :
    Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compiled.sourceProgram) context evidence
      source environment heap id (.value (.closure i.function)) heap ∧
    Evaluates actual store (code.rename ξ) (.inRight .word (CallableIndexedLambdaValues.value i.code i.captured.embedding history.native i.capturedActual)) store ∧
    FunctionCalls.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      i.mapping i.world certificate.node.type certificate.type faults (.value (.closure i.function)) (.inRight .word (CallableIndexedLambdaValues.value i.code i.captured.embedding history.native i.capturedActual)) ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      i.mapping i.world heap store ∧
    AdministrativePreserved i.mapping store i.mapping store ∧ Dynamic.HeapMetadataExtend heap heap ∧
    ChosenStoredAt root expressionSyntax headers keys registry faults i history heap store location := by
  obtain ⟨sourceTrace, nativeTrace, related, finalHeaps, frame, metadata, _⟩ :=
    CallableIndexedOwnedPreparedOrdinaryReadMembers.read_member certificate profile extension binding unique
      environments heaps locals agrees (ChosenStoredAt.stored root expressionSyntax stored) lookup
  exact ⟨sourceTrace, nativeTrace, related, finalHeaps, frame, metadata, stored⟩

/-- The actual lexical declaration and initialized cell relate the occurrence
runtime view to this known constructor's legitimate nominal Source type. -/
theorem occurrence_view
    (binding : StaticBinding certificate context)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (stored : ChosenStoredAt root expressionSyntax headers keys registry faults i history heap store location)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location) :
    SourceCoreRawMetadata.runtimeType certificate.node.type =
      SourceCoreRawMetadata.runtimeType (FunctionValues.sourceType i.function) := by
  obtain ⟨other, cell, otherLookup, otherRead, cellType, _⟩ := locals.lookup binding.declared
  have same := otherLookup.functional lookup
  subst other
  have same := otherRead.functional stored.2.choose_spec.2.1
  subst cell
  have nominal : FunctionValues.sourceType i.function = certificate.declared.scheme.body := cellType
  have view := binding.occurrence
  rw [← nominal] at view
  exact view

theorem selected_at_occurrence
    (binding : StaticBinding certificate context)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (stored : ChosenStoredAt root expressionSyntax headers keys registry faults i history heap store location)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location) :
    CallableIndexedOwnedPreparedOrdinaryLambdaValues.Selected
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := i.mapping) (world := i.world) (raw := certificate.node.type)
      (function := i.function) (native := CallableIndexedLambdaValues.value i.code i.captured.embedding history.native i.capturedActual)
      (type := CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) := by
  exact ⟨_, _, occurrence_view root expressionSyntax certificate binding locals stored lookup,
    ChosenAt.selection root expressionSyntax stored.1⟩

section Parent
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
universe u
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {childFuel : Nat}
  {compilation : SourceCoreFunctions.Context} {parentId : ExpressionId} {ids : List ExpressionId}
  {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body childFuel compilation source scope parentId id ids metadata reasonAt lowered)
  {calleeNode : ExpressionNode}
  (initial : callerProtocol.State ⟨scope, i.mapping, i.world, heap, store, canonical⟩)

theorem at_value_post_chosen
    (sameCode : compiler.calleeCode.expression = code)
    (binding : StaticBinding certificate context) (unique : NodeOccurrencesUnique source)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      i.mapping i.world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (stored : ChosenStoredAt root expressionSyntax headers keys registry faults i history heap store location)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location)
    {sourceSize : Nat} {calleeValue : Dynamic.Value} {after : Dynamic.Heap}
    {carrier : Value} {calleeStore : Store} {calleeMap : LocationMap} {calleeWorld : StoreTyping}
    (sourceTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment heap id calleeValue after)
    (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      compiler initial calleeValue after carrier calleeStore calleeMap calleeWorld) :
    CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      compiler initial calleeValue after carrier calleeStore calleeMap calleeWorld ∧
    calleeValue = (.closure i.function) ∧ after = heap ∧ carrier = (CallableIndexedLambdaValues.value i.code i.captured.embedding history.native i.capturedActual) ∧ calleeStore = store ∧
    ChosenAt root expressionSyntax headers keys registry faults
      (extendIndex i post.2.2.2.1 post.2.2.2.2.1) history := by
  obtain ⟨samePost, sameSource, sameHeap, sameNative, sameStore, _⟩ :=
    CallableIndexedOwnedPreparedOrdinaryReadMembers.at_value_post certificate bridge profile compiler initial
      sameCode binding unique environments locals agrees (ChosenStoredAt.stored root expressionSyntax stored) lookup sourceTrace post
  exact ⟨samePost, sameSource, sameHeap, sameNative, sameStore,
    ChosenAt.extend root expressionSyntax stored.1 post.2.2.2.1 post.2.2.2.2.1⟩
include evidence in
/-- The actual read type and same produced payload align this known ordinary
constructor with the parent's occurrence. Neither equation comes from a
native type or a broad representation inverse. -/
theorem selected_at_callee_post
    (sameNode : calleeNode = certificate.node)
    (sameType : compiler.calleeCode.type = certificate.type)
    (binding : StaticBinding certificate context)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      i.mapping i.world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (stored : ChosenStoredAt root expressionSyntax headers keys registry faults i history heap store location)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location)
    {calleeValue : Dynamic.Value} {after : Dynamic.Heap} {carrier : Value}
    {calleeStore : Store} {calleeMap : LocationMap} {calleeWorld : StoreTyping}
    (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      compiler initial calleeValue after carrier calleeStore calleeMap calleeWorld)
    (sameSource : calleeValue = .closure i.function)
    (sameNative : carrier = CallableIndexedLambdaValues.value i.code i.captured.embedding history.native i.capturedActual)
    (member : ChosenAt root expressionSyntax headers keys registry faults
      (extendIndex i post.2.2.2.1 post.2.2.2.2.1) history) :
    calleeValue = .closure i.function ∧
    CallableIndexedOwnedPreparedOrdinaryLambdaValues.Selected
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := calleeMap) (world := calleeWorld) (raw := calleeNode.type)
      (function := i.function) (native := carrier) (type := compiler.calleeCode.type) := by
  have view := occurrence_view root expressionSyntax certificate binding locals stored lookup
  obtain ⟨nativeType, _, _⟩ := CallableIndexedOwnedPreparedOrdinaryReadMembers.initialized_traces (evidence := evidence)
    certificate binding environments locals agrees (ChosenStoredAt.stored root expressionSyntax stored) lookup
  refine ⟨sameSource, ?_⟩
  rw [sameNode, sameNative, ← nativeType.trans sameType.symm]
  exact ⟨_, _, view, ChosenAt.selection root expressionSyntax member⟩

variable {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : Prepared compiler native)
  {sidecar : SourceCoreStageContracts.Sidecar} {sourceTypes : List TypeSystem.Ty}

def QualifiedChosenValuePrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize calleeValue after carrier calleeStore finalMap finalWorld,
    EvaluationSize nativeSize actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore ∧ nativeSize < budget ∧
    SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment heap id calleeValue after ∧
    CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
      compiler initial calleeValue after carrier calleeStore finalMap finalWorld ∧
    CallableIndexedOwnedStoredIndirectNativePrefix.GatePrefix budget prepared.site native.diagnostics.unknown compiler.resultType
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ) actual calleeStore carrier value finalStore ∧
    (∀ (function : Dynamic.Closure), calleeValue = .closure function →
      CallableIndexedOwnedPreparedOrdinaryLambdaValues.Selected
        (headers := headers) (keys := keys) (registry := registry) (faults := faults)
        (mapping := finalMap) (world := finalWorld) (raw := calleeNode.type)
        (function := function) (native := carrier) (type := compiler.calleeCode.type) ∧
      ∀ (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
          (.closure function) carrier)
        (_selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site id ids metadata
          compiler.original dispatch.row),
        CallableIndexedOwnedStoredIndirectParentPrefix.ForModel.ClosureResolutionWithEffects
          (registry := registry) (faults := faults) (context := context) (evidence := evidence)
          (calleeNode := calleeNode) (environment := environment) (actual := actual) (ξ := ξ)
          (calleeMap := finalMap) (calleeWorld := finalWorld) (calleeHeap := after)
          (calleeStore := calleeStore) (calleeSize := sourceSize) (sourceTypes := sourceTypes)
          bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
          compiler prepared initial dispatch budget value finalStore) ∧
    ∃ maps : LocationMap.Extends i.mapping finalMap, ∃ worlds : WorldExtends i.world finalWorld,
      calleeValue = .closure i.function ∧
      carrier = CallableIndexedLambdaValues.value i.code i.captured.embedding history.native i.capturedActual ∧
      ChosenAt root expressionSyntax headers keys registry faults (extendIndex i maps worlds) history

theorem at_value_prefix_chosen
    (sameCode : compiler.calleeCode.expression = code)
    (binding : StaticBinding certificate context) (unique : NodeOccurrencesUnique source)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      i.mapping i.world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (stored : ChosenStoredAt root expressionSyntax headers keys registry faults i history heap store location)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location)
    {budget : Nat} {value : Value} {finalStore : Store}
    (produced : CallableIndexedOwnedPreparedStoredIndirectParentPrefix.ValuePrefix
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
      (sourceTypes := sourceTypes) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore) :
    CallableIndexedOwnedPreparedStoredIndirectParentPrefix.ValuePrefix
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
      (sourceTypes := sourceTypes) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore ∧
    QualifiedChosenValuePrefix (i := i) (history := history) (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
      (sourceTypes := sourceTypes) (sidecar := sidecar)
      root expressionSyntax bridge profile compiler initial prepared budget value finalStore := by
  obtain ⟨nativeSize, sourceSize, calleeValue, after, carrier, calleeStore, finalMap, finalWorld,
    completed, smaller, sourceTrace, post, gate, resolver⟩ := produced
  obtain ⟨samePost, sameSource, _, sameNative, _, member⟩ :=
    at_value_post_chosen root expressionSyntax certificate bridge profile compiler initial
      sameCode binding unique environments locals agrees stored lookup sourceTrace post
  exact ⟨⟨nativeSize, sourceSize, calleeValue, after, carrier, calleeStore, finalMap, finalWorld,
      completed, smaller, sourceTrace, post, gate, resolver⟩,
    nativeSize, sourceSize, calleeValue, after, carrier, calleeStore, finalMap, finalWorld,
      completed, smaller, sourceTrace, samePost, gate, resolver, post.2.2.2.1, post.2.2.2.2.1,
      sameSource, sameNative, member⟩
end Parent

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryReadMembers
