import Solcore.SourceSemantics.CoreLowering.Internal.Owned.DecodedCallFaults
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CallRejection
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ChosenLambdaFormation
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryMembers
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ReadyContinuations
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallEvidence
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredIndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LiteralReturns
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralRuntime
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.PublicExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.AssignmentHeads
import Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderCoupledReadyBounds

/-!
# Owned callables: chosen ordinary calls

Staged public call faults, and the receipts, dispatch and posts of calls from chosen ordinary rows.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDecodedStagedCallFaults
/-! One literal public diagnostic table interprets semantic assignment/arity
failures and scoped first-call-gate failures. The failure constructor chooses
the view; an equal raw runtime error never changes the original failure tag.
These adapters retain the same payload model, value and reached indices. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDecodedStagedCallFaults
open Core Frontend SourceInference GeneralHeap CompatiblePayload

def faults (table : SourceCoreFaultSites.Table) : RecursiveStageMeaning.FaultRep :=
  fun failure token => match failure with
    | .semantic reason => CallableIndexedOwnedPublicDecodedCallFaults.faults table reason token
    | .stage invocation call reason =>
        CallableIndexedOwnedPreparedReceivingFirstCallGateRejection.stagedFaults table
          (.stage invocation call reason) token

/-- A semantic producer keeps its original tag at this exact public table. -/
theorem of_semantic {table : SourceCoreFaultSites.Table}
    {failure : Staging.Recursive.Failure} {token : Word}
    (represented : CallableIndexedOwnedPublicDecodedCallFaults.stagedSemanticFaults table failure token) :
    faults table failure token := by
  cases failure with
  | semantic reason => exact represented
  | stage invocation call reason => exact False.elim represented

/-- A scoped first-gate producer retains the failing invocation and call. -/
theorem of_first_gate {table : SourceCoreFaultSites.Table}
    {failure : Staging.Recursive.Failure} {token : Word}
    (represented : CallableIndexedOwnedPreparedReceivingFirstCallGateRejection.stagedFaults table failure token) :
    faults table failure token := by
  cases failure with
  | semantic reason => exact False.elim represented
  | stage invocation call reason => exact represented

theorem of_assignment {table : SourceCoreFaultSites.Table} {reason : Dynamic.SemanticFault}
    {token : Word}
    (represented : CallableIndexedOwnedPublicDecodedAssignmentFaults.faults table reason token) :
    faults table (.semantic reason) token :=
  CallableIndexedOwnedPublicDecodedCallFaults.of_assignment represented

theorem of_arity {table : SourceCoreFaultSites.Table} {failure : Staging.Recursive.Failure}
    {token : Word}
    (represented : CallableIndexedOwnedPreparedSecondCallGateRejection.stagedArityFaults table failure token) :
    faults table failure token :=
  of_semantic (CallableIndexedOwnedPublicDecodedCallFaults.of_staged_arity represented)

/-- Every interpretation still supplies the literal decoder equation. -/
theorem decoded {table : SourceCoreFaultSites.Table} {failure : Staging.Recursive.Failure}
    {token : Word} (represented : faults table failure token) :
    ∃ diagnostic, table.diagnostic? token = some diagnostic := by
  cases failure with
  | semantic reason =>
    obtain ⟨diagnostic, lookup, _view⟩ := represented
    exact ⟨diagnostic, lookup⟩
  | stage invocation call reason =>
    obtain ⟨diagnostic, lookup, _view⟩ := represented
    exact ⟨diagnostic, lookup⟩

section Results
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
  {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty} {type : Ty}
  {table : SourceCoreFaultSites.Table} {outcome : Staging.Recursive.Outcome} {value : Value}

theorem semantic_result
    (represented : RecursiveStageMeaning.ResultRepresentsFor model mapping world sourceType type
      (CallableIndexedOwnedPublicDecodedCallFaults.stagedSemanticFaults table) outcome value) :
    RecursiveStageMeaning.ResultRepresentsFor model mapping world sourceType type (faults table) outcome value := by
  cases represented with
  | value payload => exact .value payload
  | fault matched => exact .fault (of_semantic matched)

theorem first_gate_result
    (represented : RecursiveStageMeaning.ResultRepresentsFor model mapping world sourceType type
      (CallableIndexedOwnedPreparedReceivingFirstCallGateRejection.stagedFaults table) outcome value) :
    RecursiveStageMeaning.ResultRepresentsFor model mapping world sourceType type (faults table) outcome value := by
  cases represented with
  | value payload => exact .value payload
  | fault matched => exact .fault (of_first_gate matched)

theorem arity_result
    (represented : RecursiveStageMeaning.ResultRepresentsFor model mapping world sourceType type
      (CallableIndexedOwnedPreparedSecondCallGateRejection.stagedArityFaults table) outcome value) :
    RecursiveStageMeaning.ResultRepresentsFor model mapping world sourceType type (faults table) outcome value := by
  cases represented with
  | value payload => exact .value payload
  | fault matched => exact .fault (of_arity matched)

end Results
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDecodedStagedCallFaults
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryReadMembers
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinarySelectedCallReceipts
/-! The known chosen callee stays at one actual post and selected row.
Successful argument receipts extend that same positive index and retain the
current pool and complete fourth bind. Body construction remains in the
existing chosen continuation and invocation producers. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinarySelectedCallReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedChosenOrdinaryFormedMembers (FactoryMember)
open CallableIndexedOwnedChosenOrdinaryStoredMembers
open CallableIndexedOwnedIndirectSourceAdapters
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {rootCompilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode rootCompilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)



/-- All payload equations and the chosen constructor belong to this known index. -/
def CalleeAt
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (i : OrdinaryIndex compiled) (history : History i.code)
    (raw : TypeSystem.Ty) (sourceValue : Dynamic.Value) (carrier : Value) (type : Ty) : Prop :=
  sourceValue = .closure i.function ∧
  carrier = CallableIndexedLambdaValues.value i.code i.captured.embedding history.native i.capturedActual ∧
  ChosenAt root expressionSyntax headers keys registry faults i history ∧
  CallableIndexedOwnedPreparedOrdinaryLambdaValues.Selected
    (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    (mapping := i.mapping) (world := i.world) (raw := raw)
    (function := i.function) (native := carrier) (type := type)

section ReadPost
open CompatibleExpressionReads
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
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {childFuel : Nat}
  {compilation : SourceCoreFunctions.Context} {parentId : ExpressionId} {ids : List ExpressionId}
  {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body childFuel compilation source scope parentId id ids metadata reasonAt lowered)
  {calleeNode : ExpressionNode}
  (initial : callerProtocol.State ⟨scope, i.mapping, i.world, heap, store, canonical⟩)

theorem at_chosen_post
    (sameCode : compiler.calleeCode.expression = code)
    (sameNode : calleeNode = certificate.node)
    (sameType : compiler.calleeCode.type = certificate.type)
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
    CalleeAt root expressionSyntax headers keys registry faults
      (extendIndex i post.2.2.2.1 post.2.2.2.2.1) history calleeNode.type calleeValue carrier compiler.calleeCode.type := by
  obtain ⟨samePost, sameSource, _sameHeap, sameNative, _sameStore, member⟩ :=
    CallableIndexedOwnedChosenOrdinaryReadMembers.at_value_post_chosen
      root expressionSyntax certificate bridge profile compiler initial sameCode binding unique
      environments locals agrees stored lookup sourceTrace post
  obtain ⟨sameSource, selected⟩ :=
    CallableIndexedOwnedChosenOrdinaryReadMembers.selected_at_callee_post
      (evidence := evidence) root expressionSyntax certificate bridge profile compiler initial
      sameNode sameType binding environments locals agrees stored lookup samePost sameSource sameNative member
  exact ⟨samePost, sameSource, sameNative, member, selected⟩
end ReadPost

section Gate
variable {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution} {node : ExpressionNode}
  {function : Dynamic.Closure} {carrier : Value}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) site site.call ids (.closure function) carrier)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar site callee ids metadata node dispatch.row)

/-- Genuine stage acceptance and physical counts close only these two selected gates. -/
structure AcceptedAt (unknown : Word) : Prop where
  stage : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) site.call ids (.closure function)
  physical : function.parameters.length = ids.length
  first : dispatch.row.beforeArguments = .ok ()
  fourth : dispatch.row.afterArguments = .ok ()
  beforeApplication : CallableContract.decision site.gates .beforeApplication unknown dispatch.contract = none

include selected in
/-- The original bound Source contract authenticates the same row counts. -/
theorem accepted_at_row (unknown : Word)
    (stage : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) site.call ids (.closure function))
    (physical : function.parameters.length = ids.length) : AcceptedAt dispatch unknown :=
  ⟨stage, physical, dispatch.accepted stage,
    CallableIndexedOwnedStoredIndirectApplicationPrefix.accepted_row dispatch selected physical,
    CallableIndexedOwnedStoredIndirectCallBounds.application_gate dispatch selected physical unknown⟩

include selected in
/-- An actual passed fourth bind retains its physical count; stage acceptance stays independent. -/
theorem at_passed (unknown : Word)
    (stage : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) site.call ids (.closure function))
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
    {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
    (same : prepared.site = site) {budget : Nat} {actual : Environment} {value : Value} {finalStore : Store}
    (passed : CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared (same.symm ▸ dispatch) budget value finalStore) : AcceptedAt dispatch unknown := by
  exact accepted_at_row dispatch selected unknown stage passed.1
end Gate

section Arguments
variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

/-- The owner is the one retained by the actual positive constructor.
Every dynamic input is at this same argument heap, store and current row. -/
inductive ArgumentAt (i : OrdinaryIndex compiled) (history : History i.code)
    {callerScope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {heap : Dynamic.Heap} {store : Store}
    (state : State headers keys ⟨callerScope, i.mapping, i.world, heap, store, canonical⟩)
    (sources : List Dynamic.Value) (payloads : List Value) : Prop where
  | ordinary
      (owner : OwnedKey keys) (factory : FactoryMember root expressionSyntax i)
      (origin : SourceOrigin i.support history)
      (prefixContext : i.captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) i.support.caller)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 i.scope i.captured.canonical owner.key.frameLocation)
      (referenceIndex : i.code.referenceIndex = i.scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType i.world (CallableIndexedLambdaValues.value i.code i.captured.embedding history.native i.capturedActual)
        (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) compiled.indexed.layouts.definitions)
      (represented : CallableIndexedParameterMeaning.Arguments
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
        i.mapping i.world i.code.receipt.loweredParameters sources payloads)
      (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) i.mapping i.world heap store)
      (raw : CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments i.function heap sources)
      (argumentsTyped : Dynamic.ValuesHaveTypes i.function.context heap sources i.support.body.types)
      (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows state)
      (reference : i.captured.canonical[i.code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
      (currentMetadata : Option MetadataState)
      (currentCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        (state.rows owner.position).authority.current (state.rows owner.position).authority.ghost currentMetadata)
      (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed compiled.indexed.ancestry.graph.inputs
        history.metadata i.code.descriptor.id = true) : ArgumentAt i history state sources payloads

/-- This projection reconstructs the same positive constructor, without extracting data from Prop. -/
theorem ArgumentAt.chosen {i : OrdinaryIndex compiled} {history : History i.code}
    {callerScope : SourceCoreLocalCell.Scope} {canonical : Environment} {heap : Dynamic.Heap} {store : Store}
    {state : State headers keys ⟨callerScope, i.mapping, i.world, heap, store, canonical⟩}
    {sources : List Dynamic.Value} {payloads : List Value}
    (receipt : ArgumentAt (registry := registry) (faults := faults) root expressionSyntax profile i history state sources payloads) :
    ChosenAt root expressionSyntax headers keys registry faults i history := by
  cases receipt with
  | ordinary owner factory origin prefixContext globals referenceIndex typed represented heaps raw argumentsTyped stable reference currentMetadata currentCarried allowed =>
    exact .ordinary owner factory origin prefixContext globals referenceIndex typed

/-- The chosen compiler factory remains attached to the literal future index. -/
theorem ArgumentAt.factory {i : OrdinaryIndex compiled} {history : History i.code}
    {callerScope : SourceCoreLocalCell.Scope} {canonical : Environment} {heap : Dynamic.Heap} {store : Store}
    {state : State headers keys ⟨callerScope, i.mapping, i.world, heap, store, canonical⟩}
    {sources : List Dynamic.Value} {payloads : List Value}
    (receipt : ArgumentAt (registry := registry) (faults := faults) root expressionSyntax profile i history state sources payloads) :
    FactoryMember root expressionSyntax i :=
  ChosenAt.factory root expressionSyntax (ArgumentAt.chosen root expressionSyntax profile receipt)
end Arguments

namespace ForModel
section ArgumentPacket
variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))

/-- The owner is the one retained by the actual positive constructor.
Every dynamic input is at this same argument heap, store and current row. -/
inductive ArgumentReceipt (i : OrdinaryIndex compiled) (history : History i.code)
    {callerScope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {heap : Dynamic.Heap} {store : Store}
    (state : State headers keys ⟨callerScope, i.mapping, i.world, heap, store, canonical⟩)
    (sources : List Dynamic.Value) (payloads : List Value) : Prop where
  | ordinary
      (owner : OwnedKey keys) (factory : FactoryMember root expressionSyntax i)
      (origin : SourceOrigin i.support history)
      (prefixContext : i.captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) i.support.caller)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 i.scope i.captured.canonical owner.key.frameLocation)
      (referenceIndex : i.code.referenceIndex = i.scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType i.world (CallableIndexedLambdaValues.value i.code i.captured.embedding history.native i.capturedActual)
        (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) compiled.indexed.layouts.definitions)
      (represented : CallableIndexedParameterMeaning.Arguments
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          functions)
        i.mapping i.world i.code.receipt.loweredParameters sources payloads)
      (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        functions i.mapping i.world heap store)
      (raw : CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments i.function heap sources)
      (argumentsTyped : Dynamic.ValuesHaveTypes i.function.context heap sources i.support.body.types)
      (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows state)
      (reference : i.captured.canonical[i.code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
      (currentMetadata : Option MetadataState)
      (currentCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        (state.rows owner.position).authority.current (state.rows owner.position).authority.ghost currentMetadata)
      (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed compiled.indexed.ancestry.graph.inputs
        history.metadata i.code.descriptor.id = true) : ArgumentReceipt i history state sources payloads

/-- This projection reconstructs the same positive constructor, without extracting data from Prop. -/
theorem ArgumentReceipt.chosen_member {i : OrdinaryIndex compiled} {history : History i.code}
    {callerScope : SourceCoreLocalCell.Scope} {canonical : Environment} {heap : Dynamic.Heap} {store : Store}
    {state : State headers keys ⟨callerScope, i.mapping, i.world, heap, store, canonical⟩}
    {sources : List Dynamic.Value} {payloads : List Value}
    (receipt : ArgumentReceipt (registry := registry) root expressionSyntax functions i history state sources payloads) :
    ChosenAt root expressionSyntax headers keys registry faults i history := by
  cases receipt with
  | ordinary owner factory origin prefixContext globals referenceIndex typed represented heaps raw argumentsTyped stable reference currentMetadata currentCarried allowed =>
    exact .ordinary owner factory origin prefixContext globals referenceIndex typed

/-- The chosen compiler factory remains attached to the literal future index. -/
theorem ArgumentReceipt.factory_member {i : OrdinaryIndex compiled} {history : History i.code}
    {callerScope : SourceCoreLocalCell.Scope} {canonical : Environment} {heap : Dynamic.Heap} {store : Store}
    {state : State headers keys ⟨callerScope, i.mapping, i.world, heap, store, canonical⟩}
    {sources : List Dynamic.Value} {payloads : List Value}
    (receipt : ArgumentReceipt (registry := registry) root expressionSyntax functions i history state sources payloads) :
    FactoryMember root expressionSyntax i :=
by
  cases receipt with
  | ordinary owner factory origin prefixContext globals referenceIndex typed represented heaps raw argumentsTyped stable reference currentMetadata currentCarried allowed =>
    exact factory
end ArgumentPacket
end ForModel

section ParentArguments
variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {calleeNode : ExpressionNode}
  {firstMap : LocationMap} {firstWorld : StoreTyping} {before : Dynamic.Heap} {firstStore : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)
  {sourceTypes : List TypeSystem.Ty} {calleeHeap : Dynamic.Heap} {calleeStore : Store} {calleeNative : Value}
  (i : OrdinaryIndex compiled) (history : History i.code)

/-- This is the original complete argument tuple with one additional positive receipt. -/
def QualifiedSuccessStep (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize sources payloads middle argumentStore finalMap finalWorld,
    EvaluationSize nativeSize (.unit :: calleeNative :: actual) calleeStore
      ((((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ).weakenAt 0).weakenAt 0)
      (.inRight .word (DataPatternValues.packValues payloads)) argumentStore ∧ nativeSize < budget ∧
    SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment calleeHeap ids sources middle ∧
    DataExpressionSequence.Values
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      finalMap finalWorld sourceTypes (compiler.codes.map (·.type)) sources payloads ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) finalMap finalWorld middle argumentStore ∧
    ∃ stepMaps : LocationMap.Extends i.mapping finalMap, ∃ stepWorlds : WorldExtends i.world finalWorld,
    AdministrativePreserved i.mapping calleeStore finalMap argumentStore ∧ Dynamic.HeapMetadataExtend calleeHeap middle ∧
    LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
    AdministrativePreserved firstMap firstStore finalMap argumentStore ∧ Dynamic.HeapMetadataExtend before middle ∧
    ∃ argumentState : callerProtocol.State ⟨scope, finalMap, finalWorld, middle, argumentStore, canonical⟩,
    callerProtocol.Relates first argumentState ∧ Admission bridge context argumentState ∧
    ∃ remainingSize,
    EvaluationSize remainingSize (DataPatternValues.packValues payloads :: .unit :: calleeNative :: actual) argumentStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication native.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore ∧ remainingSize < budget ∧
    ArgumentAt (registry := registry) (faults := faults) root expressionSyntax profile (extendIndex i stepMaps stepWorlds) history (bridge.pool argumentState) sources payloads

variable {sidecar : SourceCoreStageContracts.Sidecar}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure i.function) calleeNative)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata compiler.original dispatch.row)
  (stage : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure i.function))
  (member : ChosenAt root expressionSyntax headers keys registry faults i history)
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure i.function) calleeHeap)
  (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context) bridge
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
    compiler first (.closure i.function) calleeHeap calleeNative calleeStore i.mapping i.world)
  (sameNative : calleeNative = CallableIndexedLambdaValues.value i.code i.captured.embedding history.native i.capturedActual)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  {certificate : GenericExpressionMeaning.Certificate}
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context) (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (admitted : Admission bridge context first)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)

namespace ForModel
variable
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (genericPost : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context) bridge
    functions compiler first (.closure i.function) calleeHeap calleeNative calleeStore i.mapping i.world)

/-- This is the original complete argument tuple with one additional positive receipt. -/
def SuccessfulArgumentPost (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize sources payloads middle argumentStore finalMap finalWorld,
    EvaluationSize nativeSize (.unit :: calleeNative :: actual) calleeStore
      ((((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ).weakenAt 0).weakenAt 0)
      (.inRight .word (DataPatternValues.packValues payloads)) argumentStore ∧ nativeSize < budget ∧
    SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment calleeHeap ids sources middle ∧
    DataExpressionSequence.Values
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions)
      finalMap finalWorld sourceTypes (compiler.codes.map (·.type)) sources payloads ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      functions finalMap finalWorld middle argumentStore ∧
    ∃ stepMaps : LocationMap.Extends i.mapping finalMap, ∃ stepWorlds : WorldExtends i.world finalWorld,
    AdministrativePreserved i.mapping calleeStore finalMap argumentStore ∧ Dynamic.HeapMetadataExtend calleeHeap middle ∧
    LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
    AdministrativePreserved firstMap firstStore finalMap argumentStore ∧ Dynamic.HeapMetadataExtend before middle ∧
    ∃ argumentState : callerProtocol.State ⟨scope, finalMap, finalWorld, middle, argumentStore, canonical⟩,
    callerProtocol.Relates first argumentState ∧ Admission bridge context argumentState ∧
    ∃ remainingSize,
    EvaluationSize remainingSize (DataPatternValues.packValues payloads :: .unit :: calleeNative :: actual) argumentStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication native.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore ∧ remainingSize < budget ∧
    ArgumentReceipt (registry := registry) root expressionSyntax functions (extendIndex i stepMaps stepWorlds) history (bridge.pool argumentState) sources payloads


include functions profile member calleeTrace genericPost sameNative parentTyped tree unique wellFormed runtime covers locals admitted actualFunctionType in
/-- The same successful argument witness supplies all invocation inputs.
This endpoint invokes neither a callee/argument semantic producer nor a body. -/
theorem at_argument_post (budget : Nat) {value : Value} {finalStore : Store}
    (original : CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge functions compiler prepared first budget value finalStore)
    (step : CallableIndexedOwnedStoredFunctionModelReceipts.SuccessStep
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      (calleeMap := i.mapping) (calleeWorld := i.world)
      bridge functions compiler prepared first budget value finalStore)
    (passed : CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore) :
    CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge functions compiler prepared first budget value finalStore ∧
    CallableIndexedOwnedStoredFunctionModelReceipts.SuccessStep
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      (calleeMap := i.mapping) (calleeWorld := i.world)
      bridge functions compiler prepared first budget value finalStore ∧
    CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore ∧
    SuccessfulArgumentPost (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      (functions := functions) root expressionSyntax bridge compiler prepared first i history budget value finalStore := by
  refine ⟨original, step, passed, ?_⟩
  obtain ⟨nativeSize, sourceSize, sources, payloads, middle, argumentStore, finalMap, finalWorld,
    nativeTrace, strict, argumentsTrace, represented, argumentHeaps, stepMaps, stepWorlds, stepFrame, stepMetadata,
    maps, worlds, frame, metadataExtended, ⟨argumentState, related, argumentAdmission⟩,
    ⟨remainingSize, remaining, remainingStrict⟩⟩ := step
  have future := ChosenAt.extend root expressionSyntax member stepMaps stepWorlds
  cases future with
  | ordinary owner factory origin prefixContext globals referenceIndex typed =>
    have parameters := CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) i.code
    have sourceBinders : i.code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body) =
        i.function.parameters.map (fun binding => binding.scheme.body) := by
      simpa only [List.map_map, Function.comp_def] using
        (congrArg (List.map (fun binding : TypedBinder => binding.scheme.body)) parameters).symm
    have sourceBundle := CallableIndexedOwnedStoredSourceBundleReceipts.source_bundle_of_trace
      unique compiler.found compiler.originalForm parentTyped tree compiler.argumentCoercions
      wellFormed runtime covers locals admitted.heap calleeTrace sourceBinders
    have selectedType : RuntimeValueHasType finalWorld calleeNative
        (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) compiled.indexed.layouts.definitions := by
      rw [sameNative]
      exact typed
    have actualType := genericPost.2.1.runtime_hasType.type_eq
    have callableType := compiler.callableType
    rw [actualFunctionType] at callableType
    have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters
      (callableType.trans (actualType.symm.trans selectedType.type_eq))
    have nativeBundle := (CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
      (compiler.packedType.symm.trans nativeTypes.1)
    have nativeCount : (compiler.codes.map (·.type)).length = i.function.parameters.length := by
      simpa only [List.length_map] using compiler.ordered_children.1.symm.trans passed.1.symm
    have arity : sources.length = i.function.parameters.length := represented.length.1.symm.trans nativeCount
    have representedArguments := CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.arguments_of_bundles
      (i.captured.extend stepMaps stepWorlds) i.code i.support i.prepared
      functions profile represented arity.symm
      (by simpa only [sourceBinders] using sourceBundle) nativeBundle
    obtain ⟨parameter, sourceResult, rawTypes, _calleeTyping, _argumentsTyping, _application,
      _calleeTyped, _calleeHeapTyped, _calleeExtension, _calleeLocals, _rawTyped, _argumentHeapTyped,
      _heapExtension, _argumentLocals, _fullExtension, _rawArity, _packed, _packing, _packedTyped, raw⟩ :=
      CallableIndexedOwnedStoredCallSourcePrefix.from_admission_with_arity bridge first wellFormed runtime covers locals admitted
        unique compiler.found compiler.originalForm parentTyped compiler.argumentCoercions arity calleeTrace argumentsTrace
    have rawArguments : Dynamic.ValuesHaveTypes i.function.context middle sources i.support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq i.support.body.extended] using raw.arguments
    have reference : i.captured.canonical[i.code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      have actualReferenceIndex : i.code.referenceIndex =
          i.scope.length + 1 + compiled.indexed.base.globals.length := referenceIndex
      rw [actualReferenceIndex]
      exact globals.reference
    obtain ⟨currentMetadata, currentCarried⟩ := argumentAdmission.rows owner.position
    exact ⟨nativeSize, sourceSize, sources, payloads, middle, argumentStore, finalMap, finalWorld,
      nativeTrace, strict, argumentsTrace, represented, argumentHeaps, stepMaps, stepWorlds, stepFrame, stepMetadata,
      maps, worlds, frame, metadataExtended, argumentState, related, argumentAdmission,
      remainingSize, remaining, remainingStrict,
      .ordinary owner factory origin prefixContext globals referenceIndex typed representedArguments argumentHeaps
        raw rawArguments argumentAdmission.rows reference currentMetadata currentCarried
        (CallableIndexedLambdaTemplatePermission.lambda_allowed i.code history)⟩
end ForModel

include member calleeTrace post sameNative parentTyped tree unique wellFormed runtime covers locals admitted actualFunctionType in
/-- The same successful argument witness supplies all invocation inputs.
This endpoint invokes neither a callee/argument semantic producer nor a body. -/
theorem at_successful_arguments (budget : Nat) {value : Value} {finalStore : Store}
    (original : CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler prepared first budget value finalStore)
    (step : CallableIndexedOwnedStoredFunctionModelReceipts.SuccessStep
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      (calleeMap := i.mapping) (calleeWorld := i.world)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler prepared first budget value finalStore)
    (passed : CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore) :
    CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler prepared first budget value finalStore ∧
    CallableIndexedOwnedStoredFunctionModelReceipts.SuccessStep
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      (calleeMap := i.mapping) (calleeWorld := i.world)
      bridge (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) compiler prepared first budget value finalStore ∧
    CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore ∧
    QualifiedSuccessStep (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      root expressionSyntax bridge profile compiler prepared first i history budget value finalStore := by
  obtain ⟨sameOriginal, sameStep, samePassed, qualified⟩ :=
    ForModel.at_argument_post (functions := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
      (genericPost := post) (root := root) (expressionSyntax := expressionSyntax) (bridge := bridge) (profile := profile)
      (compiler := compiler) (prepared := prepared) (first := first) (i := i) (history := history) (dispatch := dispatch)
      (member := member) (calleeTrace := calleeTrace) (sameNative := sameNative) (parentTyped := parentTyped)
      (tree := tree) (unique := unique) (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
      (locals := locals) (admitted := admitted) (actualFunctionType := actualFunctionType) budget original step passed
  refine ⟨sameOriginal, sameStep, samePassed, ?_⟩
  obtain ⟨nativeSize, sourceSize, sources, payloads, middle, argumentStore, finalMap, finalWorld,
    nativeTrace, strict, argumentsTrace, represented, argumentHeaps, stepMaps, stepWorlds, stepFrame, stepMetadata,
    maps, worlds, frame, metadataExtended, argumentState, related, argumentAdmission,
    remainingSize, remaining, remainingStrict, receipt⟩ := qualified
  cases receipt with
  | ordinary owner factory origin prefixContext globals referenceIndex typed representedArguments heaps raw argumentsTyped stable reference currentMetadata currentCarried allowed =>
    exact ⟨nativeSize, sourceSize, sources, payloads, middle, argumentStore, finalMap, finalWorld,
      nativeTrace, strict, argumentsTrace, represented, argumentHeaps, stepMaps, stepWorlds, stepFrame, stepMetadata,
      maps, worlds, frame, metadataExtended, argumentState, related, argumentAdmission,
      remainingSize, remaining, remainingStrict,
      .ordinary owner factory origin prefixContext globals referenceIndex typed representedArguments heaps
        raw argumentsTyped stable reference currentMetadata currentCarried allowed⟩

end ParentArguments

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinarySelectedCallReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryArgumentBundles
/-! The known chosen constructor and actual callee representation identify
the compiler's native argument bundle. Genuine Source arity and raw binder
types remain independent. The original parameter alignment consumes actual
argument values at their reached map and world without a payload inverse. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryArgumentBundles
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
open CallableIndexedOwnedChosenOrdinaryStoredMembers (ChosenAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {rootCompilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode rootCompilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {i : OrdinaryIndex compiled} {history : History i.code}
  (member : ChosenAt root expressionSyntax headers keys registry faults i history)

include member in
/-- The original positive constructor already contains this native type. -/
theorem native_type :
    (value i.code i.captured.embedding history.native i.capturedActual).type =
      CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore := by
  cases member with
  | ordinary _ _ _ _ _ _ typed => exact typed.type_eq

variable {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {call callee : ExpressionId} {ids : List ExpressionId}
  {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt root.selected.policy root.selected.lowerBody fuel
    compilation source scope call callee ids metadata reasonAt lowered)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {raw : TypeSystem.Ty} {carrier : Value}
  (represented : ValueRep compiled.compatible.checked registry functions i.mapping i.world
    raw (.closure i.function) carrier compiler.calleeCode.type)
  (sameNative : carrier = value i.code i.captured.embedding history.native i.capturedActual)

include member represented sameNative in
/-- The actual root's callable convention and the same known callee fix
both native signature components; Source metadata is not inverted. -/
theorem compiler_parameters : compiler.parameterType = i.code.receipt.parameterCore ∧
    compiler.resultType = i.code.receipt.resultCore := by
  have actualType := represented.runtime_hasType.type_eq
  rw [sameNative] at actualType
  have selectedType := native_type root expressionSyntax member
  have accepted := compiler.callableType
  rw [root.callables] at accepted
  change CallableContract.functionType compiler.parameterType compiler.resultType = compiler.calleeCode.type at accepted
  exact CallableIndexedOwnedStoredNativePackReceipts.callable_parameters
    (accepted.trans (actualType.symm.trans selectedType))

include member represented sameNative in
/-- The real ordered compiler vector has the selected Code's packed type. -/
theorem compiler_parameter_pack :
    SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) = i.code.receipt.parameterCore :=
  (CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
    (compiler.packedType.symm.trans
      (compiler_parameters root expressionSyntax member compiler functions represented sameNative).1)

include member represented sameNative in
/-- Original parameter alignment uses actual values at the argument post.
Physical arity and raw Source bundle equality retain their own provenance. -/
theorem arguments_at_compiler
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {futureMap : LocationMap} {futureWorld : StoreTyping}
    (maps : LocationMap.Extends i.mapping futureMap) (worlds : WorldExtends i.world futureWorld)
    {sourceTypes : List TypeSystem.Ty} {arguments : List Dynamic.Value} {payloads : List Value}
    (values : DataExpressionSequence.Values
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      futureMap futureWorld sourceTypes (compiler.codes.map (·.type)) arguments payloads)
    (arity : i.function.parameters.length = arguments.length)
    (rawBundle : TypeSystem.Ty.productMany sourceTypes =
      TypeSystem.Ty.productMany (i.function.parameters.map (fun binder => binder.scheme.body))) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      futureMap futureWorld i.code.receipt.loweredParameters arguments payloads := by
  exact CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.arguments_of_bundles
    (i.captured.extend maps worlds) i.code i.support i.prepared functions profile values arity rawBundle
    (compiler_parameter_pack root expressionSyntax member compiler functions represented sameNative)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryArgumentBundles
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryCallDispatchReceipts
/-! The known chosen ordinary closure selects its actual source sidecar,
lambda origin and parent codebook row. Original and contextual lambda origins
remain available, including contextual origins whose substitution is empty.
This static receipt retains the literal capture/history carrier; association
with an actual callee read or value post remains a runtime input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryCallDispatchReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
open CallableIndexedOwnedChosenOrdinaryStoredMembers (ChosenAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {i : OrdinaryIndex compiled} {history : History i.code}

/-- The positive constructor identifies the actual owning Header. -/
theorem chosen_caller (member : ChosenAt root expressionSyntax headers keys registry faults i history) :
    i.support.caller = caller := by
  have factory := member.factory
  cases factory with
  | formed receipt chosen environment captured prefixContext => rfl

variable {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {call callee : ExpressionId}
  {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt root.selected.policy root.selected.lowerBody fuel
    (context compiled.indexed caller.named) (source caller.named) scope call callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)

/-- Every field is tied to the same known closure and original parent receipt.
The selected row records its genuine guard provenance without assuming a
stage verdict, argument execution or called-body meaning. -/
structure Receipt where
  chosen : ChosenAt root expressionSyntax headers keys registry faults i history
  sidecar : SourceCoreStageContracts.Sidecar
  sidecarPrepared : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
    (context compiled.indexed caller.named).owner = .ok sidecar
  sidecarCaller : sidecar.caller = caller.named.specialized
  sidecarSource : sidecar.source = source caller.named
  sidecarPlan : sidecar.plan = compiled.indexed.base.plan
  lambdaSite : AuthenticatedCallableLedger.LambdaSite compiled.indexed.base.plan
    compiled.indexed.ancestry.graph.inputs.callable.table i.code.compilation.owner i.code.id i.code.active i.code.descriptor.id
  lambdaOrigin : CallableLedger.LambdaOrigin compiled.indexed.base.plan i.code.compilation.owner
    i.code.id i.code.active i.function lambdaSite.contract
  origin : CallableLedger.OriginRep sidecar.plan prepared.site.table (.closure i.function)
    (value i.code i.captured.embedding history.native i.capturedActual)
  rows : CallableLedger.Rows sidecar prepared.site prepared.site.call ids
  dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site call ids (.closure i.function)
    (value i.code i.captured.embedding history.native i.capturedActual)
  selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site
    callee ids metadata compiler.original dispatch.row

/-- Actual public preparation and the known positive member construct the
sidecar, both lambda-origin alternatives, complete rows and exact selection.
The original parent policy, scope, children and budget are preserved. -/
theorem at_chosen_parent (member : ChosenAt root expressionSyntax headers keys registry faults i history) :
    Nonempty (Receipt root expressionSyntax compiler prepared (headers := headers) (keys := keys)
      (registry := registry) (faults := faults) (i := i) (history := history)) := by
  have sameCaller := chosen_caller root expressionSyntax member
  have actual := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  obtain ⟨lambdaSite⟩ := RecursiveStageProjection.lambda_site_of_descriptor actual.accepted i.code.descriptor
  obtain ⟨sidecar, sidecarPrepared, _⟩ := LambdaSourceAlignment.LambdaSource.canonical lambdaSite.original
  have sourceReceipt := i.support.source_receipt
  have sameSource := sourceReceipt.source sidecarPrepared
  rw [i.support.active, EmptySourceSubstitution.source] at sameSource
  have owner : i.code.compilation.owner = (context compiled.indexed caller.named).owner := by
    rw [i.support.compilation, sameCaller]
  have callerPrepared : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
      (context compiled.indexed caller.named).owner = .ok sidecar := by
    rwa [owner] at sidecarPrepared
  have sidecarCaller := RecursiveNamedPreparedStageScopes.sidecar_caller callerPrepared
    (CallableIndexedActualNamedSourceReceipts.header_record compiled caller)
  have source : sidecar.source = CallableIndexedNamedGeneration.source caller.named := by
    rw [← sameSource, i.support.source, sameCaller]
  have sidecarPlan := (CallContractCertificates.sidecar_of_accepted callerPrepared).1
  have lambdaOrigin := LambdaMetadataViews.lambda_origin sourceReceipt lambdaSite.original
    i.code.viewOfSource i.support.unique i.code.found (i.code.form.trans i.code.sourceForm)
  have codeOrigin : CallableLedger.OriginRep compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table (.closure i.function)
      (value i.code i.captured.embedding history.native i.capturedActual) := by
    have represented := CallableLedger.OriginRep.closure
      (raw := .pair (.inLeft .word .unit)
        (.closure i.code.receipt.parameterCore (LanguageResult.resultType i.code.receipt.resultCore)
          (i.code.body.rename i.captured.embedding.lift.lift)
          (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame history.native :: i.capturedActual)))
      lambdaSite.member lambdaSite.origin lambdaSite.retained lambdaOrigin
    simpa only [value, lambdaSite.id_eq] using represented
  have parentContains : ContainsExpression sidecar.source prepared.site.call compiler.original := by
    rw [source, prepared.call]
    exact lookupExpression?_sound compiler.found
  have atSite := actual.accepted
  rw [← prepared.table] at atSite
  have atCaller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar := by
    rwa [prepared.caller]
  have rows := CallCodebookCertificates.rows_of_prepareWithProjection atSite atCaller
    parentContains compiler.originalForm
  have origin : CallableLedger.OriginRep sidecar.plan prepared.site.table (.closure i.function)
      (value i.code i.captured.embedding history.native i.capturedActual) := by
    rw [sidecarPlan, prepared.table]
    exact codeOrigin
  have bound : (CallableLedger.frame sidecar).Binds (.closure i.function)
      (CallContractCertificates.semanticContract lambdaSite.contract) := by
    change CallableLedger.Binds sidecar.plan (.closure i.function)
      (CallContractCertificates.semanticContract lambdaSite.contract)
    rw [sidecarPlan]
    exact lambdaOrigin.binds
  obtain ⟨dispatch⟩ := CallableLedger.dispatch rows origin bound
  have dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site call ids
      (.closure i.function) (value i.code i.captured.embedding history.native i.capturedActual) := by
    rwa [prepared.call] at dispatch
  have selected := CallableIndexedOwnedSelectedCallCodebookReceipts.selected_at_prepared actual prepared.table
    atCaller parentContains compiler.originalForm (by rw [← sameSource]; exact i.support.unique) dispatch.found
  exact ⟨⟨member, sidecar, callerPrepared, sidecarCaller, source, sidecarPlan, lambdaSite,
    lambdaOrigin, origin, rows, dispatch, selected⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryCallDispatchReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryCallDispatchSourceTransport
/-! Dispatch provenance across a genuine equality of the caller's Source.
The receipt keeps the original compiler and Prepared endpoints, including the
chosen lambda origin and selected row. Its producer transports the equality
and uses the existing dispatch producer once under the same root policy. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryCallDispatchSourceTransport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
open CallableIndexedOwnedChosenOrdinaryStoredMembers (ChosenAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {i : OrdinaryIndex compiled} {history : History i.code}
  {actualSource : TypedSource}
  {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {call callee : ExpressionId}
  {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt root.selected.policy root.selected.lowerBody fuel
    (context compiled.indexed caller.named) actualSource scope call callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)

/-- Static dispatch fields at the original Source-indexed parent endpoints.
The actual Source equality and contextual lambda-origin alternatives remain
available; association with an executed callee is a separate runtime fact. -/
structure Receipt where
  source_eq : actualSource = source caller.named
  chosen : ChosenAt root expressionSyntax headers keys registry faults i history
  sidecar : SourceCoreStageContracts.Sidecar
  sidecarPrepared : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
    (context compiled.indexed caller.named).owner = .ok sidecar
  sidecarCaller : sidecar.caller = caller.named.specialized
  sidecarSource : sidecar.source = actualSource
  sidecarPlan : sidecar.plan = compiled.indexed.base.plan
  lambdaSite : AuthenticatedCallableLedger.LambdaSite compiled.indexed.base.plan
    compiled.indexed.ancestry.graph.inputs.callable.table i.code.compilation.owner i.code.id i.code.active i.code.descriptor.id
  lambdaOrigin : CallableLedger.LambdaOrigin compiled.indexed.base.plan i.code.compilation.owner
    i.code.id i.code.active i.function lambdaSite.contract
  origin : CallableLedger.OriginRep sidecar.plan prepared.site.table (.closure i.function)
    (value i.code i.captured.embedding history.native i.capturedActual)
  rows : CallableLedger.Rows sidecar prepared.site prepared.site.call ids
  dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site call ids (.closure i.function)
    (value i.code i.captured.embedding history.native i.capturedActual)
  selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site
    callee ids metadata compiler.original dispatch.row

/-- Transport the genuine Source equality before invoking the original
producer. The output retains this compiler, Prepared site, chosen closure and
root; it supplies no execution, guard verdict or called-body law. -/
theorem at_chosen_parent (sameSource : actualSource = source caller.named)
    (member : ChosenAt root expressionSyntax headers keys registry faults i history) :
    Nonempty (Receipt root expressionSyntax compiler prepared (headers := headers) (keys := keys)
      (registry := registry) (faults := faults) (i := i) (history := history)) := by
  cases sameSource
  obtain ⟨receipt⟩ := CallableIndexedOwnedChosenOrdinaryCallDispatchReceipts.at_chosen_parent
    root expressionSyntax compiler prepared member
  exact ⟨⟨rfl, receipt.chosen, receipt.sidecar, receipt.sidecarPrepared, receipt.sidecarCaller,
    receipt.sidecarSource, receipt.sidecarPlan, receipt.lambdaSite, receipt.lambdaOrigin,
    receipt.origin, receipt.rows, receipt.dispatch, receipt.selected⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryCallDispatchSourceTransport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryCalleePosts
/-! Strict callee children retain their actual chosen function representation.
Selection is derived at that same reached state, preserving every prior branch.
Faults use the same child post and stop before argument evaluation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryCalleePosts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler native)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)


variable
  {rootCaller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {rootCompilation : CallableIndexedNamedGeneration.Compilation compiled.indexed rootCaller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
    (compiled := compiled) rootCaller.named diagnostics namedCode rootCompilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)


variable (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
  (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile) mapping world before store)

/-- Selection inspects the complete representation of this exact callee post.
Every General prior branch and the positive chosen constructor remain present. -/
theorem selected_at_value_post
    {function : Dynamic.Closure} {after : Dynamic.Heap} {value : Value} {finalStore : Store}
    {finalMap : LocationMap} {finalWorld : StoreTyping}
    (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost
      (registry := registry) (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
      bridge (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile) compiler initial (.closure function) after value finalStore finalMap finalWorld) :
    CallableIndexedOwnedChosenOrdinaryLambdaValues.Selected
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := finalMap) (world := finalWorld) (raw := calleeNode.type)
      (function := function) (native := value) (type := compiler.calleeCode.type) root expressionSyntax :=
  CallableIndexedOwnedChosenOrdinaryLambdaValues.selected_of_value root expressionSyntax profile post.2.1

section SourceValue
include certified found sourceTyped environments heaps locals agrees typed admitted
/-- The strict Source child produces both the whole real post and its selection.
No callee value, reached state or provenance qualifier is supplied separately. -/
theorem source_closure_at_callee (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)) context evidence source certificate faults size)
    {size : Nat} {function : Dynamic.Closure} {after : Dynamic.Heap}
    (trace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) size
      context evidence source environment before callee (.closure function) after)
    (smaller : size < budget) :
    ∃ value finalStore finalMap finalWorld,
      CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost
        (registry := registry) (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
        bridge (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile) compiler initial (.closure function) after value finalStore finalMap finalWorld ∧
      CallableIndexedOwnedChosenOrdinaryLambdaValues.Selected
        (headers := headers) (keys := keys) (registry := registry) (faults := faults)
        (mapping := finalMap) (world := finalWorld) (raw := calleeNode.type)
        (function := function) (native := value) (type := compiler.calleeCode.type) root expressionSyntax := by
  obtain ⟨value, finalStore, finalMap, finalWorld, post⟩ :=
    CallableIndexedOwnedStoredIndirectCalleePost.ForModel.preserves_callee_value
      (bridge := bridge) (functionModel := (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)) (compiler := compiler)
      (certified := certified) (found := found) (sourceTyped := sourceTyped)
      (environments := environments) (modelHeaps := heaps) (locals := locals)
      (agrees := agrees) (typed := typed) (initial := initial) (admitted := admitted)
      budget children trace smaller
  exact ⟨value, finalStore, finalMap, finalWorld, post,
    selected_at_value_post (root := root) (expressionSyntax := expressionSyntax)
      (profile := profile) (bridge := bridge) (compiler := compiler) (initial := initial) post⟩

end SourceValue

section SourceFault
include prepared certified found sourceTyped parentTyped wellFormed runtime covers
  environments heaps locals agrees typed admitted
/-- A callee fault stops at the same actual post before arguments or invocation. -/
theorem source_fault_at_callee (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)) context evidence source certificate faults size)
    {size : Nat} {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (fault : SourceExecutionSize.ExpressionFaults (Program.ofChecked compiled.sourceProgram) size
      context evidence source environment before callee reason after)
    (smaller : size < budget) :
    ∃ sourceSize token finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id (.fault reason) after ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inLeft lowered.type (.word token)) finalStore ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ForModel.ResultAt
        (registry := registry) (faults := faults) (context := context)
        bridge (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile) compiler initial (.fault reason) after
        (.inLeft lowered.type (.word token)) finalStore finalMap finalWorld :=
  CallableIndexedOwnedStoredIndirectCalleePost.ForModel.preserves_callee_fault
    (bridge := bridge) (functionModel := (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)) (compiler := compiler) (prepared := prepared)
    (certified := certified) (found := found) (sourceTyped := sourceTyped) (parentTyped := parentTyped)
    (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
    (environments := environments) (modelHeaps := heaps) (locals := locals)
    (agrees := agrees) (typed := typed) (initial := initial) (admitted := admitted)
    budget children fault smaller

end SourceFault
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryCalleePosts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryInitializedReadPosts
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryInitializedReadAdmission
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenWordLiteralExpressionBounds
/-! A fixed approved Word literal has admitted meaning at the same chosen
recaptured support. The original literal producer leaves its actual state
unchanged; numeric evidence and all current rows remain genuine inputs. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenWordLiteralExpressionBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedPreparedMixedBodyCompilerFactory
open CallableIndexedOwnedPreparedMixedBodySiteInputs
open CallableIndexedOwnedLiteralReturnSiteShells
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission

/-- The approved occurrence is fixed before selecting the actual Site. -/
def approved (literalId : ExpressionId) : TypedSource → ExpressionId → Prop :=
  fun _ child => child = literalId

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (literalRoot : LiteralRootReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (literalId : ExpressionId) (node : ExpressionNode)

/-- Actual Source and compiler metadata for the approved Word occurrence. -/
structure WordNodeFacts : Prop where
  found : (source caller.named).lookupExpression? literalId = some node
  form : (∃ literal, node.form = .literal literal) ∨
    ∃ literal resolution, node.form = .integerLiteral literal resolution
  wordType : node.type = .word
  coercions : node.coercions = []
  ordinary : ∃ owned, SourceCompilationPlan.ordinaryOwnedRequirements? node = some owned
  requirements : node.requirements = [] ∨ ∃ literal resolution, node.form = .integerLiteral literal resolution
  initializer : compiled.indexed.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = (context compiled.indexed caller.named).owner ∧ binding.initializer = literalId)) = none

/-- Only actual Word spellings and resolved numeric occurrences are admitted. -/
theorem WordNodeFacts.atomic (facts : WordNodeFacts (caller := caller) literalId node) :
    CompatibleExpressionLiterals.Atomic node.form := by
  rcases facts.form with ⟨literal, form⟩ | ⟨literal, resolution, form⟩
  · rw [form]; exact .word literal
  · rw [form]; exact .integer literal resolution

variable {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
    sourceContext evidence scope id lowered)
  (chosen : ChosenFactory literalRoot.root (approved literalId) receipt)
  (capturedEnvironment : Dynamic.Environment)
  (facts : WordNodeFacts (caller := caller) literalId node)

include chosen facts in
/-- The same recaptured factory retains the original accepted child action.
Only its actual literal compiler branch supplies the selected numeric row. -/
theorem certificate_at_support
    {currentContext : SourceSemantics.Context} {childScope : SourceCoreLocalCell.Scope}
    {child : ExpressionId} {output : SourceCoreBasic.LoweredExpr}
    (actual : (receipt.formation.support capturedEnvironment).certificates
      (receipt.formation.support capturedEnvironment).body.readFuel
      (receipt.formation.function capturedEnvironment).source currentContext childScope child output) :
    child = literalId ∧ CompatibleExpressionLiteralRuntime.Certificate
      (context compiled.indexed caller.named).solvedRequirements
      (receipt.formation.function capturedEnvironment).source child output := by
  change child = literalId ∧ CompatibleExpressionLiteralRuntime.Certificate
    (context compiled.indexed caller.named).solvedRequirements (source caller.named) child output
  change receipt.formation.certificates receipt.formation.body.readFuel (source caller.named)
    currentContext childScope child output at actual
  have same := congrArg (fun family => family receipt.formation.body.readFuel (source caller.named)
    currentContext childScope child output) (formation_factories literalRoot.root (approved literalId) receipt chosen).2
  have accepted := same.mp actual
  cases accepted with
  | intro found _ allowed _ _ _ _ accepted =>
    change child = literalId at allowed
    subst child
    obtain ⟨owned, ordinary⟩ := facts.ordinary
    have policy := literal_policy literalRoot.root facts.found facts.atomic ordinary facts.coercions
      facts.requirements facts.initializer (childScope := childScope) (reasonAt := rootReasonAt)
    refine ⟨rfl, ?_⟩
    exact CompatibleExpressionLiteralRuntime.of_functions (values := .initial compiled.compatible.checked)
      (source := source caller.named) facts.found facts.atomic
      (by intro form; rcases facts.form with ⟨literal, other⟩ | ⟨literal, resolution, other⟩ <;> rw [other] at form <;> cases form)
      policy.special policy.read literalRoot.leaf accepted

private theorem literal_word_type {solved : List SolvedRequirement} {node : ExpressionNode} {type : Ty} {code : Expr}
    (literal : CompatibleExpressionLiterals.Literal solved node type code) (wordType : node.type = .word) : type = .word := by
  cases literal with
  | unit _ typed _ _ | bool _ _ typed _ _ => cases typed.symm.trans wordType
  | word => rfl
  | resolvedWord => rfl
  | resolvedInteger _ metadata => cases metadata.nodeType.symm.trans wordType

private theorem word_typed {solved : List SolvedRequirement} {node : ExpressionNode} {code : Expr}
    (literal : CompatibleExpressionLiterals.Literal solved node .word code)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap} {value : Dynamic.Value}
    (raw : Dynamic.ExpressionFormEvaluates program context evidence source environment heap
      node.form node.requirements node.coercions value heap) : Dynamic.ValueHasType context heap value .word := by
  cases literal with
  | word _ form _ _ _ _ =>
    rw [form] at raw
    cases raw with | literal _ constructed => cases constructed; exact .word _
  | resolvedWord form metadata =>
    rw [form] at raw
    cases raw with | integerLiteral _ constructed =>
      cases constructed with
      | word => exact .word _
      | integer => cases metadata.targetType

private theorem word_outcome_unique {solved : List SolvedRequirement} {node : ExpressionNode} {code : Expr}
    (literal : CompatibleExpressionLiterals.Literal solved node .word code)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    (numeric : CompatibleExpressionLiterals.NumericEvidence context evidence node)
    {source : TypedSource} {id : ExpressionId} (found : source.lookupExpression? id = some node)
    (unique : NodeOccurrencesUnique source) (empty : node.coercions = [])
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {value : Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (raw : Dynamic.ExpressionFormEvaluates program context evidence source environment before
      node.form node.requirements node.coercions value before)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    outcome = .value value ∧ after = before := by
  have contains := lookupExpression?_sound found
  have sameNode : ∀ other, ContainsExpression source id other → other = node := by
    intro other present
    exact Option.some.inj ((lookupExpression?_complete unique present).symm.trans found)
  have nonlocal : ∀ name binder, node.form ≠ .reference name (.local binder) := by
    cases literal <;> intros <;> simp_all
  cases trace with
  | value evaluation =>
    cases evaluation with
    | intro other actual coercions =>
      have same := sameNode _ other
      subst same
      rw [empty] at coercions
      cases coercions
      cases literal with
      | word _ form _ _ _ _ =>
        rw [form] at raw actual
        cases raw with | literal _ first =>
          cases actual with | literal _ second => exact ⟨congrArg _ (second.functional first), rfl⟩
      | resolvedWord form _ =>
        rw [form] at raw actual
        cases raw with | integerLiteral _ first =>
          cases actual with | integerLiteral _ second => exact ⟨congrArg _ (second.functional first), rfl⟩
    | generalizedLocal other form _ _ _ _ _ _ _ =>
      exact False.elim (nonlocal _ _ (sameNode _ other ▸ form))
  | @fault _ _ reason failed =>
    have rawFault : Dynamic.ExpressionFormFaults program context evidence source environment before
        node.form node.requirements node.coercions reason after := by
      cases failed with
      | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent contains)
      | form other failed => exact sameNode _ other ▸ failed
      | coercion other _ failed =>
        have same := sameNode _ other
        subst same
        rw [empty] at failed
        cases failed
      | generalizedLocalRequirement other form _ _ _ _ _ _ _
      | generalizedLocalCoercion other form _ _ _ _ _ _ _ =>
        exact False.elim (nonlocal _ _ (sameNode _ other ▸ form))
    cases literal with
    | word _ form _ _ _ _ => rw [form] at rawFault; cases rawFault
    | resolvedWord form _ =>
      rw [form] at rawFault
      cases rawFault with | integerRequirement _ unavailable => exact False.elim ((numeric _ _ form).2 unavailable)

section Admitted
universe u
variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (currentContext : SourceSemantics.Context) (currentEvidence : Dynamic.EvidenceEnvironment)
  (ledger : currentContext.solvedRequirements = (context compiled.indexed caller.named).solvedRequirements)
  (runtime : RuntimeRequirementLedgerValid currentContext)

include chosen facts ledger runtime in
/-- A real Source child returns the same state with successful Word admission.
The literal producer is the only semantic child consumer. -/
theorem preserves_at_support
    (unique : NodeOccurrencesUnique (receipt.formation.function capturedEnvironment).source) (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      currentContext currentEvidence (receipt.formation.function capturedEnvironment).source
      ((receipt.formation.support capturedEnvironment).certificates
        (receipt.formation.support capturedEnvironment).body.readFuel
        (receipt.formation.function capturedEnvironment).source currentContext) faults size := by
  intro childScope child output actual actualNode found _sourceTyped mapping world administrative environment canonical native
    actualContext before store ξ outcome after _environments heaps _locals _agrees _typed initial admitted trace
  obtain ⟨sameId, actualLiteral⟩ := certificate_at_support literalRoot literalId node receipt chosen capturedEnvironment facts actual
  subst child
  obtain ⟨other, otherFound, literal, selected⟩ := actualLiteral
  have sameNode := Option.some.inj (otherFound.symm.trans facts.found)
  subst other
  have nodeEq := Option.some.inj (found.symm.trans facts.found)
  subst actualNode
  have nativeWord := literal_word_type literal facts.wordType
  rw [nativeWord] at literal
  have numeric := selected.evidence ledger runtime currentEvidence
  obtain ⟨sourceValue, coreValue, raw, related, evaluated⟩ := literal.evaluates_with_evidence (registry := registry)
    functions (Program.ofChecked compiled.sourceProgram) currentContext currentEvidence numeric
    _ environment before mapping world native store ξ
  obtain ⟨sameOutcome, sameHeap⟩ := word_outcome_unique literal numeric facts.found unique facts.coercions raw trace.sound
  subst outcome
  subst after
  refine ⟨.inRight .word coreValue, store, mapping, world, evaluated, .value (by simpa only [CompatibleAmbientHeap.payloadModel, nativeWord] using related), heaps,
    .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial, admitted.rows, ?_⟩
  intro value same
  cases same
  rw [facts.wordType]
  exact ⟨word_typed literal raw, admitted.heap⟩

include chosen facts ledger runtime in
/-- A native completion constructs its genuine independently sized Source
trace. The same current state authenticates every successful post row. -/
theorem reflects_at_support (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      currentContext currentEvidence (receipt.formation.function capturedEnvironment).source
      ((receipt.formation.support capturedEnvironment).certificates
        (receipt.formation.support capturedEnvironment).body.readFuel
        (receipt.formation.function capturedEnvironment).source currentContext) faults size := by
  intro childScope child output actual actualNode found _sourceTyped mapping world administrative environment canonical native
    actualContext before store ξ value finalStore _environments heaps _locals _agrees _typed initial admitted completed
  obtain ⟨sameId, actualLiteral⟩ := certificate_at_support literalRoot literalId node receipt chosen capturedEnvironment facts actual
  subst child
  obtain ⟨other, otherFound, literal, selected⟩ := actualLiteral
  have sameNode := Option.some.inj (otherFound.symm.trans facts.found)
  subst other
  have nodeEq := Option.some.inj (found.symm.trans facts.found)
  subst actualNode
  have nativeWord := literal_word_type literal facts.wordType
  rw [nativeWord] at literal
  have numeric := selected.evidence ledger runtime currentEvidence
  obtain ⟨sourceValue, coreValue, raw, related, evaluated⟩ := literal.evaluates_with_evidence (registry := registry)
    functions (Program.ofChecked compiled.sourceProgram) currentContext currentEvidence numeric
    _ environment before mapping world native store ξ
  obtain ⟨sameValue, sameStore⟩ := evaluation_deterministic evaluated completed.sound
  subst value
  subst finalStore
  have sourceTrace : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      currentContext currentEvidence (receipt.formation.function capturedEnvironment).source
      environment before literalId sourceValue before := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound facts.found) raw
    rw [facts.coercions]
    exact .nil
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size (.value sourceTrace)
  refine ⟨sourceSize, .value sourceValue, before, mapping, world, sized, .value (by simpa only [CompatibleAmbientHeap.payloadModel, nativeWord] using related), heaps,
    .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial, admitted.rows, ?_⟩
  intro value same
  cases same
  rw [facts.wordType]
  exact ⟨word_typed literal raw, admitted.heap⟩

end Admitted
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenWordLiteralExpressionBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicCoupledForHeaderBounds
/-! The public Header supplies full Source typing and its own issued diagnostics.
The joint receipt keeps the actual selected assignment preparations. Strict
children feed the existing Header core at each genuine validity context. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicCoupledForHeaderBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory (NativeFrame)
open TypedLexicalWhile (Scope ValuesContext)
open ProtectedForHeader (Tree)
open ProtectedStateTransition ProtectedForHeader.Stateful ProtectedForHeader.Stateful.WithReady
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (receipt : CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds.PublicReceipt header)
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {administrative : Core.Context}
  {continuation : SourceSemantics.Context → Scope → Expr → Prop}
  {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
  (functions : FunctionModel compiled.compatible.checked.catalog ambient)
  (ambientDefinitions : ambient.definitions = compiled.indexed.layouts.definitions)
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {faults : FunctionCalls.FaultRep}
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (condition : Location → NativeFrame → Prop)
  (producer : OrdinaryAllocation.Producer callerProtocol header.layouts compiled.indexed.ancestry.layout.frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
  (acquire : ∀ location native, condition location native → OrdinaryAllocation.ReadyAt producer location native)
  (stateTransport : AdministrativeTransport callerProtocol) (stateBindings : Bindings callerProtocol)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {control : ControlContext} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {factory : AssignmentDiagnosticOrigins.Factory true diagnosticPolicy header.function.source
    (GenericAssignmentDiagnostics.token receipt.original.prepared.compilation.own.assignments)}
  {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
  (diagnosticsFound : compiled.indexed.base.diagnostics = some diagnostics)
  {table : SourceCoreFaultSites.Table} (rebuilt : diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep receipt.original.prepared.compilation.own.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep receipt.original.prepared.compilation.own.assignments reason token → faults reason token)

include ambientDefinitions extension faithful observations producer acquire stateTransport stateBindings wellFormed diagnosticsFound rebuilt operandIncluded unaryIncluded in
theorem preserves_fault_coupled_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (runtime : ∀ context, validity context → Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context header.function.source)
    (covers : ∀ context, validity context → header.function.evidence.Covers context)
    (signatures : ∀ context, validity context → context.signatures = compiled.compatible.checked.signatures)
    (interprets : ∀ context, validity context → CallableIndexedOwnedPublicPreparedAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := certificates) (administrative := administrative)
      (factory := factory) (faults := faults) (registry := registry) header bridge receipt functions table)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends header.function.source.owner context binder next → validity next) (budget : Nat)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context header.function.evidence header.function.source (certificates context) faults size)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame header.globals header.onError
      (.initial compiled.compatible.checked) header.function.source certificates ambient.definitions administrative header.output continuation
      context scope items code) {plan : EmittedDiagnosticPlan.Plan factory}
    (coupled : GenericForHeader.Coupled factory
      (fun site root => receipt.original.prepared.diagnostics.placeReason header.named.signature.key site root none)
      (fun site root raw => receipt.original.prepared.diagnostics.placeReason header.named.signature.key site root (some raw)) tree plan)
    (tokens : EmittedDiagnosticTokenPlan.TokensFor factory
      (fun site root => receipt.original.prepared.compilation.own.assignments.reasonAt site root .bitNot) plan)
    (valid : validity context) {staticFinal : SourceSemantics.Context}
    (itemTyping : ForItemsHaveType header.function.source control context items staticFinal)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + header.globals]? = some (.cellRef compiled.indexed.ancestry.layout.frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : (readiness bridge).Ready context state) {reason : Dynamic.SemanticFault}
    {size : Nat} (trace : SourceExecutionSize.ForItemsFault (Program.ofChecked compiled.sourceProgram) size context header.function.evidence header.function.source environment before items finalContext reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType header.output) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      FaultTransition (readiness bridge) state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨first, issued⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.assignments_at_header
    receipt.original.prepared receipt.diagnostic receipt.original.aligned
  have definitions := header.definitions_eq.trans ambientDefinitions.symm
  have registered : compiled.indexed.ancestry.layout.frame.Registered ambient.definitions :=
    ambientDefinitions.symm ▸ header.registered
  exact ProtectedForHeader.Stateful.WithReady.preserves_fault_coupled_bounded_for
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (source := header.function.source) (certificates := certificates) (ambient := ambient)
      (functions := functions) (definitions := definitions) (registered := registered)
      (program := Program.ofChecked compiled.sourceProgram) (evidence := header.function.evidence)
      (protocol := callerProtocol) (condition := condition) (producer := producer) (acquire := acquire)
      (stateTransport := stateTransport) (stateBindings := stateBindings)
      (readiness := readiness bridge) (facts := ProtectedStateForHeaderSourceSites.Facts header.function.source control)
      (itemFacts := ProtectedStateForHeaderSourceSites.ItemFacts header.function.source control)
      (exprFacts := ProtectedStateForHeaderSourceSites.ExpressionFacts header.function.source)
      (assignmentFacts := SourceAssignmentHasType header.function.source) (snapshotFacts := SourceBitNotAssignmentValid header.function.source)
      (sites := ProtectedStateForHeaderSourceSites.sites (Program.ofChecked compiled.sourceProgram) header.function.evidence header.function.source control header.unique)
      (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge stateBindings header.function.source)
      (SourceDiagnosticTyping.header_diagnostic_typed header wellFormed).1 issued unaryIncluded
      validity (CallableIndexedOwnedAdmittedForHeaderReadiness.snapshot_transfers bridge header.function.evidence wellFormed validity runtime covers) extend budget
      (fun context valid => CallableIndexedOwnedAdmittedForHeaderReadiness.assignment_prefix
        (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
        (certificate := certificates context) (administrative := administrative) (faults := faults)
        bridge functions extension header.function.evidence
        stateTransport faithful observations header.unique wellFormed (runtime context valid) (covers context valid) budget (boundedMeaning context valid))
      (fun context valid => CallableIndexedOwnedPublicPreparedAssignmentReadiness.assignment_fault header bridge receipt functions extension header.function.evidence
        stateTransport faithful observations header.unique wellFormed diagnosticsFound rebuilt (interprets context valid)
        operandIncluded (signatures context valid) (runtime context valid) (covers context valid) budget (boundedMeaning context valid))
      (fun context valid child within => CallableIndexedOwnedAdmittedLexicalReadiness.preserves_at bridge _ (boundedMeaning context valid child within))
      tree coupled tokens valid ⟨staticFinal, itemTyping⟩ environments heaps locals agrees actualTyped reference read unmapped state gate ready trace bounded

include ambientDefinitions extension faithful observations producer acquire stateTransport stateBindings wellFormed diagnosticsFound rebuilt operandIncluded unaryIncluded in
theorem reflects_coupled_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (runtime : ∀ context, validity context → Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context header.function.source)
    (covers : ∀ context, validity context → header.function.evidence.Covers context)
    (signatures : ∀ context, validity context → context.signatures = compiled.compatible.checked.signatures)
    (interprets : ∀ context, validity context → CallableIndexedOwnedPublicPreparedAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := certificates) (administrative := administrative)
      (factory := factory) (faults := faults) (registry := registry) header bridge receipt functions table)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends header.function.source.owner context binder next → validity next) (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (boundedReflection : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context header.function.evidence header.function.source (certificates context) faults size))    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame header.globals header.onError
      (.initial compiled.compatible.checked) header.function.source certificates ambient.definitions administrative header.output continuation
      context scope items code) {plan : EmittedDiagnosticPlan.Plan factory}
    (coupled : GenericForHeader.Coupled factory
      (fun site root => receipt.original.prepared.diagnostics.placeReason header.named.signature.key site root none)
      (fun site root raw => receipt.original.prepared.diagnostics.placeReason header.named.signature.key site root (some raw)) tree plan)
    (tokens : EmittedDiagnosticTokenPlan.TokensFor factory
      (fun site root => receipt.original.prepared.compilation.own.assignments.reasonAt site root .bitNot) plan)
    (valid : validity context) {staticFinal : SourceSemantics.Context}
    (itemTyping : ForItemsHaveType header.function.source control context items staticFinal)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + header.globals]? = some (.cellRef compiled.indexed.ancestry.layout.frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : (readiness bridge).Ready context state)
    {size : Nat} (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) (bounded : size ≤ budget) :
    ResultAtFor (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
      callerProtocol (readiness bridge) condition validity size registry functions (Program.ofChecked compiled.sourceProgram) header.function.source header.solved header.function.evidence
      administrative compiled.indexed.ancestry.layout.frame header.globals contextLocation native header.output faults continuation
      context environment ⟨scope, mapping, world, before, store, canonical⟩ state items value finalStore := by
  obtain ⟨first, issued⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.assignments_at_header
    receipt.original.prepared receipt.diagnostic receipt.original.aligned
  have definitions := header.definitions_eq.trans ambientDefinitions.symm
  have registered : compiled.indexed.ancestry.layout.frame.Registered ambient.definitions :=
    ambientDefinitions.symm ▸ header.registered
  exact ProtectedForHeader.Stateful.WithReady.reflects_coupled_bounded_for
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (source := header.function.source) (certificates := certificates) (solved := header.solved) (ambient := ambient)
      (functions := functions) (definitions := definitions) (registered := registered)
      (program := Program.ofChecked compiled.sourceProgram) (evidence := header.function.evidence)
      (protocol := callerProtocol) (condition := condition) (producer := producer) (acquire := acquire)
      (stateTransport := stateTransport) (stateBindings := stateBindings)
      (readiness := readiness bridge) (facts := ProtectedStateForHeaderSourceSites.Facts header.function.source control)
      (itemFacts := ProtectedStateForHeaderSourceSites.ItemFacts header.function.source control)
      (exprFacts := ProtectedStateForHeaderSourceSites.ExpressionFacts header.function.source)
      (assignmentFacts := SourceAssignmentHasType header.function.source) (snapshotFacts := SourceBitNotAssignmentValid header.function.source)
      (sites := ProtectedStateForHeaderSourceSites.sites (Program.ofChecked compiled.sourceProgram) header.function.evidence header.function.source control header.unique)
      (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge stateBindings header.function.source)
      (SourceDiagnosticTyping.header_diagnostic_typed header wellFormed).1 issued unaryIncluded
      validity (CallableIndexedOwnedAdmittedForHeaderReadiness.snapshot_transfers bridge header.function.evidence wellFormed validity runtime covers) extend budget
      (fun context valid => CallableIndexedOwnedPublicPreparedAssignmentReadiness.assignment_reflection header bridge receipt functions extension header.function.evidence
        stateTransport faithful observations header.unique wellFormed diagnosticsFound rebuilt (interprets context valid)
        operandIncluded (signatures context valid) (runtime context valid) (covers context valid) budget functionTypes (boundedReflection context valid))
      (fun context valid child within => CallableIndexedOwnedAdmittedLexicalReadiness.reflects_at bridge _ (boundedReflection context valid child within))
      tree coupled tokens valid ⟨staticFinal, itemTyping⟩ environments heaps locals agrees actualTyped reference read unmapped state gate ready evaluated bounded

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicCoupledForHeaderBounds
end
