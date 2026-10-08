import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedBodyRuntimeBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaNestedEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaBodyContinuations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedFunctionFinishBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPreparedFlowBounds

/-! The actual chosen Support supplies nested flow at its real parameter pool.
Raw packet and typing producers supply admission without legacy body packaging;
typed finish retains the same returned packet before finite base projection. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenNestedLambdaBodyContinuations
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedPreparedMixedBodyCompilerFactory
open CallableIndexedOwnedPreparedMixedBodySiteInputs
open RecursiveNamedCatalogInvocationBounds (Below)

section Parameters
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (support : Support code) (origin : SourceOrigin support history)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (first : State headers keys ⟨callerScope, mapping, world, before, store, canonical⟩)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments support.body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows first)

include stable in
private theorem parameter_rows {next : NativeFrame} {nextGhost : GhostFrame} {metadata : Option MetadataState}
    {final : ProtectedStateTransition.Index} (reached : State headers keys final)
    (carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table next nextGhost metadata)
    (parameters : AdministrativePreserved mapping
      (store.set owner.key.frameLocation (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame next))
      final.mapping final.store) :
    CallableIndexedOwnedIndirectExpressionHeads.StableRows reached :=
  CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
    (install first owner.position (.stable carried)) reached
    (CallableIndexedOwnedAdmittedBodyEntries.stable_rows_install first stable owner.position carried) parameters

include origin observed prefixContext beforeTyped argumentsTyped stable in
/-- The Source entry supplies its exact packet, raw typing and every row's history. -/
theorem source_parameter_admission
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history support.body.toBody.toContext functions registry arguments nativeArguments before store owner.key.frameLocation
      (first.rows owner.position).authority.current (first.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (spine : entry.entry.canonical = added ++ captured.canonical)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ reached ∧
    SourceReceipt (Program.ofChecked compiled.sourceProgram) function support.body.context entry.entry.environment entry.entry.heap ∧
    CallableIndexedOwnedIndirectExpressionHeads.StableRows reached :=
  ⟨CallableIndexedOwnedLambdaNestedEntries.source_packet captured code history support.body.toBody.toContext
    functions owner support.caller observed prefixContext origin.metadata first entry added length spine reached,
    CallableIndexedOwnedTypedLambdaBodyContinuations.source_receipt captured code history support.body.toBody
      functions owner first beforeTyped argumentsTyped entry,
    parameter_rows owner first stable reached entry.nextHistory entry.entry.frame⟩

include origin observed prefixContext beforeTyped argumentsTyped stable in
/-- The native prefix keeps its own allocation and independently typed Source heap. -/
theorem native_parameter_admission
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history support.body.toBody.toContext functions registry arguments before store owner.key.frameLocation
      (first.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ reached ∧
    SourceReceipt (Program.ofChecked compiled.sourceProgram) function support.body.context entry.environment entry.heap ∧
    CallableIndexedOwnedIndirectExpressionHeads.StableRows reached :=
  ⟨CallableIndexedOwnedLambdaNestedEntries.native_packet captured code history support.body.toBody.toContext
    functions owner support.caller observed prefixContext origin.metadata first entry reached,
    CallableIndexedOwnedTypedLambdaBodyContinuations.native_receipt captured code history support.body.toBody
      functions owner first beforeTyped argumentsTyped entry,
    parameter_rows owner first stable reached entry.nextHistory entry.frame⟩
end Parameters

section Chosen
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {formationContext : SourceSemantics.Context} {formationEvidence : Dynamic.EvidenceEnvironment}
  {formationScope : SourceCoreLocalCell.Scope} {formationId : ExpressionId} {formationCode : SourceCoreBasic.LoweredExpr}
  (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
    formationContext formationEvidence formationScope formationId formationCode)
  (chosen : ChosenFactory root expressionSyntax receipt) (environment : Dynamic.Environment)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)

/-- The actual solved ledger accompanies independent Source runtime validity. -/
def Validity (context : SourceSemantics.Context) : Prop :=
  CompatibleRuntimeContextValidity.Valid (receipt.formation.code environment).compilation.solvedRequirements context (receipt.formation.function environment).evidence ∧
    Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (receipt.formation.function environment).source

/-- The owning nested protocol remains distinct from the base ordinary family. -/
def NestedFlowPreserves (size : Nat) : Prop :=
  RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
    (readiness (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (ProtectedStateImperativeTypedSourceSites.Facts (receipt.formation.function environment).source ((receipt.formation.support environment).expressionSyntax (receipt.formation.function environment).source))
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) (Program.ofChecked compiled.sourceProgram) (receipt.formation.function environment).evidence (Validity receipt environment)
    (source := (receipt.formation.function environment).source) (context := ((receipt.formation.support environment).body).context) (registry := registry) (faults := faults)
    (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
    (administrative := RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
    size (scope := (receipt.formation.code environment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ formationScope)
    true (receipt.formation.function environment).body (receipt.formation.function environment).resultType (receipt.formation.code environment).receipt.resultCore ((receipt.formation.support environment).body).flow

def NestedFlowReflects (size : Nat) : Prop :=
  RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
    (readiness (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (ProtectedStateImperativeTypedSourceSites.Facts (receipt.formation.function environment).source ((receipt.formation.support environment).expressionSyntax (receipt.formation.function environment).source))
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) (Program.ofChecked compiled.sourceProgram) (receipt.formation.function environment).evidence (Validity receipt environment)
    (source := (receipt.formation.function environment).source) (context := ((receipt.formation.support environment).body).context) (registry := registry) (faults := faults)
    (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
    (administrative := RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
    size (scope := (receipt.formation.code environment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ formationScope)
    true (receipt.formation.function environment).body (receipt.formation.function environment).resultType (receipt.formation.code environment).receipt.resultCore ((receipt.formation.support environment).body).flow

variable
  (domains : ∀ context, Validity receipt environment context → ∀ childScope,
    DomainAt root expressionSyntax ((receipt.formation.support environment).body).readFuel context formationEvidence childScope headers)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : ∀ context, Validity receipt environment context → RequirementIdsUnique context)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)
  (noIndirect : CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirect (source caller.named))
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) identities)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (rootReasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((rootReasonAt id).add tag))
  {table : SourceCoreFaultSites.Table}
  (rebuilt : (receipt.formation.support environment).issued.diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep (receipt.formation.support environment).issued.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep (receipt.formation.support environment).issued.assignments reason token → faults reason token)
  (interprets : ∀ context, Validity receipt environment context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := (receipt.formation.support environment).certificates ((receipt.formation.support environment).body).readFuel (receipt.formation.function environment).source)
      (administrative := RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
      (factory := CallableIndexedOwnedContextualLambdaJointStaticReceipts.trackedFactory (receipt.formation.support environment).diagnosticPolicy (receipt.formation.function environment).source (receipt.formation.support environment).issued.invalidOperand)
      (faults := faults) (registry := registry) (receipt.formation.support environment).issued (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) table)

namespace ForModel
section
variable
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))

/-- The owning nested protocol remains distinct from the base ordinary family. -/
def NestedFlowPreserves (size : Nat) : Prop :=
  RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
    (readiness (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (ProtectedStateImperativeTypedSourceSites.Facts (receipt.formation.function environment).source ((receipt.formation.support environment).expressionSyntax (receipt.formation.function environment).source))
    functions (Program.ofChecked compiled.sourceProgram) (receipt.formation.function environment).evidence (Validity receipt environment)
    (source := (receipt.formation.function environment).source) (context := ((receipt.formation.support environment).body).context) (registry := registry) (faults := faults)
    (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
    (administrative := RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
    size (scope := (receipt.formation.code environment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ formationScope)
    true (receipt.formation.function environment).body (receipt.formation.function environment).resultType (receipt.formation.code environment).receipt.resultCore ((receipt.formation.support environment).body).flow

def NestedFlowReflects (size : Nat) : Prop :=
  RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
    (readiness (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (ProtectedStateImperativeTypedSourceSites.Facts (receipt.formation.function environment).source ((receipt.formation.support environment).expressionSyntax (receipt.formation.function environment).source))
    functions (Program.ofChecked compiled.sourceProgram) (receipt.formation.function environment).evidence (Validity receipt environment)
    (source := (receipt.formation.function environment).source) (context := ((receipt.formation.support environment).body).context) (registry := registry) (faults := faults)
    (frameLayout := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
    (administrative := RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
    size (scope := (receipt.formation.code environment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ formationScope)
    true (receipt.formation.function environment).body (receipt.formation.function environment).resultType (receipt.formation.code environment).receipt.resultCore ((receipt.formation.support environment).body).flow

end
end ForModel

namespace ForModel
section
variable
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (members : CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.Members
    (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    caller root expressionSyntax functions)
  (observationsGeneric : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypesGeneric : FunctionRuntimeViews functions)
  (interpretsGeneric : ∀ context, Validity receipt environment context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := (receipt.formation.support environment).certificates ((receipt.formation.support environment).body).readFuel (receipt.formation.function environment).source)
      (administrative := RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
      (factory := CallableIndexedOwnedContextualLambdaJointStaticReceipts.trackedFactory (receipt.formation.support environment).diagnosticPolicy (receipt.formation.function environment).source (receipt.formation.support environment).issued.invalidOperand)
      (faults := faults) (registry := registry) (receipt.formation.support environment).issued (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) functions table)

include functions members profile chosen domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero noIndirect
  extension faithful observationsGeneric functionTypesGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric in
/-- The same chosen Support supplies nested flow through the original prepared core. -/
theorem preserves_flow (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i)) :
    RecursiveNamedHeaderContracts.AtMost budget
      (NestedFlowPreserves (functions := functions) receipt environment owner (headers := headers) (registry := registry) (faults := faults)) := by
  have meaning : ∀ context, Validity receipt environment context →
      RecursiveNamedHeaderContracts.AtMost budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          context (receipt.formation.function environment).evidence (receipt.formation.function environment).source ((receipt.formation.support environment).certificates ((receipt.formation.support environment).body).readFuel (receipt.formation.function environment).source context) faults size) := by
    intro context valid size measured
    have ledger : CompatibleRuntimeContextValidity.Valid (CallableIndexedNamedGeneration.context compiled.indexed caller.named).solvedRequirements context formationEvidence := by
      have actual := valid.1
      change CompatibleRuntimeContextValidity.Valid (receipt.formation.code environment).compilation.solvedRequirements context formationEvidence at actual
      rw [(receipt.formation.support environment).compilation] at actual
      exact actual
    change CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions)
      context formationEvidence (receipt.formation.function environment).source
      ((receipt.formation.support environment).certificates (receipt.formation.support environment).body.readFuel
        (receipt.formation.function environment).source context) faults size
    exact CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.ForModel.preserves_at_support
      (functions := functions) (members := members)
      (root := root) (expressionSyntax := expressionSyntax) (profile := profile) (owner := owner)
      (wellFormed := wellFormed) (sameLayouts := sameLayouts) (owners := owners) (complete := complete)
      (globals := globals) (slots := slots) (prefixZero := prefixZero) (noIndirect := noIndirect)
      (receipt := receipt) (chosen := chosen) (environment := environment) (domains := domains context valid) (valid := ledger)
      valid.2 extension faithful observationsGeneric functionTypesGeneric uninitialized missing outer budget size
      measured within ih (idsUnique context valid)
  exact CallableIndexedOwnedContextualLambdaPreparedFlowBounds.preserves_flow
    (active := (receipt.formation.code environment).active) (onError := (receipt.formation.code environment).allocationError)
    (expressionSyntax := (receipt.formation.support environment).expressionSyntax (receipt.formation.function environment).source)
    (certificates := (receipt.formation.support environment).certificates ((receipt.formation.support environment).body).readFuel (receipt.formation.function environment).source)
    (administrative := RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
    (registry := registry) (faults := faults)
    (factory := CallableIndexedOwnedContextualLambdaJointStaticReceipts.trackedFactory (receipt.formation.support environment).diagnosticPolicy (receipt.formation.function environment).source (receipt.formation.support environment).issued.invalidOperand)
    (receipt.formation.support environment).issued (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) functions rfl (CallableIndexedAmbient.frame_registered compiled.indexed)
    extension (receipt.formation.function environment).evidence faithful observationsGeneric (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (CallableIndexedOwnedNestedCanonicalState.markedProducer (headers := headers) owner caller
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    (fun _ _ stable => CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner
      (headers := headers) owner caller (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) stable)
    (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner caller)
    (CallableIndexedOwnedNestedCanonicalState.bindings (headers := headers) owner caller)
    ((receipt.formation.support environment).body).unique wellFormed rebuilt operandIncluded unaryIncluded interpretsGeneric budget
    (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters ((receipt.formation.support environment).body).frame ((receipt.formation.support environment).body).extended).1
    meaning ((receipt.formation.support environment).body).prepared
end
end ForModel

include chosen domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero noIndirect
  extension faithful observations functionTypes uninitialized missing rebuilt operandIncluded unaryIncluded interprets in
/-- The same chosen Support supplies nested flow through the original prepared core. -/
theorem preserves_flow (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner i)) :
    RecursiveNamedHeaderContracts.AtMost budget
      (NestedFlowPreserves receipt environment profile owner (headers := headers) (registry := registry) (faults := faults)) := by
  exact ForModel.preserves_flow
    (functions := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    (members := fun _i _history member => member.formed.represents)
    (root := root) (expressionSyntax := expressionSyntax) (receipt := receipt) (chosen := chosen) (environment := environment) (profile := profile) (owner := owner) (domains := domains) (wellFormed := wellFormed) (sameLayouts := sameLayouts) (owners := owners) (idsUnique := idsUnique) (complete := complete) (globals := globals) (slots := slots) (prefixZero := prefixZero) (noIndirect := noIndirect) (extension := extension) (faithful := faithful) (uninitialized := uninitialized) (missing := missing) (rebuilt := rebuilt) (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded) (observationsGeneric := observations) (functionTypesGeneric := functionTypes) (interpretsGeneric := interprets)
    outer budget within ih

namespace ForModel
section
variable
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (members : CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.Members
    (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    caller root expressionSyntax functions)
  (observationsGeneric : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypesGeneric : FunctionRuntimeViews functions)
  (interpretsGeneric : ∀ context, Validity receipt environment context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := (receipt.formation.support environment).certificates ((receipt.formation.support environment).body).readFuel (receipt.formation.function environment).source)
      (administrative := RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
      (factory := CallableIndexedOwnedContextualLambdaJointStaticReceipts.trackedFactory (receipt.formation.support environment).diagnosticPolicy (receipt.formation.function environment).source (receipt.formation.support environment).issued.invalidOperand)
      (faults := faults) (registry := registry) (receipt.formation.support environment).issued (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) functions table)

include functions members profile chosen domains wellFormed sameLayouts complete globals slots prefixZero noIndirect
  extension faithful observationsGeneric functionTypesGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric in
/-- The same chosen Support supplies nested flow through the original prepared core. -/
theorem reflects_flow (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i)) :
    Below budget
      (NestedFlowReflects (functions := functions) receipt environment owner (headers := headers) (registry := registry) (faults := faults)) := by
  have meaning : ∀ context, Validity receipt environment context →
      Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          context (receipt.formation.function environment).evidence (receipt.formation.function environment).source ((receipt.formation.support environment).certificates ((receipt.formation.support environment).body).readFuel (receipt.formation.function environment).source context) faults size) := by
    intro context valid size measured
    have ledger : CompatibleRuntimeContextValidity.Valid (CallableIndexedNamedGeneration.context compiled.indexed caller.named).solvedRequirements context formationEvidence := by
      have actual := valid.1
      change CompatibleRuntimeContextValidity.Valid (receipt.formation.code environment).compilation.solvedRequirements context formationEvidence at actual
      rw [(receipt.formation.support environment).compilation] at actual
      exact actual
    change CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions)
      context formationEvidence (receipt.formation.function environment).source
      ((receipt.formation.support environment).certificates (receipt.formation.support environment).body.readFuel
        (receipt.formation.function environment).source context) faults size
    exact CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.ForModel.reflects_at_support
      (functions := functions) (members := members)
      (root := root) (expressionSyntax := expressionSyntax) (profile := profile) (owner := owner)
      (wellFormed := wellFormed) (sameLayouts := sameLayouts) (complete := complete)
      (globals := globals) (slots := slots) (prefixZero := prefixZero) (noIndirect := noIndirect)
      (receipt := receipt) (chosen := chosen) (environment := environment) (domains := domains context valid) (valid := ledger)
      valid.2 extension faithful observationsGeneric functionTypesGeneric uninitialized missing outer budget size
      (Nat.le_of_lt measured) within ih
  exact CallableIndexedOwnedContextualLambdaPreparedFlowBounds.reflects_flow
    (active := (receipt.formation.code environment).active) (onError := (receipt.formation.code environment).allocationError)
    (expressionSyntax := (receipt.formation.support environment).expressionSyntax (receipt.formation.function environment).source)
    (certificates := (receipt.formation.support environment).certificates ((receipt.formation.support environment).body).readFuel (receipt.formation.function environment).source)
    (administrative := RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
    (registry := registry) (faults := faults)
    (factory := CallableIndexedOwnedContextualLambdaJointStaticReceipts.trackedFactory (receipt.formation.support environment).diagnosticPolicy (receipt.formation.function environment).source (receipt.formation.support environment).issued.invalidOperand)
    (receipt.formation.support environment).issued (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) functions rfl (CallableIndexedAmbient.frame_registered compiled.indexed)
    extension (receipt.formation.function environment).evidence faithful observationsGeneric (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (CallableIndexedOwnedNestedCanonicalState.markedProducer (headers := headers) owner caller
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    (fun _ _ stable => CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner
      (headers := headers) owner caller (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) stable)
    (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner caller)
    (CallableIndexedOwnedNestedCanonicalState.bindings (headers := headers) owner caller)
    ((receipt.formation.support environment).body).unique wellFormed rebuilt operandIncluded unaryIncluded interpretsGeneric budget
    (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters ((receipt.formation.support environment).body).frame ((receipt.formation.support environment).body).extended).1
    functionTypesGeneric meaning ((receipt.formation.support environment).body).prepared
end
end ForModel

include chosen domains wellFormed sameLayouts complete globals slots prefixZero noIndirect
  extension faithful observations functionTypes uninitialized missing rebuilt operandIncluded unaryIncluded interprets in
/-- The same chosen Support supplies nested flow through the original prepared core. -/
theorem reflects_flow (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner i)) :
    Below budget
      (NestedFlowReflects receipt environment profile owner (headers := headers) (registry := registry) (faults := faults)) := by
  exact ForModel.reflects_flow
    (functions := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    (members := fun _i _history member => member.formed.represents)
    (root := root) (expressionSyntax := expressionSyntax) (receipt := receipt) (chosen := chosen) (environment := environment) (profile := profile) (owner := owner) (domains := domains) (wellFormed := wellFormed) (sameLayouts := sameLayouts) (complete := complete) (globals := globals) (slots := slots) (prefixZero := prefixZero) (noIndirect := noIndirect) (extension := extension) (faithful := faithful) (uninitialized := uninitialized) (missing := missing) (rebuilt := rebuilt) (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded) (observationsGeneric := observations) (functionTypesGeneric := functionTypes) (interpretsGeneric := interprets)
    outer budget within ih

variable {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
  (captured : Captures compiled.indexed mapping world formationScope (receipt.formation.function environment).captured actual)
  (prefixContext : captured.administrative = (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller))
  (history : History (receipt.formation.code environment)) (origin : SourceOrigin (receipt.formation.support environment) history)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 formationScope captured.canonical owner.key.frameLocation)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (first : State headers keys ⟨callerScope, mapping, world, before, store, canonical⟩)
  (beforeTyped : Dynamic.HeapWellTyped (receipt.formation.function environment).context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes (receipt.formation.function environment).context before arguments (receipt.formation.support environment).body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows first)

private theorem body_facts {sourceEnvironment : Dynamic.Environment} {heap : Dynamic.Heap}
    (source : SourceReceipt (Program.ofChecked compiled.sourceProgram) (receipt.formation.function environment) (receipt.formation.support environment).body.context sourceEnvironment heap) :
    (ProtectedStateImperativeTypedSourceSites.Facts (receipt.formation.function environment).source ((receipt.formation.support environment).expressionSyntax (receipt.formation.function environment).source)) (receipt.formation.support environment).body.context true (receipt.formation.function environment).body (receipt.formation.function environment).resultType := by
  obtain ⟨final, facts, typed, _⟩ := source.bodyTyped
  exact ⟨(receipt.formation.support environment).body.syntaxTree, { returnType := (receipt.formation.function environment).resultType }, final, facts, typed⟩

namespace ForModel
section
variable
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (members : CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.Members
    (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    caller root expressionSyntax functions)
  (observationsGeneric : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypesGeneric : FunctionRuntimeViews functions)
  (interpretsGeneric : ∀ context, Validity receipt environment context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := (receipt.formation.support environment).certificates ((receipt.formation.support environment).body).readFuel (receipt.formation.function environment).source)
      (administrative := RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
      (factory := CallableIndexedOwnedContextualLambdaJointStaticReceipts.trackedFactory (receipt.formation.support environment).diagnosticPolicy (receipt.formation.function environment).source (receipt.formation.support environment).issued.invalidOperand)
      (faults := faults) (registry := registry) (receipt.formation.support environment).issued (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) functions table)

include functions members profile chosen domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero noIndirect
  extension faithful observationsGeneric functionTypesGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  origin observed beforeTyped argumentsTyped stable in
/-- Typed finish returns the same actual nested pool with its Packet and readiness. -/
theorem source_at_entry (outer budget size : Nat) (strict : size < budget) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i))
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt environment captured prefixContext) (receipt.formation.code environment) history (receipt.formation.support environment).body.toBody.toContext functions registry arguments nativeArguments before store owner.key.frameLocation
      (first.rows owner.position).authority.current (first.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = (receipt.formation.code environment).receipt.loweredParameters.length)
    (spine : entry.entry.canonical = added ++ captured.canonical)
    (reached : State headers keys ⟨((receipt.formation.code environment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ formationScope), entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) size (receipt.formation.function environment) (receipt.formation.support environment).body.context
      entry.entry.environment entry.entry.heap outcome after) :
    ∃ packet value finalStore finalMap finalWorld,
      Evaluates entry.entry.actualBody entry.entry.store ((receipt.formation.code environment).receipt.body.rename entry.entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld (receipt.formation.function environment).resultType (receipt.formation.code environment).receipt.resultCore faults outcome value ∧ CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.entry.mapping finalMap ∧ WorldExtends entry.entry.world finalWorld ∧
      AdministrativePreserved entry.entry.mapping entry.entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.entry.heap after ∧
      TypedMixedNamedBody.ReachedExit compiled.compatible.checked compiled.indexed.layouts.definitions finalMap finalWorld
        (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) (Program.ofChecked compiled.sourceProgram) (receipt.formation.function environment) (receipt.formation.support environment).body.context ((receipt.formation.code environment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ formationScope)
        entry.entry.environment entry.entry.heap after outcome ∧
      ProtectedStateTransition.FunctionFinish.Reached (readiness (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)) (receipt.formation.support environment).body.context outcome
        ⟨reached, packet⟩ ⟨((receipt.formation.code environment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ formationScope), finalMap, finalWorld, after, finalStore, entry.entry.canonical⟩ := by
  obtain ⟨packet, source, rows⟩ := source_parameter_admission
    (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt environment captured prefixContext) (receipt.formation.code environment) history (receipt.formation.support environment) origin functions owner observed rfl first
    beforeTyped argumentsTyped stable entry added length spine reached
  let nested : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State _ := ⟨reached, packet⟩
  have admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (receipt.formation.support environment).body.context nested := ⟨source.heapTyped, rows⟩
  have gate : CallableIndexedOwnedAllocationProducer.StableOwner keys owner.key.frameLocation entry.next :=
    ⟨owner.position, _, _, rfl, entry.nextHistory⟩
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, post⟩ :=
    CallableIndexedOwnedTypedFunctionFinishBounds.WithReady.preserves_at_emitted_with_source_receipt
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (functions := functions) (program := Program.ofChecked compiled.sourceProgram)
      (tree := (receipt.formation.support environment).body.tree) (projection := (receipt.formation.support environment).body.projection) (unique := (receipt.formation.support environment).body.unique)
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller) (readiness (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)) (CallableIndexedOwnedAllocationProducer.StableOwner keys) (ProtectedStateImperativeTypedSourceSites.Facts (receipt.formation.function environment).source ((receipt.formation.support environment).expressionSyntax (receipt.formation.function environment).source))
      (receipt.formation.support environment).body.emitted (Validity receipt environment) size
      (preserves_flow (functions := functions) (members := members) (root := root) (expressionSyntax := expressionSyntax) (receipt := receipt) (chosen := chosen) (environment := environment) (profile := profile) (owner := owner) (domains := domains) (wellFormed := wellFormed) (sameLayouts := sameLayouts) (owners := owners) (idsUnique := idsUnique) (complete := complete) (globals := globals) (slots := slots) (prefixZero := prefixZero) (noIndirect := noIndirect) (extension := extension) (faithful := faithful) (uninitialized := uninitialized) (missing := missing) (rebuilt := rebuilt) (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded) (observationsGeneric := observationsGeneric) (functionTypesGeneric := functionTypesGeneric) (interpretsGeneric := interpretsGeneric) outer size (Nat.le_trans (Nat.le_of_lt strict) within) ih size (Nat.le_refl size)) ⟨(receipt.formation.support environment).body.valid, source.runtime⟩
      (body_facts receipt environment source)
      entry.entry.environments entry.entry.heaps entry.entry.locals entry.entry.lookups entry.entry.actualTyped
      entry.entry.reference entry.entry.read entry.entry.unmapped nested gate admitted source wellFormed trace
  exact ⟨packet, value, finalStore, finalMap, finalWorld, evaluated, represented, heaps,
    maps, worlds, frame, metadata, exit, post⟩
end
end ForModel

include chosen domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero noIndirect
  extension faithful observations functionTypes uninitialized missing rebuilt operandIncluded unaryIncluded interprets
  origin observed beforeTyped argumentsTyped stable in
/-- Typed finish returns the same actual nested pool with its Packet and readiness. -/
theorem source_at_entry (outer budget size : Nat) (strict : size < budget) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner i))
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt environment captured prefixContext) (receipt.formation.code environment) history (receipt.formation.support environment).body.toBody.toContext (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) registry arguments nativeArguments before store owner.key.frameLocation
      (first.rows owner.position).authority.current (first.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = (receipt.formation.code environment).receipt.loweredParameters.length)
    (spine : entry.entry.canonical = added ++ captured.canonical)
    (reached : State headers keys ⟨((receipt.formation.code environment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ formationScope), entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) size (receipt.formation.function environment) (receipt.formation.support environment).body.context
      entry.entry.environment entry.entry.heap outcome after) :
    ∃ packet value finalStore finalMap finalWorld,
      Evaluates entry.entry.actualBody entry.entry.store ((receipt.formation.code environment).receipt.body.rename entry.entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
        finalMap finalWorld (receipt.formation.function environment).resultType (receipt.formation.code environment).receipt.resultCore faults outcome value ∧ CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.entry.mapping finalMap ∧ WorldExtends entry.entry.world finalWorld ∧
      AdministrativePreserved entry.entry.mapping entry.entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.entry.heap after ∧
      TypedMixedNamedBody.ReachedExit compiled.compatible.checked compiled.indexed.layouts.definitions finalMap finalWorld
        (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) (Program.ofChecked compiled.sourceProgram) (receipt.formation.function environment) (receipt.formation.support environment).body.context ((receipt.formation.code environment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ formationScope)
        entry.entry.environment entry.entry.heap after outcome ∧
      ProtectedStateTransition.FunctionFinish.Reached (readiness (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)) (receipt.formation.support environment).body.context outcome
        ⟨reached, packet⟩ ⟨((receipt.formation.code environment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ formationScope), finalMap, finalWorld, after, finalStore, entry.entry.canonical⟩ := by
  exact ForModel.source_at_entry
    (functions := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    (members := fun _i _history member => member.formed.represents)
    (root := root) (expressionSyntax := expressionSyntax) (receipt := receipt) (chosen := chosen) (environment := environment) (profile := profile) (owner := owner) (domains := domains) (wellFormed := wellFormed) (sameLayouts := sameLayouts) (owners := owners) (idsUnique := idsUnique) (complete := complete) (globals := globals) (slots := slots) (prefixZero := prefixZero) (noIndirect := noIndirect) (extension := extension) (faithful := faithful) (uninitialized := uninitialized) (missing := missing) (rebuilt := rebuilt) (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded) (observationsGeneric := observations) (functionTypesGeneric := functionTypes) (interpretsGeneric := interprets) (captured := captured) (prefixContext := prefixContext) (history := history) (origin := origin) (observed := observed) (first := first) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped) (stable := stable)
    outer budget size strict within ih entry added length spine reached trace

namespace ForModel
section
variable
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (members : CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.Members
    (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    caller root expressionSyntax functions)
  (observationsGeneric : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypesGeneric : FunctionRuntimeViews functions)
  (interpretsGeneric : ∀ context, Validity receipt environment context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := (receipt.formation.support environment).certificates ((receipt.formation.support environment).body).readFuel (receipt.formation.function environment).source)
      (administrative := RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
      (factory := CallableIndexedOwnedContextualLambdaJointStaticReceipts.trackedFactory (receipt.formation.support environment).diagnosticPolicy (receipt.formation.function environment).source (receipt.formation.support environment).issued.invalidOperand)
      (faults := faults) (registry := registry) (receipt.formation.support environment).issued (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) functions table)

include functions members profile chosen domains wellFormed sameLayouts complete globals slots prefixZero noIndirect
  extension faithful observationsGeneric functionTypesGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  origin observed beforeTyped argumentsTyped stable in
/-- Typed finish returns the same actual nested pool with its Packet and readiness. -/
theorem native_at_entry (outer budget size : Nat) (strict : size < budget) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i))
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt environment captured prefixContext) (receipt.formation.code environment) history (receipt.formation.support environment).body.toBody.toContext functions registry arguments before store owner.key.frameLocation
      (first.rows owner.position).authority.current)
    (reached : State headers keys ⟨((receipt.formation.code environment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ formationScope), entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size entry.actual entry.store ((receipt.formation.code environment).receipt.body.rename entry.embedding) value finalStore) :
    ∃ packet sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) sourceSize (receipt.formation.function environment) (receipt.formation.support environment).body.context
        entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld (receipt.formation.function environment).resultType (receipt.formation.code environment).receipt.resultCore faults outcome value ∧ CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit compiled.compatible.checked compiled.indexed.layouts.definitions finalMap finalWorld
        (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) (Program.ofChecked compiled.sourceProgram) (receipt.formation.function environment) (receipt.formation.support environment).body.context ((receipt.formation.code environment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ formationScope)
        entry.environment entry.heap after outcome ∧
      ProtectedStateTransition.FunctionFinish.Reached (readiness (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)) (receipt.formation.support environment).body.context outcome
        ⟨reached, packet⟩ ⟨((receipt.formation.code environment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ formationScope), finalMap, finalWorld, after, finalStore, entry.canonical⟩ := by
  obtain ⟨packet, source, rows⟩ := native_parameter_admission
    (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt environment captured prefixContext) (receipt.formation.code environment) history (receipt.formation.support environment) origin functions owner observed rfl first
    beforeTyped argumentsTyped stable entry reached
  let nested : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State _ := ⟨reached, packet⟩
  have admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (receipt.formation.support environment).body.context nested := ⟨source.heapTyped, rows⟩
  have gate : CallableIndexedOwnedAllocationProducer.StableOwner keys owner.key.frameLocation entry.next :=
    ⟨owner.position, _, _, rfl, entry.nextHistory⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, post⟩ :=
    CallableIndexedOwnedTypedFunctionFinishBounds.WithReady.reflects_at_emitted_with_source_receipt
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (functions := functions) (program := Program.ofChecked compiled.sourceProgram)
      (tree := (receipt.formation.support environment).body.tree) (projection := (receipt.formation.support environment).body.projection) (unique := (receipt.formation.support environment).body.unique)
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller) (readiness (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)) (CallableIndexedOwnedAllocationProducer.StableOwner keys) (ProtectedStateImperativeTypedSourceSites.Facts (receipt.formation.function environment).source ((receipt.formation.support environment).expressionSyntax (receipt.formation.function environment).source))
      (receipt.formation.support environment).body.emitted (Validity receipt environment) budget size (Nat.le_of_lt strict)
      (reflects_flow (functions := functions) (members := members) (root := root) (expressionSyntax := expressionSyntax) (receipt := receipt) (chosen := chosen) (environment := environment) (profile := profile) (owner := owner) (domains := domains) (wellFormed := wellFormed) (sameLayouts := sameLayouts) (complete := complete) (globals := globals) (slots := slots) (prefixZero := prefixZero) (noIndirect := noIndirect) (extension := extension) (faithful := faithful) (uninitialized := uninitialized) (missing := missing) (rebuilt := rebuilt) (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded) (observationsGeneric := observationsGeneric) (functionTypesGeneric := functionTypesGeneric) (interpretsGeneric := interpretsGeneric) outer budget within ih) ⟨(receipt.formation.support environment).body.valid, source.runtime⟩
      (body_facts receipt environment source)
      entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped
      entry.reference entry.read entry.unmapped nested gate admitted source wellFormed completed
  exact ⟨packet, sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps,
    maps, worlds, frame, metadata, exit, post⟩
end
end ForModel

include chosen domains wellFormed sameLayouts complete globals slots prefixZero noIndirect
  extension faithful observations functionTypes uninitialized missing rebuilt operandIncluded unaryIncluded interprets
  origin observed beforeTyped argumentsTyped stable in
/-- Typed finish returns the same actual nested pool with its Packet and readiness. -/
theorem native_at_entry (outer budget size : Nat) (strict : size < budget) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner i))
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt environment captured prefixContext) (receipt.formation.code environment) history (receipt.formation.support environment).body.toBody.toContext (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) registry arguments before store owner.key.frameLocation
      (first.rows owner.position).authority.current)
    (reached : State headers keys ⟨((receipt.formation.code environment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ formationScope), entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size entry.actual entry.store ((receipt.formation.code environment).receipt.body.rename entry.embedding) value finalStore) :
    ∃ packet sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) sourceSize (receipt.formation.function environment) (receipt.formation.support environment).body.context
        entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
        finalMap finalWorld (receipt.formation.function environment).resultType (receipt.formation.code environment).receipt.resultCore faults outcome value ∧ CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit compiled.compatible.checked compiled.indexed.layouts.definitions finalMap finalWorld
        (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) (Program.ofChecked compiled.sourceProgram) (receipt.formation.function environment) (receipt.formation.support environment).body.context ((receipt.formation.code environment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ formationScope)
        entry.environment entry.heap after outcome ∧
      ProtectedStateTransition.FunctionFinish.Reached (readiness (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)) (receipt.formation.support environment).body.context outcome
        ⟨reached, packet⟩ ⟨((receipt.formation.code environment).receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ formationScope), finalMap, finalWorld, after, finalStore, entry.canonical⟩ := by
  exact ForModel.native_at_entry
    (functions := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    (members := fun _i _history member => member.formed.represents)
    (root := root) (expressionSyntax := expressionSyntax) (receipt := receipt) (chosen := chosen) (environment := environment) (profile := profile) (owner := owner) (domains := domains) (wellFormed := wellFormed) (sameLayouts := sameLayouts) (complete := complete) (globals := globals) (slots := slots) (prefixZero := prefixZero) (noIndirect := noIndirect) (extension := extension) (faithful := faithful) (uninitialized := uninitialized) (missing := missing) (rebuilt := rebuilt) (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded) (observationsGeneric := observations) (functionTypesGeneric := functionTypes) (interpretsGeneric := interprets) (captured := captured) (prefixContext := prefixContext) (history := history) (origin := origin) (observed := observed) (first := first) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped) (stable := stable)
    outer budget size strict within ih entry reached completed

namespace ForModel
section
variable
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (members : CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.Members
    (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    caller root expressionSyntax functions)
  (observationsGeneric : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypesGeneric : FunctionRuntimeViews functions)
  (interpretsGeneric : ∀ context, Validity receipt environment context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := (receipt.formation.support environment).certificates ((receipt.formation.support environment).body).readFuel (receipt.formation.function environment).source)
      (administrative := RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
      (factory := CallableIndexedOwnedContextualLambdaJointStaticReceipts.trackedFactory (receipt.formation.support environment).diagnosticPolicy (receipt.formation.function environment).source (receipt.formation.support environment).issued.invalidOperand)
      (faults := faults) (registry := registry) (receipt.formation.support environment).issued (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) functions table)

include functions members profile chosen domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero noIndirect
  extension faithful observationsGeneric functionTypesGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  origin observed beforeTyped argumentsTyped stable in
/-- The base continuation projects the same returned nested State and full pool. -/
theorem source_continuation (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i)) :
    CallableIndexedOwnedLambdaEntryBodyContracts.SourceContinuation
      (registry := registry) (faults := faults) (arguments := arguments) (nativeArguments := nativeArguments) (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt environment captured prefixContext) (receipt.formation.code environment) history (receipt.formation.support environment).body.toBody.toContext functions owner first budget := by
  intro entry added length spine reached size strict outcome after trace
  obtain ⟨packet, value, finalStore, finalMap, finalWorld, evaluated, represented, heaps,
      maps, worlds, frame, metadata, exit, post⟩ :=
    source_at_entry (functions := functions) (members := members) (root := root) (expressionSyntax := expressionSyntax) (receipt := receipt) (chosen := chosen)
      (environment := environment) (profile := profile) (owner := owner) (domains := domains)
      (wellFormed := wellFormed) (sameLayouts := sameLayouts) (owners := owners) (idsUnique := idsUnique) (complete := complete)
      (globals := globals) (slots := slots) (prefixZero := prefixZero) (noIndirect := noIndirect)
      (extension := extension) (faithful := faithful) (observationsGeneric := observationsGeneric) (functionTypesGeneric := functionTypesGeneric)
      (uninitialized := uninitialized) (missing := missing) (rebuilt := rebuilt) (operandIncluded := operandIncluded)
      (unaryIncluded := unaryIncluded) (interpretsGeneric := interpretsGeneric) (captured := captured) (prefixContext := prefixContext)
      (history := history) (origin := origin) (observed := observed) (first := first)
      (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped) (stable := stable)
      outer budget size strict within ih entry added length spine reached trace
  obtain ⟨returned, related⟩ := post.forget
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps,
    maps, worlds, frame, metadata, exit, returned.val, (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller).related related⟩
end
end ForModel

include chosen domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero noIndirect
  extension faithful observations functionTypes uninitialized missing rebuilt operandIncluded unaryIncluded interprets
  origin observed beforeTyped argumentsTyped stable in
/-- The base continuation projects the same returned nested State and full pool. -/
theorem source_continuation (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner i)) :
    CallableIndexedOwnedLambdaEntryBodyContracts.SourceContinuation
      (registry := registry) (faults := faults) (arguments := arguments) (nativeArguments := nativeArguments) (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt environment captured prefixContext) (receipt.formation.code environment) history (receipt.formation.support environment).body.toBody.toContext (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner first budget := by
  exact ForModel.source_continuation
    (functions := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    (members := fun _i _history member => member.formed.represents)
    (root := root) (expressionSyntax := expressionSyntax) (receipt := receipt) (chosen := chosen) (environment := environment) (profile := profile) (owner := owner) (domains := domains) (wellFormed := wellFormed) (sameLayouts := sameLayouts) (owners := owners) (idsUnique := idsUnique) (complete := complete) (globals := globals) (slots := slots) (prefixZero := prefixZero) (noIndirect := noIndirect) (extension := extension) (faithful := faithful) (uninitialized := uninitialized) (missing := missing) (rebuilt := rebuilt) (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded) (observationsGeneric := observations) (functionTypesGeneric := functionTypes) (interpretsGeneric := interprets) (captured := captured) (prefixContext := prefixContext) (history := history) (origin := origin) (observed := observed) (first := first) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped) (stable := stable)
    outer budget within ih

namespace ForModel
section
variable
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (members : CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.Members
    (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    caller root expressionSyntax functions)
  (observationsGeneric : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypesGeneric : FunctionRuntimeViews functions)
  (interpretsGeneric : ∀ context, Validity receipt environment context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := (receipt.formation.support environment).certificates ((receipt.formation.support environment).body).readFuel (receipt.formation.function environment).source)
      (administrative := RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
      (factory := CallableIndexedOwnedContextualLambdaJointStaticReceipts.trackedFactory (receipt.formation.support environment).diagnosticPolicy (receipt.formation.function environment).source (receipt.formation.support environment).issued.invalidOperand)
      (faults := faults) (registry := registry) (receipt.formation.support environment).issued (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) functions table)

include functions members profile chosen domains wellFormed sameLayouts complete globals slots prefixZero noIndirect
  extension faithful observationsGeneric functionTypesGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  origin observed beforeTyped argumentsTyped stable in
/-- The base continuation projects the same returned nested State and full pool. -/
theorem native_continuation (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i)) :
    CallableIndexedOwnedLambdaEntryBodyContracts.NativeContinuation
      (registry := registry) (faults := faults) (arguments := arguments) (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt environment captured prefixContext) (receipt.formation.code environment) history (receipt.formation.support environment).body.toBody.toContext functions owner first budget := by
  intro entry reached size strict value finalStore completed
  obtain ⟨packet, sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps,
      maps, worlds, frame, metadata, exit, post⟩ :=
    native_at_entry (functions := functions) (members := members) (root := root) (expressionSyntax := expressionSyntax) (receipt := receipt) (chosen := chosen)
      (environment := environment) (profile := profile) (owner := owner) (domains := domains)
      (wellFormed := wellFormed) (sameLayouts := sameLayouts) (complete := complete)
      (globals := globals) (slots := slots) (prefixZero := prefixZero) (noIndirect := noIndirect)
      (extension := extension) (faithful := faithful) (observationsGeneric := observationsGeneric) (functionTypesGeneric := functionTypesGeneric)
      (uninitialized := uninitialized) (missing := missing) (rebuilt := rebuilt) (operandIncluded := operandIncluded)
      (unaryIncluded := unaryIncluded) (interpretsGeneric := interpretsGeneric) (captured := captured) (prefixContext := prefixContext)
      (history := history) (origin := origin) (observed := observed) (first := first)
      (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped) (stable := stable)
      outer budget size strict within ih entry reached completed
  obtain ⟨returned, related⟩ := post.forget
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps,
    maps, worlds, frame, metadata, exit, returned.val, (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller).related related⟩
end
end ForModel

include chosen domains wellFormed sameLayouts complete globals slots prefixZero noIndirect
  extension faithful observations functionTypes uninitialized missing rebuilt operandIncluded unaryIncluded interprets
  origin observed beforeTyped argumentsTyped stable in
/-- The base continuation projects the same returned nested State and full pool. -/
theorem native_continuation (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner i)) :
    CallableIndexedOwnedLambdaEntryBodyContracts.NativeContinuation
      (registry := registry) (faults := faults) (arguments := arguments) (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt environment captured prefixContext) (receipt.formation.code environment) history (receipt.formation.support environment).body.toBody.toContext (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner first budget := by
  exact ForModel.native_continuation
    (functions := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    (members := fun _i _history member => member.formed.represents)
    (root := root) (expressionSyntax := expressionSyntax) (receipt := receipt) (chosen := chosen) (environment := environment) (profile := profile) (owner := owner) (domains := domains) (wellFormed := wellFormed) (sameLayouts := sameLayouts) (complete := complete) (globals := globals) (slots := slots) (prefixZero := prefixZero) (noIndirect := noIndirect) (extension := extension) (faithful := faithful) (uninitialized := uninitialized) (missing := missing) (rebuilt := rebuilt) (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded) (observationsGeneric := observations) (functionTypesGeneric := functionTypes) (interpretsGeneric := interprets) (captured := captured) (prefixContext := prefixContext) (history := history) (origin := origin) (observed := observed) (first := first) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped) (stable := stable)
    outer budget within ih

end Chosen
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenNestedLambdaBodyContinuations
