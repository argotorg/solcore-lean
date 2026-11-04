import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.TerminalStatementOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LambdaReadyFamilies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ChosenLambdaFormation
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryLambdas

/-!
# Owned callables: chosen lambda bodies

Continuations of nested lambda bodies, and invocation and formation of chosen ordinary lambdas.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenNestedLambdaBodyContinuations
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
    (copied : Environment) (spine : entry.entry.canonical = added ++ copied)
    (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) :
    CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ reached ∧
    SourceReceipt (Program.ofChecked compiled.sourceProgram) function support.body.context entry.entry.environment entry.entry.heap ∧
    CallableIndexedOwnedIndirectExpressionHeads.StableRows reached :=
  ⟨CallableIndexedOwnedLambdaNestedEntries.source_packet captured code history support.body.toBody.toContext
    functions owner support.caller observed prefixContext origin.metadata first entry added length copied spine kept reached,
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

include functions members profile chosen domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero
  extension faithful observationsGeneric functionTypesGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric in
/-- The same chosen Support supplies nested flow through the original prepared core. -/
theorem preserves_flow_on
    (noIndirectOn : CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirectOn
      (source caller.named) (expressionSyntax (source caller.named))) (outer budget : Nat) (within : budget ≤ outer)
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
    exact CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.ForModel.preserves_support_on
      (functions := functions) (members := members)
      (root := root) (expressionSyntax := expressionSyntax) (profile := profile) (owner := owner)
      (wellFormed := wellFormed) (sameLayouts := sameLayouts) (owners := owners) (complete := complete)
      (globals := globals) (slots := slots) (prefixZero := prefixZero) (noIndirect := noIndirectOn)
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

include functions members profile chosen domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero noIndirect
  extension faithful observationsGeneric functionTypesGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric in
/-- The same chosen Support supplies nested flow through the original prepared core. -/
theorem preserves_flow (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i)) :
    RecursiveNamedHeaderContracts.AtMost budget
      (NestedFlowPreserves (functions := functions) receipt environment owner (headers := headers) (registry := registry) (faults := faults)) := by
  exact preserves_flow_on
    (functions := functions) (members := members)
    (root := root) (expressionSyntax := expressionSyntax) (receipt := receipt) (chosen := chosen) (environment := environment) (profile := profile) (owner := owner) (domains := domains) (wellFormed := wellFormed) (sameLayouts := sameLayouts) (owners := owners) (idsUnique := idsUnique) (complete := complete) (globals := globals) (slots := slots) (prefixZero := prefixZero) (noIndirectOn := fun _allowed found => noIndirect found) (extension := extension) (faithful := faithful) (uninitialized := uninitialized) (missing := missing) (rebuilt := rebuilt) (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded) (observationsGeneric := observationsGeneric) (functionTypesGeneric := functionTypesGeneric) (interpretsGeneric := interpretsGeneric)
    outer budget within ih
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

include functions members profile chosen domains wellFormed sameLayouts complete globals slots prefixZero
  extension faithful observationsGeneric functionTypesGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric in
/-- The same chosen Support supplies nested flow through the original prepared core. -/
theorem reflects_flow_on
    (noIndirectOn : CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirectOn
      (source caller.named) (expressionSyntax (source caller.named))) (outer budget : Nat) (within : budget ≤ outer)
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
    exact CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.ForModel.reflects_support_on
      (functions := functions) (members := members)
      (root := root) (expressionSyntax := expressionSyntax) (profile := profile) (owner := owner)
      (wellFormed := wellFormed) (sameLayouts := sameLayouts) (complete := complete)
      (globals := globals) (slots := slots) (prefixZero := prefixZero) (noIndirect := noIndirectOn)
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

include functions members profile chosen domains wellFormed sameLayouts complete globals slots prefixZero noIndirect
  extension faithful observationsGeneric functionTypesGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric in
/-- The same chosen Support supplies nested flow through the original prepared core. -/
theorem reflects_flow (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i)) :
    Below budget
      (NestedFlowReflects (functions := functions) receipt environment owner (headers := headers) (registry := registry) (faults := faults)) := by
  exact reflects_flow_on
    (functions := functions) (members := members)
    (root := root) (expressionSyntax := expressionSyntax) (receipt := receipt) (chosen := chosen) (environment := environment) (profile := profile) (owner := owner) (domains := domains) (wellFormed := wellFormed) (sameLayouts := sameLayouts) (complete := complete) (globals := globals) (slots := slots) (prefixZero := prefixZero) (noIndirectOn := fun _allowed found => noIndirect found) (extension := extension) (faithful := faithful) (uninitialized := uninitialized) (missing := missing) (rebuilt := rebuilt) (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded) (observationsGeneric := observationsGeneric) (functionTypesGeneric := functionTypesGeneric) (interpretsGeneric := interpretsGeneric)
    outer budget within ih
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

include functions members profile chosen domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero
  extension faithful observationsGeneric functionTypesGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  origin observed beforeTyped argumentsTyped stable in
/-- Typed finish returns the same actual nested pool with its Packet and readiness. -/
theorem source_at_entry_on
    (noIndirectOn : CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirectOn
      (source caller.named) (expressionSyntax (source caller.named))) (outer budget size : Nat) (strict : size < budget) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i))
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt environment captured prefixContext) (receipt.formation.code environment) history (receipt.formation.support environment).body.toBody.toContext functions registry arguments nativeArguments before store owner.key.frameLocation
      (first.rows owner.position).authority.current (first.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = (receipt.formation.code environment).receipt.loweredParameters.length)
    (copied : Environment) (spine : entry.entry.canonical = added ++ copied)
    (kept : ∀ slot, formationScope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
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
    beforeTyped argumentsTyped stable entry added length copied spine kept reached
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
      (preserves_flow_on (functions := functions) (members := members) (root := root) (expressionSyntax := expressionSyntax) (receipt := receipt) (chosen := chosen) (environment := environment) (profile := profile) (owner := owner) (domains := domains) (wellFormed := wellFormed) (sameLayouts := sameLayouts) (owners := owners) (idsUnique := idsUnique) (complete := complete) (globals := globals) (slots := slots) (prefixZero := prefixZero) (noIndirectOn := noIndirectOn) (extension := extension) (faithful := faithful) (uninitialized := uninitialized) (missing := missing) (rebuilt := rebuilt) (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded) (observationsGeneric := observationsGeneric) (functionTypesGeneric := functionTypesGeneric) (interpretsGeneric := interpretsGeneric) outer size (Nat.le_trans (Nat.le_of_lt strict) within) ih size (Nat.le_refl size)) ⟨(receipt.formation.support environment).body.valid, source.runtime⟩
      (body_facts receipt environment source)
      entry.entry.environments entry.entry.heaps entry.entry.locals entry.entry.lookups entry.entry.actualTyped
      entry.entry.reference entry.entry.read entry.entry.unmapped nested gate admitted source wellFormed trace
  exact ⟨packet, value, finalStore, finalMap, finalWorld, evaluated, represented, heaps,
    maps, worlds, frame, metadata, exit, post⟩

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
    (copied : Environment) (spine : entry.entry.canonical = added ++ copied)
    (kept : ∀ slot, formationScope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
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
  exact source_at_entry_on
    (functions := functions) (members := members)
    (root := root) (expressionSyntax := expressionSyntax) (receipt := receipt) (chosen := chosen) (environment := environment) (profile := profile) (owner := owner) (domains := domains) (wellFormed := wellFormed) (sameLayouts := sameLayouts) (owners := owners) (idsUnique := idsUnique) (complete := complete) (globals := globals) (slots := slots) (prefixZero := prefixZero) (noIndirectOn := fun _allowed found => noIndirect found) (extension := extension) (faithful := faithful) (uninitialized := uninitialized) (missing := missing) (rebuilt := rebuilt) (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded) (observationsGeneric := observationsGeneric) (functionTypesGeneric := functionTypesGeneric) (interpretsGeneric := interpretsGeneric) (captured := captured) (prefixContext := prefixContext) (history := history) (origin := origin) (observed := observed) (first := first) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped) (stable := stable)
    outer budget size strict within ih entry added length copied spine kept reached trace
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
    (copied : Environment) (spine : entry.entry.canonical = added ++ copied)
    (kept : ∀ slot, formationScope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
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
    outer budget size strict within ih entry added length copied spine kept reached trace

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

include functions members profile chosen domains wellFormed sameLayouts complete globals slots prefixZero
  extension faithful observationsGeneric functionTypesGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  origin observed beforeTyped argumentsTyped stable in
/-- Typed finish returns the same actual nested pool with its Packet and readiness. -/
theorem native_at_entry_on
    (noIndirectOn : CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirectOn
      (source caller.named) (expressionSyntax (source caller.named))) (outer budget size : Nat) (strict : size < budget) (within : budget ≤ outer)
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
      (reflects_flow_on (functions := functions) (members := members) (root := root) (expressionSyntax := expressionSyntax) (receipt := receipt) (chosen := chosen) (environment := environment) (profile := profile) (owner := owner) (domains := domains) (wellFormed := wellFormed) (sameLayouts := sameLayouts) (complete := complete) (globals := globals) (slots := slots) (prefixZero := prefixZero) (noIndirectOn := noIndirectOn) (extension := extension) (faithful := faithful) (uninitialized := uninitialized) (missing := missing) (rebuilt := rebuilt) (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded) (observationsGeneric := observationsGeneric) (functionTypesGeneric := functionTypesGeneric) (interpretsGeneric := interpretsGeneric) outer budget within ih) ⟨(receipt.formation.support environment).body.valid, source.runtime⟩
      (body_facts receipt environment source)
      entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped
      entry.reference entry.read entry.unmapped nested gate admitted source wellFormed completed
  exact ⟨packet, sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps,
    maps, worlds, frame, metadata, exit, post⟩

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
  exact native_at_entry_on
    (functions := functions) (members := members)
    (root := root) (expressionSyntax := expressionSyntax) (receipt := receipt) (chosen := chosen) (environment := environment) (profile := profile) (owner := owner) (domains := domains) (wellFormed := wellFormed) (sameLayouts := sameLayouts) (complete := complete) (globals := globals) (slots := slots) (prefixZero := prefixZero) (noIndirectOn := fun _allowed found => noIndirect found) (extension := extension) (faithful := faithful) (uninitialized := uninitialized) (missing := missing) (rebuilt := rebuilt) (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded) (observationsGeneric := observationsGeneric) (functionTypesGeneric := functionTypesGeneric) (interpretsGeneric := interpretsGeneric) (captured := captured) (prefixContext := prefixContext) (history := history) (origin := origin) (observed := observed) (first := first) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped) (stable := stable)
    outer budget size strict within ih entry reached completed
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

include functions members profile chosen domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero
  extension faithful observationsGeneric functionTypesGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  origin observed beforeTyped argumentsTyped stable in
/-- The base continuation projects the same returned nested State and full pool. -/
theorem source_continuation_on
    (noIndirectOn : CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirectOn
      (source caller.named) (expressionSyntax (source caller.named))) (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i)) :
    CallableIndexedOwnedLambdaEntryBodyContracts.SourceContinuation
      (registry := registry) (faults := faults) (arguments := arguments) (nativeArguments := nativeArguments) (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt environment captured prefixContext) (receipt.formation.code environment) history (receipt.formation.support environment).body.toBody.toContext functions owner first budget := by
  intro entry added length copied spine kept reached size strict outcome after trace
  obtain ⟨packet, value, finalStore, finalMap, finalWorld, evaluated, represented, heaps,
      maps, worlds, frame, metadata, exit, post⟩ :=
    source_at_entry_on (functions := functions) (members := members) (root := root) (expressionSyntax := expressionSyntax) (receipt := receipt) (chosen := chosen)
      (environment := environment) (profile := profile) (owner := owner) (domains := domains)
      (wellFormed := wellFormed) (sameLayouts := sameLayouts) (owners := owners) (idsUnique := idsUnique) (complete := complete)
      (globals := globals) (slots := slots) (prefixZero := prefixZero) (noIndirectOn := noIndirectOn)
      (extension := extension) (faithful := faithful) (observationsGeneric := observationsGeneric) (functionTypesGeneric := functionTypesGeneric)
      (uninitialized := uninitialized) (missing := missing) (rebuilt := rebuilt) (operandIncluded := operandIncluded)
      (unaryIncluded := unaryIncluded) (interpretsGeneric := interpretsGeneric) (captured := captured) (prefixContext := prefixContext)
      (history := history) (origin := origin) (observed := observed) (first := first)
      (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped) (stable := stable)
      outer budget size strict within ih entry added length copied spine kept reached trace
  obtain ⟨returned, related⟩ := post.forget
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps,
    maps, worlds, frame, metadata, exit, returned.val, (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller).related related⟩

include functions members profile chosen domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero noIndirect
  extension faithful observationsGeneric functionTypesGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  origin observed beforeTyped argumentsTyped stable in
/-- The base continuation projects the same returned nested State and full pool. -/
theorem source_continuation (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i)) :
    CallableIndexedOwnedLambdaEntryBodyContracts.SourceContinuation
      (registry := registry) (faults := faults) (arguments := arguments) (nativeArguments := nativeArguments) (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt environment captured prefixContext) (receipt.formation.code environment) history (receipt.formation.support environment).body.toBody.toContext functions owner first budget := by
  exact source_continuation_on
    (functions := functions) (members := members)
    (root := root) (expressionSyntax := expressionSyntax) (receipt := receipt) (chosen := chosen) (environment := environment) (profile := profile) (owner := owner) (domains := domains) (wellFormed := wellFormed) (sameLayouts := sameLayouts) (owners := owners) (idsUnique := idsUnique) (complete := complete) (globals := globals) (slots := slots) (prefixZero := prefixZero) (noIndirectOn := fun _allowed found => noIndirect found) (extension := extension) (faithful := faithful) (uninitialized := uninitialized) (missing := missing) (rebuilt := rebuilt) (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded) (observationsGeneric := observationsGeneric) (functionTypesGeneric := functionTypesGeneric) (interpretsGeneric := interpretsGeneric) (captured := captured) (prefixContext := prefixContext) (history := history) (origin := origin) (observed := observed) (first := first) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped) (stable := stable)
    outer budget within ih
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

include functions members profile chosen domains wellFormed sameLayouts complete globals slots prefixZero
  extension faithful observationsGeneric functionTypesGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  origin observed beforeTyped argumentsTyped stable in
/-- The base continuation projects the same returned nested State and full pool. -/
theorem native_continuation_on
    (noIndirectOn : CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirectOn
      (source caller.named) (expressionSyntax (source caller.named))) (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i)) :
    CallableIndexedOwnedLambdaEntryBodyContracts.NativeContinuation
      (registry := registry) (faults := faults) (arguments := arguments) (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt environment captured prefixContext) (receipt.formation.code environment) history (receipt.formation.support environment).body.toBody.toContext functions owner first budget := by
  intro entry reached size strict value finalStore completed
  obtain ⟨packet, sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps,
      maps, worlds, frame, metadata, exit, post⟩ :=
    native_at_entry_on (functions := functions) (members := members) (root := root) (expressionSyntax := expressionSyntax) (receipt := receipt) (chosen := chosen)
      (environment := environment) (profile := profile) (owner := owner) (domains := domains)
      (wellFormed := wellFormed) (sameLayouts := sameLayouts) (complete := complete)
      (globals := globals) (slots := slots) (prefixZero := prefixZero) (noIndirectOn := noIndirectOn)
      (extension := extension) (faithful := faithful) (observationsGeneric := observationsGeneric) (functionTypesGeneric := functionTypesGeneric)
      (uninitialized := uninitialized) (missing := missing) (rebuilt := rebuilt) (operandIncluded := operandIncluded)
      (unaryIncluded := unaryIncluded) (interpretsGeneric := interpretsGeneric) (captured := captured) (prefixContext := prefixContext)
      (history := history) (origin := origin) (observed := observed) (first := first)
      (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped) (stable := stable)
      outer budget size strict within ih entry reached completed
  obtain ⟨returned, related⟩ := post.forget
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps,
    maps, worlds, frame, metadata, exit, returned.val, (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller).related related⟩

include functions members profile chosen domains wellFormed sameLayouts complete globals slots prefixZero noIndirect
  extension faithful observationsGeneric functionTypesGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  origin observed beforeTyped argumentsTyped stable in
/-- The base continuation projects the same returned nested State and full pool. -/
theorem native_continuation (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ i, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner i)) :
    CallableIndexedOwnedLambdaEntryBodyContracts.NativeContinuation
      (registry := registry) (faults := faults) (arguments := arguments) (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt environment captured prefixContext) (receipt.formation.code environment) history (receipt.formation.support environment).body.toBody.toContext functions owner first budget := by
  exact native_continuation_on
    (functions := functions) (members := members)
    (root := root) (expressionSyntax := expressionSyntax) (receipt := receipt) (chosen := chosen) (environment := environment) (profile := profile) (owner := owner) (domains := domains) (wellFormed := wellFormed) (sameLayouts := sameLayouts) (complete := complete) (globals := globals) (slots := slots) (prefixZero := prefixZero) (noIndirectOn := fun _allowed found => noIndirect found) (extension := extension) (faithful := faithful) (uninitialized := uninitialized) (missing := missing) (rebuilt := rebuilt) (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded) (observationsGeneric := observationsGeneric) (functionTypesGeneric := functionTypesGeneric) (interpretsGeneric := interpretsGeneric) (captured := captured) (prefixContext := prefixContext) (history := history) (origin := origin) (observed := observed) (first := first) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped) (stable := stable)
    outer budget within ih
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaInvocation
/-! A positive chosen member supplies its literal factory and body. The nested
continuation is derived internally, then the original invocation restores the
actual caller pool once. Current arguments and static domains stay authentic. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaInvocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedMixedBodyCompilerFactory
open CallableIndexedOwnedPreparedMixedBodySiteInputs
open CallableIndexedOwnedChosenOrdinaryFormedMembers (FactoryMember)
open CallableIndexedOwnedChosenOrdinaryStoredMembers (ChosenAt)
open RecursiveNamedCatalogInvocationBounds (Below)
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

variable {i : OrdinaryIndex compiled} {history : History i.code}

/-- These fields are the same actual positive constructor, indexed by its owner. -/
structure ChosenFor (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (i : OrdinaryIndex compiled) (history : History i.code) : Prop where
  factory : FactoryMember root expressionSyntax i
  origin : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.SourceOrigin i.support history
  prefixContext : i.captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) i.support.caller
  globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 i.scope i.captured.canonical owner.key.frameLocation
  referenceIndex : i.code.referenceIndex = i.scope.length + 1 + compiled.indexed.base.globals.length
  typed : RuntimeValueHasType i.world (value i.code i.captured.embedding history.native i.capturedActual)
    (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore)
    compiled.indexed.layouts.definitions

/-- Only the genuine positive constructor exposes its own actual owner. -/
theorem chosen_for (member : ChosenAt root expressionSyntax headers keys registry faults i history) :
    ∃ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys, ChosenFor (headers := headers) root expressionSyntax owner i history := by
  cases member with
  | ordinary owner factory origin prefixContext globals referenceIndex typed =>
    exact ⟨owner, factory, origin, prefixContext, globals, referenceIndex, typed⟩

/-- The complete actual ledger accompanies independent Source runtime validity. -/
def Validity (i : OrdinaryIndex compiled) (context : SourceSemantics.Context) : Prop :=
  CompatibleRuntimeContextValidity.Valid i.code.compilation.solvedRequirements context i.function.evidence ∧
    Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context i.function.source

variable
  (i : OrdinaryIndex compiled) (history : History i.code)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (member : ChosenFor (headers := headers) root expressionSyntax owner i history)

variable
  (domains : ∀ context, Validity i context → ∀ childScope,
    DomainAt root expressionSyntax ((i.support).body).readFuel context i.function.evidence childScope headers)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : ∀ context, Validity i context → RequirementIdsUnique context)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)
  (noIndirect : CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirect (source caller.named))
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) identities)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (rootReasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((rootReasonAt id).add tag))
  {table : SourceCoreFaultSites.Table}
  (rebuilt : (i.support).issued.diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep (i.support).issued.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep (i.support).issued.assignments reason token → faults reason token)
  (interprets : ∀ context, Validity i context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := (i.support).certificates ((i.support).body).readFuel (i.function).source)
      (administrative := i.captured.administrative)
      (factory := CallableIndexedOwnedContextualLambdaJointStaticReceipts.trackedFactory (i.support).diagnosticPolicy (i.function).source (i.support).issued.invalidOperand)
      (faults := faults) (registry := registry) (i.support).issued (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) table)


variable {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (first : State headers keys ⟨callerScope, i.mapping, i.world, before, store, canonical⟩)
  (beforeTyped : Dynamic.HeapWellTyped i.function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes i.function.context before arguments i.support.body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows first)

/-- The actual stored reference follows from this same owner's positive globals. -/
theorem ChosenFor.reference (member : ChosenFor (headers := headers) root expressionSyntax owner i history) :
    i.captured.canonical[i.code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
  rw [member.referenceIndex]
  exact member.globals.reference

namespace ForModel

variable
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (members : CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.Members
    (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    caller root expressionSyntax functions)
  (functionTypes : FunctionRuntimeViews functions)
  (observationsGeneric : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (interpretsGeneric : ∀ context, Validity i context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := (i.support).certificates ((i.support).body).readFuel (i.function).source)
      (administrative := i.captured.administrative)
      (factory := CallableIndexedOwnedContextualLambdaJointStaticReceipts.trackedFactory (i.support).diagnosticPolicy (i.function).source (i.support).issued.invalidOperand)
      (faults := faults) (registry := registry) (i.support).issued (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) functions table)

include functions members functionTypes profile member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero
  extension faithful observationsGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  beforeTyped argumentsTyped stable in
/-- The same positive factory internally supplies the genuine nested Source continuation. -/
theorem source_continuation_on
    (noIndirectOn : CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirectOn
      (source caller.named) (expressionSyntax (source caller.named))) (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      functions owner index)) :
    CallableIndexedOwnedLambdaEntryBodyContracts.SourceContinuation
      (registry := registry) (faults := faults) (arguments := arguments) (nativeArguments := nativeArguments)
      i.captured i.code history i.support.body.toBody.toContext
      functions owner first budget := by
  obtain ⟨factory, origin, _prefixContext, observed, _referenceIndex, _typed⟩ := member
  cases factory with
  | formed receipt chosen environment captured prefixContext =>
    exact CallableIndexedOwnedChosenNestedLambdaBodyContinuations.ForModel.source_continuation_on
      (functions := functions) (members := members)
      (root := root) (expressionSyntax := expressionSyntax) (receipt := receipt) (chosen := chosen)
      (environment := environment) (profile := profile) (owner := owner) (domains := domains)
      (wellFormed := wellFormed) (sameLayouts := sameLayouts) (owners := owners) (idsUnique := idsUnique)
      (complete := complete) (globals := globals) (slots := slots) (prefixZero := prefixZero)
      (noIndirectOn := noIndirectOn) (extension := extension) (faithful := faithful)
      (observationsGeneric := observationsGeneric) (functionTypesGeneric := functionTypes)
      (uninitialized := uninitialized) (missing := missing) (rebuilt := rebuilt)
      (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded) (interpretsGeneric := interpretsGeneric)
      (captured := captured) (prefixContext := prefixContext) (history := history) (origin := origin)
      (observed := observed) (first := first) (beforeTyped := beforeTyped)
      (argumentsTyped := argumentsTyped) (stable := stable) outer budget within ih

include functions members functionTypes profile member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero noIndirect
  extension faithful observationsGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  beforeTyped argumentsTyped stable in
/-- The same positive factory internally supplies the genuine nested Source continuation. -/
theorem source_continuation (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      functions owner index)) :
    CallableIndexedOwnedLambdaEntryBodyContracts.SourceContinuation
      (registry := registry) (faults := faults) (arguments := arguments) (nativeArguments := nativeArguments)
      i.captured i.code history i.support.body.toBody.toContext
      functions owner first budget := by
  exact source_continuation_on
    (noIndirectOn := fun _allowed found => noIndirect found)
    (functions := functions)
    (members := members)
    (functionTypes := functionTypes)
    (observationsGeneric := observationsGeneric) (interpretsGeneric := interpretsGeneric)
    root expressionSyntax i history profile owner member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero extension faithful uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable outer budget within ih

include functions members functionTypes profile member domains wellFormed sameLayouts complete globals slots prefixZero
  extension faithful observationsGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  beforeTyped argumentsTyped stable in
/-- Reflection keeps the independent Source grade of the same literal nested continuation. -/
theorem native_continuation_on
    (noIndirectOn : CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirectOn
      (source caller.named) (expressionSyntax (source caller.named))) (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      functions owner index)) :
    CallableIndexedOwnedLambdaEntryBodyContracts.NativeContinuation
      (registry := registry) (faults := faults) (arguments := arguments)
      i.captured i.code history i.support.body.toBody.toContext
      functions owner first budget := by
  obtain ⟨factory, origin, _prefixContext, observed, _referenceIndex, _typed⟩ := member
  cases factory with
  | formed receipt chosen environment captured prefixContext =>
    exact CallableIndexedOwnedChosenNestedLambdaBodyContinuations.ForModel.native_continuation_on
      (functions := functions) (members := members)
      (root := root) (expressionSyntax := expressionSyntax) (receipt := receipt) (chosen := chosen)
      (environment := environment) (profile := profile) (owner := owner) (domains := domains)
      (wellFormed := wellFormed) (sameLayouts := sameLayouts)
      (complete := complete) (globals := globals) (slots := slots) (prefixZero := prefixZero)
      (noIndirectOn := noIndirectOn) (extension := extension) (faithful := faithful)
      (observationsGeneric := observationsGeneric) (functionTypesGeneric := functionTypes)
      (uninitialized := uninitialized) (missing := missing) (rebuilt := rebuilt)
      (operandIncluded := operandIncluded) (unaryIncluded := unaryIncluded) (interpretsGeneric := interpretsGeneric)
      (captured := captured) (prefixContext := prefixContext) (history := history) (origin := origin)
      (observed := observed) (first := first) (beforeTyped := beforeTyped)
      (argumentsTyped := argumentsTyped) (stable := stable) outer budget within ih

include functions members functionTypes profile member domains wellFormed sameLayouts complete globals slots prefixZero noIndirect
  extension faithful observationsGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  beforeTyped argumentsTyped stable in
/-- Reflection keeps the independent Source grade of the same literal nested continuation. -/
theorem native_continuation (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      functions owner index)) :
    CallableIndexedOwnedLambdaEntryBodyContracts.NativeContinuation
      (registry := registry) (faults := faults) (arguments := arguments)
      i.captured i.code history i.support.body.toBody.toContext
      functions owner first budget := by
  exact native_continuation_on
    (noIndirectOn := fun _allowed found => noIndirect found)
    (functions := functions)
    (members := members)
    (functionTypes := functionTypes)
    (observationsGeneric := observationsGeneric) (interpretsGeneric := interpretsGeneric)
    root expressionSyntax i history profile owner member domains wellFormed sameLayouts complete globals slots prefixZero extension faithful uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable outer budget within ih

/-- The represented result and exact restored caller pool are the original tuple. -/
def InvocationResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.ResultAt
    (registry := registry) (faults := faults) i.captured i.code
    functions first
    outcome after value finalStore finalMap finalWorld

variable
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      functions)
    i.mapping i.world i.code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functions
    i.mapping i.world before store)
  (locals : Dynamic.EnvironmentAgrees before i.function.context.locals i.function.captured)

include functions members functionTypes profile member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero
  extension faithful observationsGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  beforeTyped argumentsTyped stable represented heaps locals in
/-- One internally built continuation feeds the original invocation and restoration once. -/
theorem invocation_preserves_on
    (noIndirectOn : CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirectOn
      (source caller.named) (expressionSyntax (source caller.named))) (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      functions owner index))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence i.function.evidence before (.closure i.function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: i.capturedActual)
        store (i.code.body.rename i.captured.embedding.lift.lift) value finalStore ∧
      InvocationResultAt (registry := registry) (faults := faults) (functions := functions) i first outcome after value finalStore finalMap finalWorld := by
  have continuation := source_continuation_on (noIndirectOn := noIndirectOn) (nativeArguments := nativeArguments) (functions := functions) (members := members) (functionTypes := functionTypes) (observationsGeneric := observationsGeneric) (interpretsGeneric := interpretsGeneric) root expressionSyntax i history profile owner member
    domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero extension faithful
    uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable
    outer budget withinOuter ih
  obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
  exact CallableIndexedOwnedLambdaInvocationBounds.invocation_preserves_bounded_at_with_continuation
    i.captured i.code history i.support.body.toBody.toContext
    functions represented owner first heaps locals
    (member.reference root expressionSyntax) currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed i.code history)
    budget continuation trace within

include functions members functionTypes profile member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero noIndirect
  extension faithful observationsGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  beforeTyped argumentsTyped stable represented heaps locals in
/-- One internally built continuation feeds the original invocation and restoration once. -/
theorem invocation_preserves (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      functions owner index))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence i.function.evidence before (.closure i.function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: i.capturedActual)
        store (i.code.body.rename i.captured.embedding.lift.lift) value finalStore ∧
      InvocationResultAt (registry := registry) (faults := faults) (functions := functions) i first outcome after value finalStore finalMap finalWorld := by
  exact invocation_preserves_on
    (noIndirectOn := fun _allowed found => noIndirect found)
    (functions := functions)
    (members := members)
    (functionTypes := functionTypes)
    (observationsGeneric := observationsGeneric) (interpretsGeneric := interpretsGeneric)
    root expressionSyntax i history profile owner member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero extension faithful uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable represented heaps locals outer budget withinOuter ih trace within

include functions members functionTypes profile member domains wellFormed sameLayouts complete globals slots prefixZero
  extension faithful observationsGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  beforeTyped argumentsTyped stable represented heaps locals in
/-- Native completion invokes the same continuation and restores the actual caller pool once. -/
theorem invocation_reflects_on
    (noIndirectOn : CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirectOn
      (source caller.named) (expressionSyntax (source caller.named))) (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      functions owner index))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: i.capturedActual)
      store (i.code.body.rename i.captured.embedding.lift.lift) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        callContext callerEvidence i.function.evidence before (.closure i.function) arguments outcome after ∧
      InvocationResultAt (registry := registry) (faults := faults) (functions := functions) i first outcome after value finalStore finalMap finalWorld := by
  have continuation := native_continuation_on (noIndirectOn := noIndirectOn) (arguments := arguments) (functions := functions) (members := members) (functionTypes := functionTypes) (observationsGeneric := observationsGeneric) (interpretsGeneric := interpretsGeneric) root expressionSyntax i history profile owner member
    domains wellFormed sameLayouts complete globals slots prefixZero extension faithful
    uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable
    outer budget withinOuter ih
  obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
  exact CallableIndexedOwnedLambdaInvocationBounds.invocation_reflects_bounded_at_with_continuation
    i.captured i.code history i.support.body.toBody.toContext
    functions represented owner first heaps locals
    (member.reference root expressionSyntax) currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed i.code history)
    i.support.body.frame budget continuation completed within

include functions members functionTypes profile member domains wellFormed sameLayouts complete globals slots prefixZero noIndirect
  extension faithful observationsGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  beforeTyped argumentsTyped stable represented heaps locals in
/-- Native completion invokes the same continuation and restores the actual caller pool once. -/
theorem invocation_reflects (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      functions owner index))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: i.capturedActual)
      store (i.code.body.rename i.captured.embedding.lift.lift) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        callContext callerEvidence i.function.evidence before (.closure i.function) arguments outcome after ∧
      InvocationResultAt (registry := registry) (faults := faults) (functions := functions) i first outcome after value finalStore finalMap finalWorld := by
  exact invocation_reflects_on
    (noIndirectOn := fun _allowed found => noIndirect found)
    (functions := functions)
    (members := members)
    (functionTypes := functionTypes)
    (observationsGeneric := observationsGeneric) (interpretsGeneric := interpretsGeneric)
    root expressionSyntax i history profile owner member domains wellFormed sameLayouts complete globals slots prefixZero extension faithful uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable represented heaps locals outer budget withinOuter ih completed within

include functions members functionTypes profile member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero
  extension faithful observationsGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  beforeTyped argumentsTyped stable represented heaps locals in
/-- The genuine payload application edge retains that same invocation tuple. -/
theorem application_preserves_on
    (noIndirectOn : CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirectOn
      (source caller.named) (expressionSyntax (source caller.named))) (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      functions owner index))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence i.function.evidence before (.closure i.function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [CallableIndexedLambdaValues.value i.code i.captured.embedding history.native i.capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      InvocationResultAt (registry := registry) (faults := faults) (functions := functions) i first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result⟩ :=
    invocation_preserves_on (noIndirectOn := noIndirectOn) (functions := functions) (members := members) (functionTypes := functionTypes) (observationsGeneric := observationsGeneric) (interpretsGeneric := interpretsGeneric) root expressionSyntax i history profile owner member domains wellFormed sameLayouts owners idsUnique
      complete globals slots prefixZero extension faithful uninitialized missing rebuilt
      operandIncluded unaryIncluded first beforeTyped argumentsTyped stable represented heaps locals
      outer budget withinOuter ih trace within
  exact ⟨value, finalStore, finalMap, finalWorld,
    .apply (.second (.first (.var rfl))) (.var rfl) evaluated, result⟩

include functions members functionTypes profile member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero noIndirect
  extension faithful observationsGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  beforeTyped argumentsTyped stable represented heaps locals in
/-- The genuine payload application edge retains that same invocation tuple. -/
theorem application_preserves (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      functions owner index))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence i.function.evidence before (.closure i.function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [CallableIndexedLambdaValues.value i.code i.captured.embedding history.native i.capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      InvocationResultAt (registry := registry) (faults := faults) (functions := functions) i first outcome after value finalStore finalMap finalWorld := by
  exact application_preserves_on
    (noIndirectOn := fun _allowed found => noIndirect found)
    (functions := functions)
    (members := members)
    (functionTypes := functionTypes)
    (observationsGeneric := observationsGeneric) (interpretsGeneric := interpretsGeneric)
    root expressionSyntax i history profile owner member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero extension faithful uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable represented heaps locals outer budget withinOuter ih trace within

include functions members functionTypes profile member domains wellFormed sameLayouts complete globals slots prefixZero
  extension faithful observationsGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  beforeTyped argumentsTyped stable represented heaps locals in
/-- The real application child keeps its strict native bound and independent Source grade. -/
theorem application_reflects_on
    (noIndirectOn : CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirectOn
      (source caller.named) (expressionSyntax (source caller.named))) (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      functions owner index))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value i.code i.captured.embedding history.native i.capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        callContext callerEvidence i.function.evidence before (.closure i.function) arguments outcome after ∧
      InvocationResultAt (registry := registry) (faults := faults) (functions := functions) i first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨bodySize, smaller, applied⟩ := completed.apply_body (.second (.first (.var rfl))) (.var rfl)
  exact invocation_reflects_on (noIndirectOn := noIndirectOn) (functions := functions) (members := members) (functionTypes := functionTypes) (observationsGeneric := observationsGeneric) (interpretsGeneric := interpretsGeneric) root expressionSyntax i history profile owner member domains wellFormed sameLayouts
    complete globals slots prefixZero extension faithful uninitialized missing rebuilt
    operandIncluded unaryIncluded first beforeTyped argumentsTyped stable represented heaps locals
    outer budget withinOuter ih applied (Nat.le_trans (Nat.le_of_lt smaller) within)

include functions members functionTypes profile member domains wellFormed sameLayouts complete globals slots prefixZero noIndirect
  extension faithful observationsGeneric uninitialized missing rebuilt operandIncluded unaryIncluded interpretsGeneric
  beforeTyped argumentsTyped stable represented heaps locals in
/-- The real application child keeps its strict native bound and independent Source grade. -/
theorem application_reflects (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      functions owner index))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value i.code i.captured.embedding history.native i.capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        callContext callerEvidence i.function.evidence before (.closure i.function) arguments outcome after ∧
      InvocationResultAt (registry := registry) (faults := faults) (functions := functions) i first outcome after value finalStore finalMap finalWorld := by
  exact application_reflects_on
    (noIndirectOn := fun _allowed found => noIndirect found)
    (functions := functions)
    (members := members)
    (functionTypes := functionTypes)
    (observationsGeneric := observationsGeneric) (interpretsGeneric := interpretsGeneric)
    root expressionSyntax i history profile owner member domains wellFormed sameLayouts complete globals slots prefixZero extension faithful uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable represented heaps locals outer budget withinOuter ih completed within
end ForModel

include member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero noIndirect
  extension faithful observations uninitialized missing rebuilt operandIncluded unaryIncluded interprets
  beforeTyped argumentsTyped stable in
/-- The same positive factory internally supplies the genuine nested Source continuation. -/
theorem source_continuation_chosen (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner index)) :
    CallableIndexedOwnedLambdaEntryBodyContracts.SourceContinuation
      (registry := registry) (faults := faults) (arguments := arguments) (nativeArguments := nativeArguments)
      i.captured i.code history i.support.body.toBody.toContext
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner first budget :=
  ForModel.source_continuation
    (functions := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    (members := fun _i _history member => member.formed.represents)
    (functionTypes := CallableIndexedOwnedPreparedOrdinaryLambdaValues.runtime_views headers keys registry faults profile)
    (observationsGeneric := observations) (interpretsGeneric := interprets)
    root expressionSyntax i history profile owner member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero noIndirect extension faithful uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable outer budget within ih

include member domains wellFormed sameLayouts complete globals slots prefixZero noIndirect
  extension faithful observations uninitialized missing rebuilt operandIncluded unaryIncluded interprets
  beforeTyped argumentsTyped stable in
/-- Reflection keeps the independent Source grade of the same literal nested continuation. -/
theorem native_continuation_chosen (outer budget : Nat) (within : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner index)) :
    CallableIndexedOwnedLambdaEntryBodyContracts.NativeContinuation
      (registry := registry) (faults := faults) (arguments := arguments)
      i.captured i.code history i.support.body.toBody.toContext
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner first budget :=
  ForModel.native_continuation
    (functions := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    (members := fun _i _history member => member.formed.represents)
    (functionTypes := CallableIndexedOwnedPreparedOrdinaryLambdaValues.runtime_views headers keys registry faults profile)
    (observationsGeneric := observations) (interpretsGeneric := interprets)
    root expressionSyntax i history profile owner member domains wellFormed sameLayouts complete globals slots prefixZero noIndirect extension faithful uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable outer budget within ih

/-- The represented result and exact restored caller pool are the original tuple. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.ResultAt
    (registry := registry) (faults := faults) i.captured i.code
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) first
    outcome after value finalStore finalMap finalWorld

variable
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    i.mapping i.world i.code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
    i.mapping i.world before store)
  (locals : Dynamic.EnvironmentAgrees before i.function.context.locals i.function.captured)

include member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero noIndirect
  extension faithful observations uninitialized missing rebuilt operandIncluded unaryIncluded interprets
  beforeTyped argumentsTyped stable represented heaps locals in
/-- One internally built continuation feeds the original invocation and restoration once. -/
theorem invocation_preserves_chosen (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner index))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence i.function.evidence before (.closure i.function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: i.capturedActual)
        store (i.code.body.rename i.captured.embedding.lift.lift) value finalStore ∧
      ResultAt (registry := registry) (faults := faults) i profile first outcome after value finalStore finalMap finalWorld :=
  ForModel.invocation_preserves
    (functions := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    (members := fun _i _history member => member.formed.represents)
    (functionTypes := CallableIndexedOwnedPreparedOrdinaryLambdaValues.runtime_views headers keys registry faults profile)
    (observationsGeneric := observations) (interpretsGeneric := interprets)
    root expressionSyntax i history profile owner member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero noIndirect extension faithful uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable represented heaps locals outer budget withinOuter ih trace within

include member domains wellFormed sameLayouts complete globals slots prefixZero noIndirect
  extension faithful observations uninitialized missing rebuilt operandIncluded unaryIncluded interprets
  beforeTyped argumentsTyped stable represented heaps locals in
/-- Native completion invokes the same continuation and restores the actual caller pool once. -/
theorem invocation_reflects_chosen (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner index))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: i.capturedActual)
      store (i.code.body.rename i.captured.embedding.lift.lift) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        callContext callerEvidence i.function.evidence before (.closure i.function) arguments outcome after ∧
      ResultAt (registry := registry) (faults := faults) i profile first outcome after value finalStore finalMap finalWorld :=
  ForModel.invocation_reflects
    (functions := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    (members := fun _i _history member => member.formed.represents)
    (functionTypes := CallableIndexedOwnedPreparedOrdinaryLambdaValues.runtime_views headers keys registry faults profile)
    (observationsGeneric := observations) (interpretsGeneric := interprets)
    root expressionSyntax i history profile owner member domains wellFormed sameLayouts complete globals slots prefixZero noIndirect extension faithful uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable represented heaps locals outer budget withinOuter ih completed within

include member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero noIndirect
  extension faithful observations uninitialized missing rebuilt operandIncluded unaryIncluded interprets
  beforeTyped argumentsTyped stable represented heaps locals in
/-- The genuine payload application edge retains that same invocation tuple. -/
theorem application_preserves_chosen (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner index))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      callContext callerEvidence i.function.evidence before (.closure i.function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [CallableIndexedLambdaValues.value i.code i.captured.embedding history.native i.capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := registry) (faults := faults) i profile first outcome after value finalStore finalMap finalWorld :=
  ForModel.application_preserves
    (functions := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    (members := fun _i _history member => member.formed.represents)
    (functionTypes := CallableIndexedOwnedPreparedOrdinaryLambdaValues.runtime_views headers keys registry faults profile)
    (observationsGeneric := observations) (interpretsGeneric := interprets)
    root expressionSyntax i history profile owner member domains wellFormed sameLayouts owners idsUnique complete globals slots prefixZero noIndirect extension faithful uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable represented heaps locals outer budget withinOuter ih trace within

include member domains wellFormed sameLayouts complete globals slots prefixZero noIndirect
  extension faithful observations uninitialized missing rebuilt operandIncluded unaryIncluded interprets
  beforeTyped argumentsTyped stable represented heaps locals in
/-- The real application child keeps its strict native bound and independent Source grade. -/
theorem application_reflects_chosen (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults)
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) owner index))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value i.code i.captured.embedding history.native i.capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        callContext callerEvidence i.function.evidence before (.closure i.function) arguments outcome after ∧
      ResultAt (registry := registry) (faults := faults) i profile first outcome after value finalStore finalMap finalWorld :=
  ForModel.application_reflects
    (functions := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    (members := fun _i _history member => member.formed.represents)
    (functionTypes := CallableIndexedOwnedPreparedOrdinaryLambdaValues.runtime_views headers keys registry faults profile)
    (observationsGeneric := observations) (interpretsGeneric := interprets)
    root expressionSyntax i history profile owner member domains wellFormed sameLayouts complete globals slots prefixZero noIndirect extension faithful uninitialized missing rebuilt operandIncluded unaryIncluded first beforeTyped argumentsTyped stable represented heaps locals outer budget withinOuter ih completed within
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaInvocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaFormation
/-! The actual chosen compiler receipt supplies the local member constructor
at its literal recaptured index. Each endpoint invokes the committed formation
core once with one model for the input heap and returned relation. The
formation copies the captured cells, so the member sits at the formed
closure's index over the copies. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedMixedBodySiteInputs (ChosenFactory)
open CallableIndexedOwnedChosenOrdinaryFormedMembers (FactoryMember index)
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


variable {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt caller diagnostics namedCode compilation
    sourceContext evidence scope id lowered)
  (chosen : ChosenFactory root expressionSyntax receipt) (environment : Dynamic.Environment)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {actual canonical : Environment} {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope (receipt.formation.function environment).captured actual)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) caller)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)

include chosen observed in
/-- The known receipt and actual packet build this positive member directly at
the formed closure's literal recaptured index, over the copies. Typing is
supplied independently by the original formation core. -/
theorem chosen_at
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) projects
      compiled.indexed.layouts.definitions} {location : Location}
    (formed : Formed model (index receipt environment captured prefixContext).captured
      (index receipt environment captured prefixContext).code
      (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.history_at
        (index receipt environment captured prefixContext).captured
        (index receipt environment captured prefixContext).code
        (index receipt environment captured prefixContext).support owner initial packet) heap store location)
    (nativeTyped : RuntimeValueHasType formed.finalWorld
      (value (index receipt environment captured prefixContext).code formed.embedding
        (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.history_at
          (index receipt environment captured prefixContext).captured
          (index receipt environment captured prefixContext).code
          (index receipt environment captured prefixContext).support owner initial packet).native formed.closureActual)
      (CallableContract.functionType (index receipt environment captured prefixContext).code.receipt.parameterCore
        (index receipt environment captured prefixContext).code.receipt.resultCore) compiled.indexed.layouts.definitions) :
    ChosenAt root expressionSyntax headers keys registry faults (index receipt formed.captured formed.captures rfl)
      formed.closureHistory := by
  let i := index receipt environment captured prefixContext
  exact .ordinary owner (.formed receipt chosen formed.captured formed.captures rfl)
    ⟨(CallableIndexedOwnedPreparedOrdinaryLambdaFormation.source_origin i.captured i.code i.support owner initial packet).metadata⟩
    rfl (observed.of_slots formed.slots)
    (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.reference_index i.captured i.code i.support) nativeTyped

include chosen observed in
/-- One actual formation over the copies creates the new model member at the
formed closure's literal recaptured index. There is no whole-model inclusion
premise. -/
theorem formation
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
      mapping world heap store) :
    let i := index receipt environment captured prefixContext
    let history := CallableIndexedOwnedPreparedOrdinaryLambdaFormation.history_at i.captured i.code i.support owner initial packet
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile))
        i.captured i.code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) i.function.context i.function.evidence
        i.function.source i.function.captured heap i.code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (i.code.lowered.expression.rename i.captured.embedding)
        (.inRight .word (value i.code formed.embedding history.native formed.closureActual)) formed.finalStore ∧
      (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile).Represents
        registry formed.finalMap formed.finalWorld (FunctionValues.sourceType i.function) (.closure formed.closure)
        (value i.code formed.embedding history.native formed.closureActual)
        (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (i.code.lowered.expression.rename i.captured.embedding) result finalStore →
        result = .inRight .word (value i.code formed.embedding history.native formed.closureActual) ∧
          finalStore = formed.finalStore) := by
  let i := index receipt environment captured prefixContext
  exact CallableIndexedOwnedPreparedOrdinaryLambdaFormation.formation_with_member
    i.captured i.code i.support owner initial packet profile observed
    (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
    (fun formed nativeTyped => .chosen_ordinary (index receipt formed.captured formed.captures rfl) formed.closureHistory
      (chosen_at root expressionSyntax receipt chosen environment captured prefixContext owner initial packet observed
        formed nativeTyped))
    heaps (receipt.formation.snapshots environment) receipt.formation.ordinary receipt.formation.coercions

variable
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
    (receipt.formation.function environment).context (receipt.formation.function environment).source)
  (covers : (receipt.formation.function environment).evidence.Covers (receipt.formation.function environment).context)
  (locals : Dynamic.EnvironmentAgrees heap (receipt.formation.function environment).context.locals
    (receipt.formation.function environment).captured)
  (typed : ExpressionHasType (receipt.formation.function environment).source (receipt.formation.function environment).context
    (receipt.formation.code environment).id (receipt.formation.code environment).sourceNode.type)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
    mapping world heap store)
  (admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller)
    (receipt.formation.function environment).context ⟨initial, packet⟩)

include chosen observed wellFormed runtime covers locals typed heaps admitted in
/-- The Source endpoint supplies the actual member of the formed closure
internally and preserves all heap/effect/admission fields, in the formed state,
under this same function model. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      (receipt.formation.function environment).context (receipt.formation.function environment).evidence
      (receipt.formation.function environment).source (receipt.formation.function environment).captured
      heap (receipt.formation.code environment).id outcome after) :
    let i := index receipt environment captured prefixContext
    ∃ result finalStore, CallableIndexedOwnedPreparedOrdinaryLambdaFormation.ResultAt
      (registry := registry) (faults := faults) i.captured i.code i.support owner initial packet
      (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
      outcome after result finalStore := by
  let i := index receipt environment captured prefixContext
  exact CallableIndexedOwnedPreparedOrdinaryLambdaFormation.preserves_at_with_member
    i.captured i.code i.support owner initial packet profile observed
    (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
    wellFormed runtime covers locals typed receipt.formation.sourceType (receipt.formation.snapshots environment)
    receipt.formation.ordinary receipt.formation.coercions heaps admitted
    (fun formed nativeTyped => .chosen_ordinary (index receipt formed.captured formed.captures rfl) formed.closureHistory
      (chosen_at root expressionSyntax receipt chosen environment captured prefixContext owner initial packet observed
        formed nativeTyped)) trace

include chosen observed wellFormed runtime covers locals typed heaps admitted in
/-- Native reflection uses the same actual closure formation and current packet;
its Source execution size is independent of the native completion. -/
theorem reflects_at {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      ((receipt.formation.code environment).lowered.expression.rename captured.embedding) result finalStore) :
    let i := index receipt environment captured prefixContext
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        i.function.context i.function.evidence i.function.source i.function.captured heap i.code.id outcome after ∧
      CallableIndexedOwnedPreparedOrdinaryLambdaFormation.ResultAt
        (registry := registry) (faults := faults) i.captured i.code i.support owner initial packet
        (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
        outcome after result finalStore := by
  let i := index receipt environment captured prefixContext
  exact CallableIndexedOwnedPreparedOrdinaryLambdaFormation.reflects_at_with_member
    i.captured i.code i.support owner initial packet profile observed
    (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
    wellFormed runtime covers locals typed receipt.formation.sourceType (receipt.formation.snapshots environment)
    receipt.formation.ordinary receipt.formation.coercions heaps admitted
    (fun formed nativeTyped => .chosen_ordinary (index receipt formed.captured formed.captures rfl) formed.closureHistory
      (chosen_at root expressionSyntax receipt chosen environment captured prefixContext owner initial packet observed
        formed nativeTyped)) completed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaFormation
end
