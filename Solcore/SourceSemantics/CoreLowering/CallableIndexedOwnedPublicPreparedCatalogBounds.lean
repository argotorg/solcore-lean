import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedSourceSites
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedAssignmentReadiness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogProducers
import Solcore.SourceSemantics.CoreLowering.ProtectedImperativeMatchCoupledReadyBounds

/-! The actual public extraction supplies its own Tree, diagnostic plan and
match contexts. Genuine Source validity and strict expression children feed
the original prepared Catalog operations at the same reached states. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedCatalogBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory (NativeFrame)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open ProtectedStateTransition ProtectedStateImperativeCatalogReady
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedPublicPreparedSourceSites (Validity)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {protocol : Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (issued : CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds.PublicReceipt header)
  {compilation : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → SourceCoreFunctions.Context}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {administrative : Core.Context}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}









variable (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends ((SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (condition : Location → NativeFrame → Prop)
  (producer : MarkedAllocation.Producer protocol header.layouts compiled.indexed.ancestry.layout.frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
  (acquire : ∀ location native, condition location native → OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  (transport : AdministrativeTransport protocol) (bindings : Bindings protocol)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) header.context (header.function.source))
  {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)}
  (diagnosticsFound : compiled.indexed.base.diagnostics = some diagnostics)
  {table : SourceCoreFaultSites.Table} (rebuilt : diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep issued.original.prepared.compilation.own.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep issued.original.prepared.compilation.own.assignments reason token → faults reason token)

variable (receipt : CallableIndexedOwnedPublicCatalogPreparedReceipts.CatalogReceipt
  (headers := headers) (compilation := compilation) (expressionSyntax := expressionSyntax)
  (administrative := administrative) issued)







variable (interprets : ∀ context, Validity header context →
  CallableIndexedOwnedPublicPreparedAssignmentReadiness.ReachedInterpretations
    (context := context) (certificates := (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header)) (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
    (factory := (AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments)) (faults := faults) (registry := registry) header bridge issued functions table)

include extension faithful observations producer acquire transport bindings wellFormed sourceRuntime
  diagnosticsFound rebuilt operandIncluded unaryIncluded interprets in
theorem preserves_flow (budget : Nat)
    (_meaning : ∀ context, Validity header context → RecursiveNamedHeaderContracts.AtMost budget
      (fun size => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context (header.function.evidence) (header.function.source) ((CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header) context) faults size)) :
    ProtectedStateImperativeCatalogPayload.PreservesAtWithReceipt protocol (readiness bridge) condition
      (ProtectedStateImperativeTypedSourceSites.Facts (header.function.source) (expressionSyntax header))
      (CallableIndexedOwnedAdmittedForBounds.LoopFacts (header.function.source) (expressionSyntax header))
      (ProtectedStateImperativeInitializerSourceSites.Facts (header.function.source) (expressionSyntax header))
      functions (Program.ofChecked compiled.sourceProgram) (header.function.evidence) (Validity header) budget (ProtectedStateImperativeCatalogPayload.StructuralHeaderReceipt
  (layouts := header.layouts) (owner := header.owner) (active := header.active)
  (frame := compiled.indexed.ancestry.layout.frame) (globals := header.globals) (onError := header.onError)
  (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (source := (header.function.source)) (certificates := (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header))
  (definitions := compiled.indexed.layouts.definitions) (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) ((fun head => GenericForHeader.Structural.PreparedAssignment (AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments) (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection issued.original.prepared) (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault issued.original.prepared) head)) ((fun head => GenericForHeader.Structural.PreparedUnary true (header.function.source)
  (fun site root => issued.original.prepared.compilation.own.assignments.reasonAt site root SourceCoreAssignmentFaultSites.Kind.bitNot) head)))
      (frame := compiled.indexed.ancestry.layout.frame) (globals := header.globals)
      (source := (header.function.source)) (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) (registry := registry) (faults := faults)
      (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
      header.context (RecursiveNamedCatalogNativeContexts.bodyScope (prepared := compiled.indexed.ancestry)
  (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (program := (Program.ofChecked compiled.sourceProgram)) header) (.statements true header.function.body) header.function.resultType header.output receipt.flow := by
  let inputs := CallableIndexedOwnedPublicPreparedSourceSites.inputs header bridge bindings wellFormed sourceRuntime
    (expressionSyntax := expressionSyntax header)
  have below : ∀ context, Validity header context → RecursiveNamedBoundedContracts.Below budget
      (fun size => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context (header.function.evidence) (header.function.source) ((CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header) context) faults size) :=
    fun context valid child smaller => _meaning context valid child (Nat.le_of_lt smaller)
  let assignments : ∀ context, Validity header context →
      ProtectedForHeader.Stateful.WithReady.AssignmentFaultPreservesWithPayloadAt
        protocol (readiness bridge) (SourceAssignmentHasType (header.function.source))
        (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) functions (registry := registry)
        (Program.ofChecked compiled.sourceProgram) (header.function.evidence) (header.function.source) ((CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header) context) context (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) faults budget
        (fun head => ((fun head => GenericForHeader.Structural.PreparedAssignment (AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments) (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection issued.original.prepared) (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault issued.original.prepared) head)) head) := by
    intro context valid scope assignment operator rhs
    dsimp only [ProtectedForHeader.Stateful.WithReady.AssignmentFaultPreservesWithPayloadAt,
      ProtectedForHeader.Stateful.WithReady.AssignmentReflectsWithPayloadAt,
      RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection,
      RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault]
    unfold RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection
      RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault
    have key := congrArg (fun named : SourceCoreGeneralFunctions.Function => named.signature.key) issued.original.aligned.named
    rw [← key]
    exact (CallableIndexedOwnedPublicPreparedAssignmentReadiness.assignment_fault
      (context := context) (certificates := (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header)) (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
      (factory := (AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments)) (registry := registry) (faults := faults)
      (scope := scope) (assignment := assignment) (operator := operator) (rhs := rhs)
      header bridge issued functions extension (header.function.evidence)
      transport faithful observations header.unique wellFormed diagnosticsFound rebuilt (interprets context valid)
      operandIncluded (CallableIndexedOwnedPublicPreparedSourceSites.signatures header valid) valid.2 valid.1.covers budget (below context valid))
  exact RecursiveNamedImperativeFor.Stateful.WithReady.preservesAt_match_catalog_coupled
    (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (layouts := header.layouts)
    (owner := header.owner) (active := header.active) (frame := compiled.indexed.ancestry.layout.frame)
    (globals := header.globals) (onError := header.onError) (source := (header.function.source))
    (expressionSyntax := expressionSyntax header) (certificates := (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header))
    (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) (solved := header.solved) (factory := (AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments))
    (invalidProjection := (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection issued.original.prepared)) (missingDefault := (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault issued.original.prepared))
    (functions := functions) (definitions := header.definitions_eq) (registered := header.registered)
    (program := (Program.ofChecked compiled.sourceProgram)) (evidence := (header.function.evidence)) (protocol := protocol)
    (readiness := readiness bridge) (conditionGate := condition)
    (facts := ProtectedStateImperativeTypedSourceSites.Facts (header.function.source) (expressionSyntax header))
    (headFacts := ProtectedStateImperativeTypedSourceSites.HeadFacts (header.function.source) (expressionSyntax header))
    (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts (header.function.source))
    (loopFacts := CallableIndexedOwnedAdmittedForBounds.LoopFacts (header.function.source) (expressionSyntax header))
    (initializerFacts := ProtectedStateImperativeInitializerSourceSites.Facts (header.function.source) (expressionSyntax header))
    (assignmentFacts := SourceAssignmentHasType (header.function.source)) (snapshotFacts := SourceBitNotAssignmentValid (header.function.source))
    (producer := producer) (stateTransport := transport) (stateBindings := bindings) (acquire := acquire)
    (validity := Validity header) (extend := fun valid extended => CallableIndexedOwnedPublicPreparedSourceSites.validity_extend header valid extended)
    (budget := budget)
    (sites := inputs.sites) (assignmentSites := inputs.assignments) (initializerSites := inputs.initializers)
    (transfers := inputs.transfers) (snapshots := inputs.snapshots) (observations := observations)
    (assignments := fun context valid => CallableIndexedOwnedAdmittedForHeaderReadiness.assignment_prefix
      (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (certificate := (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header) context) (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) (faults := faults)
      bridge functions extension (header.function.evidence) transport faithful observations header.unique wellFormed valid.2 valid.1.covers budget (below context valid))
    (meaningMost := fun context valid child within => CallableIndexedOwnedAdmittedLexicalReadiness.preserves_at bridge _ (_meaning context valid child within))
    receipt.unaryTyped receipt.assignments unaryIncluded receipt.catalog assignments header.unique
    (CallableIndexedOwnedPreparedCatalogProducers.preserving_heads
      (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (source := (header.function.source)) (expressionSyntax := expressionSyntax header)
      (certificates := (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header)) (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) (factory := (AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments)) (invalidProjection := (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection issued.original.prepared)) (missingDefault := (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault issued.original.prepared))
      bridge functions header.definitions_eq header.registered extension (header.function.evidence) faithful observations condition producer acquire transport bindings header.unique wellFormed
      (Validity header) (fun _ valid => valid.2) (fun _ valid => valid.1.covers)
      (fun valid extended => CallableIndexedOwnedPublicPreparedSourceSites.validity_extend header valid extended)
      budget .reachable (fun _ valid => valid.1) receipt.unaryTyped receipt.assignments unaryIncluded below assignments)
    (CallableIndexedOwnedPreparedCatalogProducers.preserving_loops
      (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (source := (header.function.source)) (expressionSyntax := expressionSyntax header)
      (certificates := (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header)) (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) (factory := (AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments)) (invalidProjection := (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection issued.original.prepared)) (missingDefault := (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault issued.original.prepared))
      bridge functions header.definitions_eq header.registered extension (header.function.evidence) faithful observations condition producer acquire transport bindings header.unique wellFormed
      (Validity header) (fun _ valid => valid.2) (fun _ valid => valid.1.covers)
      (fun valid extended => CallableIndexedOwnedPublicPreparedSourceSites.validity_extend header valid extended)
      budget .reachable receipt.unaryTyped receipt.assignments unaryIncluded below assignments)
    receipt.extracted (CallableIndexedOwnedPublicCatalogPreparedReceipts.ledger issued)

include extension observations producer acquire transport bindings wellFormed sourceRuntime
  diagnosticsFound rebuilt operandIncluded unaryIncluded interprets faithful in
theorem reflects_flow (budget : Nat) (_functionTypes : FunctionRuntimeViews functions)
    (_reflection : ∀ context, Validity header context → RecursiveNamedBoundedContracts.Below budget
      (fun size => CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context (header.function.evidence) (header.function.source) ((CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header) context) faults size)) :
    ProtectedStateImperativeCatalogPayload.ReflectsAtWithReceipt protocol (readiness bridge) condition
      (ProtectedStateImperativeTypedSourceSites.Facts (header.function.source) (expressionSyntax header))
      (CallableIndexedOwnedAdmittedForBounds.LoopFacts (header.function.source) (expressionSyntax header))
      (ProtectedStateImperativeInitializerSourceSites.Facts (header.function.source) (expressionSyntax header))
      functions (Program.ofChecked compiled.sourceProgram) (header.function.evidence) (Validity header) budget (ProtectedStateImperativeCatalogPayload.StructuralHeaderReceipt
  (layouts := header.layouts) (owner := header.owner) (active := header.active)
  (frame := compiled.indexed.ancestry.layout.frame) (globals := header.globals) (onError := header.onError)
  (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (source := (header.function.source)) (certificates := (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header))
  (definitions := compiled.indexed.layouts.definitions) (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) ((fun head => GenericForHeader.Structural.PreparedAssignment (AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments) (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection issued.original.prepared) (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault issued.original.prepared) head)) ((fun head => GenericForHeader.Structural.PreparedUnary true (header.function.source)
  (fun site root => issued.original.prepared.compilation.own.assignments.reasonAt site root SourceCoreAssignmentFaultSites.Kind.bitNot) head)))
      (frame := compiled.indexed.ancestry.layout.frame) (globals := header.globals)
      (source := (header.function.source)) (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) (registry := registry) (faults := faults)
      (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
      header.context (RecursiveNamedCatalogNativeContexts.bodyScope (prepared := compiled.indexed.ancestry)
  (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (program := (Program.ofChecked compiled.sourceProgram)) header) (.statements true header.function.body) header.function.resultType header.output receipt.flow := by
  let inputs := CallableIndexedOwnedPublicPreparedSourceSites.inputs header bridge bindings wellFormed sourceRuntime
    (expressionSyntax := expressionSyntax header)
  let assignments : ∀ context, Validity header context →
      ProtectedForHeader.Stateful.WithReady.AssignmentReflectsWithPayloadAt
        protocol (readiness bridge) (SourceAssignmentHasType (header.function.source))
        (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) functions (registry := registry)
        (Program.ofChecked compiled.sourceProgram) (header.function.evidence) (header.function.source) ((CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header) context) context (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) faults budget
        (fun head => ((fun head => GenericForHeader.Structural.PreparedAssignment (AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments) (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection issued.original.prepared) (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault issued.original.prepared) head)) head) := by
    intro context valid scope assignment operator rhs
    dsimp only [ProtectedForHeader.Stateful.WithReady.AssignmentFaultPreservesWithPayloadAt,
      ProtectedForHeader.Stateful.WithReady.AssignmentReflectsWithPayloadAt,
      RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection,
      RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault]
    unfold RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection
      RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault
    have key := congrArg (fun named : SourceCoreGeneralFunctions.Function => named.signature.key) issued.original.aligned.named
    rw [← key]
    exact (CallableIndexedOwnedPublicPreparedAssignmentReadiness.assignment_reflection
      (context := context) (certificates := (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header)) (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
      (factory := (AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments)) (registry := registry) (faults := faults)
      (scope := scope) (assignment := assignment) (operator := operator) (rhs := rhs)
      header bridge issued functions extension (header.function.evidence)
      transport faithful observations header.unique wellFormed diagnosticsFound rebuilt (interprets context valid)
      operandIncluded (CallableIndexedOwnedPublicPreparedSourceSites.signatures header valid) valid.2 valid.1.covers budget _functionTypes (_reflection context valid))
  exact RecursiveNamedImperativeFor.Stateful.WithReady.reflectsAt_match_catalog_coupled
    (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (layouts := header.layouts)
    (owner := header.owner) (active := header.active) (frame := compiled.indexed.ancestry.layout.frame)
    (globals := header.globals) (onError := header.onError) (source := (header.function.source))
    (expressionSyntax := expressionSyntax header) (certificates := (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header))
    (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) (solved := header.solved) (factory := (AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments))
    (invalidProjection := (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection issued.original.prepared)) (missingDefault := (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault issued.original.prepared))
    (functions := functions) (definitions := header.definitions_eq) (registered := header.registered)
    (program := (Program.ofChecked compiled.sourceProgram)) (evidence := (header.function.evidence)) (protocol := protocol)
    (readiness := readiness bridge) (conditionGate := condition)
    (facts := ProtectedStateImperativeTypedSourceSites.Facts (header.function.source) (expressionSyntax header))
    (headFacts := ProtectedStateImperativeTypedSourceSites.HeadFacts (header.function.source) (expressionSyntax header))
    (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts (header.function.source))
    (loopFacts := CallableIndexedOwnedAdmittedForBounds.LoopFacts (header.function.source) (expressionSyntax header))
    (initializerFacts := ProtectedStateImperativeInitializerSourceSites.Facts (header.function.source) (expressionSyntax header))
    (assignmentFacts := SourceAssignmentHasType (header.function.source)) (snapshotFacts := SourceBitNotAssignmentValid (header.function.source))
    (producer := producer) (stateTransport := transport) (stateBindings := bindings) (acquire := acquire)
    (validity := Validity header) (extend := fun valid extended => CallableIndexedOwnedPublicPreparedSourceSites.validity_extend header valid extended)
    (budget := budget) (sites := inputs.sites) (assignmentSites := inputs.assignments) (initializerSites := inputs.initializers)
    (transfers := inputs.transfers) (snapshots := inputs.snapshots) (observations := observations)
    (reflection := fun context valid child within => CallableIndexedOwnedAdmittedLexicalReadiness.reflects_at bridge _ (_reflection context valid child within))
    receipt.unaryTyped receipt.assignments unaryIncluded receipt.catalog assignments header.unique
    (CallableIndexedOwnedPreparedCatalogProducers.reflecting_heads
      (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (source := (header.function.source)) (expressionSyntax := expressionSyntax header)
      (certificates := (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header)) (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) (factory := (AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments)) (invalidProjection := (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection issued.original.prepared)) (missingDefault := (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault issued.original.prepared))
      bridge functions header.definitions_eq header.registered extension (header.function.evidence) observations condition producer acquire transport bindings header.unique wellFormed
      (Validity header) (fun _ valid => valid.2) (fun _ valid => valid.1.covers)
      (fun valid extended => CallableIndexedOwnedPublicPreparedSourceSites.validity_extend header valid extended)
      budget .reachable (fun _ valid => valid.1) receipt.unaryTyped receipt.assignments unaryIncluded _reflection assignments)
    (CallableIndexedOwnedPreparedCatalogProducers.reflecting_loops
      (values := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (ambient := (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) (source := (header.function.source)) (expressionSyntax := expressionSyntax header)
      (certificates := (CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation header)) (administrative := (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) (factory := (AssignmentDiagnosticOrigins.Factory.prepared receipt.operandsTyped receipt.assignments)) (invalidProjection := (RecursiveNamedPreparedHeaderPolicies.Prepared.invalidProjection issued.original.prepared)) (missingDefault := (RecursiveNamedPreparedHeaderPolicies.Prepared.missingDefault issued.original.prepared))
      bridge functions header.definitions_eq header.registered (header.function.evidence) observations condition producer acquire transport bindings header.unique wellFormed
      (Validity header) (fun _ valid => valid.2) (fun _ valid => valid.1.covers)
      (fun valid extended => CallableIndexedOwnedPublicPreparedSourceSites.validity_extend header valid extended)
      budget .reachable receipt.unaryTyped receipt.assignments unaryIncluded _reflection assignments)
    receipt.extracted (CallableIndexedOwnedPublicCatalogPreparedReceipts.ledger issued)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedCatalogBounds
