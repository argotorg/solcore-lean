import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedAssignmentReadiness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForHeaderBounds
import Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderCoupledReadyBounds

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
      (program := Program.ofChecked compiled.sourceProgram) (evidence := header.function.evidence) (observations := observations)
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
      (program := Program.ofChecked compiled.sourceProgram) (evidence := header.function.evidence) (observations := observations)
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
