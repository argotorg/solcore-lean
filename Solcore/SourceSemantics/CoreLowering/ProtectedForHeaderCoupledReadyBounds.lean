import Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderReflection

/-! Prepared Header endpoints derive the structural eliminator internally from
the actual joint receipt and its same Plan tokens. Genuine unary table rows
provide the unchanged unary diagnostics; assignment callbacks consume the
actual selected preparation payload at the real current state. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedForHeader
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalControl (allocate_absent allocate_initialized sequence_rename valid_extend)
open CallableIndexedHistory (NativeFrame)
open TypedForHeader (Fallthrough)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {administrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (bindings : ProtectedExpressionMeaning.Binds entry)
  (meaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults entry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)

namespace Stateful
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (condition : Location → NativeFrame → Prop)
  (producer : OrdinaryAllocation.Producer protocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ location native, condition location native → OrdinaryAllocation.ReadyAt producer location native)
  (stateTransport : AdministrativeTransport protocol) (stateBindings : Bindings protocol)

namespace WithReady
open RecursiveNamedLexicalContracts.Stateful.WithReady
variable (readiness : Readiness protocol)
  (facts : SourceSemantics.Context → List ForItemForm → Prop)
  (itemFacts : SourceSemantics.Context → ForItemForm → Prop)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop)
  (snapshotFacts : SourceSemantics.Context → AssignmentResolution → Prop)
  (sites : StaticSites facts itemFacts exprFacts assignmentFacts snapshotFacts program evidence source)
  (transfers : AllocationTransfers protocol readiness stateBindings source)

variable {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {factory : AssignmentDiagnosticOrigins.Factory true diagnosticPolicy source invalidOperand}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}

include definitions registered observations producer acquire stateTransport stateBindings sites transfers in
theorem preserves_fault_coupled_bounded_for
    (unaryTyped : EmittedDiagnosticTokenPlan.UnaryTyped source)
    (issued : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep table reason token → faults reason token)
    (validity : SourceSemantics.Context → Prop)
    (snapshots : SnapshotTransfers protocol readiness validity snapshotFacts program evidence source)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentPrefixPreservesAt protocol readiness assignmentFacts functions (registry := registry)
      program evidence source (certificates context) context administrative budget)
    (assignmentFaults : ∀ context, validity context → AssignmentFaultPreservesWithPayloadAt protocol readiness assignmentFacts functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget
        (fun head => GenericForHeader.Structural.PreparedAssignment factory invalidProjection missingDefault head))
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ExpressionPreservesAt protocol readiness program evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (certificates context)
        (source := source) (context := context) (faults := faults) size)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) {plan : EmittedDiagnosticPlan.Plan factory}
    (coupled : GenericForHeader.Coupled factory invalidProjection missingDefault tree plan)
    (tokens : EmittedDiagnosticTokenPlan.TokensFor factory (fun site root => table.reasonAt site root .bitNot) plan)
    (valid : validity context) (itemsFacts : facts context items)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : readiness.Ready context state) {reason : Dynamic.SemanticFault}
    {size : Nat} (trace : SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      FaultTransition readiness state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact Tree.preserves_fault_reachable_bounded_for_with_eliminator
    (values := values) (source := source) (certificates := certificates)
    (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (evidence := evidence) (observations := observations)
    (protocol := protocol) (condition := condition) (producer := producer) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (readiness := readiness) (facts := facts) (itemFacts := itemFacts) (exprFacts := exprFacts)
    (assignmentFacts := assignmentFacts) (snapshotFacts := snapshotFacts) (sites := sites) (transfers := transfers)
    (fun head => GenericForHeader.Structural.PreparedAssignment factory invalidProjection missingDefault head)
    (fun head => GenericForHeader.Structural.PreparedUnary true source (fun site root => table.reasonAt site root .bitNot) head)
    (fun _ receipt => receipt.errors unaryTyped issued unaryIncluded)
    validity snapshots extend budget assignments assignmentFaults boundedMeaning
    (GenericForHeader.Structural.of_coupled coupled tokens)
    valid itemsFacts environments heaps locals agrees actualTyped reference read unmapped state gate ready trace bounded

include definitions registered observations producer acquire stateTransport stateBindings sites transfers in
theorem reflects_coupled_bounded_for
    (unaryTyped : EmittedDiagnosticTokenPlan.UnaryTyped source)
    (issued : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep table reason token → faults reason token)
    (validity : SourceSemantics.Context → Prop)
    (snapshots : SnapshotTransfers protocol readiness validity snapshotFacts program evidence source)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentReflectsWithPayloadAt protocol readiness assignmentFacts functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget
        (fun head => GenericForHeader.Structural.PreparedAssignment factory invalidProjection missingDefault head))
    (boundedReflection : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ExpressionReflectsAt protocol readiness program evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (certificates context)
        (source := source) (context := context) (faults := faults) size))
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) {plan : EmittedDiagnosticPlan.Plan factory}
    (coupled : GenericForHeader.Coupled factory invalidProjection missingDefault tree plan)
    (tokens : EmittedDiagnosticTokenPlan.TokensFor factory (fun site root => table.reasonAt site root .bitNot) plan)
    (valid : validity context) (itemsFacts : facts context items)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : readiness.Ready context state)
    {size : Nat} (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) (bounded : size ≤ budget) :
    ResultAtFor protocol readiness condition validity size registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment ⟨scope, mapping, world, before, store, canonical⟩ state items value finalStore := by
  exact Tree.reflects_reachable_bounded_for_with_eliminator
    (values := values) (source := source) (certificates := certificates)
    (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (evidence := evidence) (observations := observations)
    (protocol := protocol) (condition := condition) (producer := producer) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (readiness := readiness) (facts := facts) (itemFacts := itemFacts) (exprFacts := exprFacts)
    (assignmentFacts := assignmentFacts) (snapshotFacts := snapshotFacts) (sites := sites) (transfers := transfers)
    (fun head => GenericForHeader.Structural.PreparedAssignment factory invalidProjection missingDefault head)
    (fun head => GenericForHeader.Structural.PreparedUnary true source (fun site root => table.reasonAt site root .bitNot) head)
    (fun _ receipt => receipt.errors unaryTyped issued unaryIncluded)
    validity snapshots extend budget assignments boundedReflection
    (GenericForHeader.Structural.of_coupled coupled tokens)
    valid itemsFacts environments heaps locals agrees actualTyped reference read unmapped state gate ready evaluated bounded

end WithReady
end Stateful
end Solcore.SourceSemantics.CoreLowering.ProtectedForHeader
