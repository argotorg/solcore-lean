import Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentReflection
import Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignmentReflection
import Solcore.SourceSemantics.CoreLowering.ProtectedStateAssignmentHeadContracts
import Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentPreservation
import Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignmentPreservation
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatementCertificates
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentReachableDiagnostics

/-! Bare and projected Heads return the actual fault or written-prefix state.
Projected branches relay real keys, getter, RHS and latest-root write stages.
Seven temporary slots and measured continuation bounds remain the original receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceReachedDiagnostics
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces
universe u v
/-- Bare paths request only operand interpretation; projected paths retain
actual phase and fault receipts for their own prepared route. -/
inductive ShapeErrors (values : SourceCoreCompatibleValues.Context) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions values.checked.catalog.definitions} (functions : FunctionModel values.checked.catalog ambient)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (source : TypedSource) (context : SourceSemantics.Context) (certificate : GenericExpressionMeaning.Certificate)
    (scope : SourceCoreLocalCell.Scope) (administrative : Core.Context) (environment : Dynamic.Environment)
    (place : PlaceResolution) (prepared : Prepared) (operator : Syntax.ValueAssignOp) (invalid : Word)
    {initialIndex : ProtectedStateTransition.Index} (initial : protocol.State initialIndex) (faults : FunctionCalls.FaultRep) :
    {codes : List SourceCoreBasic.LoweredExpr} → {leaf : TypeSystem.Ty} →
    GenericAssignmentStatements.Shape values source context certificate scope administrative ambient.definitions
      place prepared codes leaf → Prop where
  | bare {empty : place.projections = []} {layout : CompatibleBareAssignment.Layout values prepared}
      (operands : AssignmentOperandDiagnostics.OperandsLaw faults operator invalid) :
      ShapeErrors values registry functions protocol source context certificate scope administrative environment
        place prepared operator invalid initial faults (.bare empty layout)
  | projected {codes : List SourceCoreBasic.LoweredExpr} {leaf : TypeSystem.Ty}
      {sourceTypes : List TypeSystem.Ty} {site : SourceCoreElaboration.ErrorSite}
      {layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) values source certificate
        scope site place prepared codes sourceTypes leaf administrative}
      {ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none}
      (missing : MissingFor values.checked registry functions protocol source site place prepared leaf initial faults)
      (uninitialized : UninitializedFor values.checked registry functions protocol environment place prepared initial faults) :
      ShapeErrors values registry functions protocol source context certificate scope administrative environment
        place prepared operator invalid initial faults (.projected layout ordinary)

theorem ShapeErrors.of_uniform {values : SourceCoreCompatibleValues.Context} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
    {Records : Type v} {protocol : ProtectedStateTransition.Protocol.{u, v} Records}
    {source : TypedSource} {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context} {environment : Dynamic.Environment}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {head : GenericAssignmentStatements.Head values source context certificate scope administrative ambient.definitions assignment operator rhs}
    {initialIndex : ProtectedStateTransition.Index} {initial : protocol.State initialIndex} {faults : FunctionCalls.FaultRep}
    (errors : head.ReachableErrors registry faults) :
    ShapeErrors values registry functions protocol source context certificate scope administrative environment
      assignment.target head.prepared operator head.invalid initial faults head.shape := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  change ShapeErrors values registry functions protocol source context certificate scope administrative environment
    assignment.target prepared operator invalid initial faults shape
  cases shape with
  | bare empty layout => exact .bare (empty := empty) (layout := layout) errors.operands
  | projected layout ordinary => exact .projected (layout := layout) (ordinary := ordinary) (MissingFor.of_uniform errors.missing) (UninitializedFor.of_uniform errors.uninitialized)

end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceReachedDiagnostics

namespace Solcore.SourceSemantics.CoreLowering.ProtectedAssignmentHeads.Stateful.Head
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning
universe u v
variable {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head values source context certificate scope administrative ambient.definitions assignment operator rhs)
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)


include transport extension faithful observations environments heaps locals agrees actualTyped initialState in
theorem preserves_prefix_bounded (budget : Nat)
    (boundedMeaning : RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.PreservesAt protocol (payloadModel values.checked registry functions) program context evidence source certificate faults size)) {updated : Dynamic.Value} {after : Dynamic.Heap}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignment program size context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before assignment.target rhs updated after) (bounded : size ≤ budget) :
    ∃ finalStore finalMap finalWorld slots,
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  cases shape with
  | bare empty layout =>
    obtain ⟨_, finalStore, finalMap, finalWorld, slots, _, finalHeaps, maps, worlds, preservation, metadata, count, typed, continuation, post⟩ :=
      ProtectedBareAssignment.Stateful.preserves_prefix_bounded protocol transport budget initialState layout empty extension boundedMeaning observations right found rightView rightType profile
        environments heaps locals agrees actualTyped slot writable trace bounded invalid
    exact ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, preservation, metadata, count,
      by simpa [GenericAssignmentStatements.Head.writtenContext, CompatibleRenamedPlaceSuccess.writtenContext, CompatibleBareAssignment.writtenContext,
        Prepared.optionalLeaf, SourceCoreCalls.packArguments, layout.sameType] using typed,
      post, continuation⟩
  | projected layout ordinary =>
    obtain ⟨_, finalStore, finalMap, finalWorld, _, finalHeaps, maps, worlds, frame, metadata, slots, count, typed, continuation, post⟩ :=
      ProtectedPlaceAssignmentSuccess.Stateful.preserves_prefix_bounded budget layout ordinary extension protocol transport boundedMeaning faithful observations right found rightView rightType profile
        environments heaps locals agrees actualTyped initialState slot writable trace bounded invalid
    exact ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, frame, metadata, count, typed, post, continuation⟩

include transport extension faithful observations environments heaps locals agrees actualTyped initialState in
theorem preserves_fault_bounded_with_diagnostics (budget : Nat)
    (boundedMeaning : RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.PreservesAt protocol (payloadModel values.checked registry functions) program context evidence source certificate faults size)) (errors : ProtectedPlaceReachedDiagnostics.ShapeErrors values registry functions protocol source context certificate
      scope administrative environment assignment.target head.prepared operator head.invalid initialState faults head.shape)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program size context evidence source environment before assignment.target operator rhs reason after) (bounded : size ≤ budget)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  change ProtectedPlaceReachedDiagnostics.ShapeErrors values registry functions protocol source context certificate
    scope administrative environment assignment.target prepared operator invalid initialState faults shape at errors
  cases errors with
  | @bare empty layout operands =>
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata, post⟩ :=
      ProtectedBareAssignment.Stateful.preserves_fault_reachable_bounded protocol budget initialState layout empty extension boundedMeaning observations right found rightView rightType profile
        environments heaps locals agrees actualTyped slot writable trace bounded next output invalid operands
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata,
      post⟩
  | @projected codes leaf sourceTypes site layout ordinary missingFor uninitializedFor =>
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata, post⟩ :=
      ProtectedPlaceAssignmentFaults.Stateful.preserves_bounded_with_diagnostics budget layout ordinary extension protocol transport boundedMeaning faithful observations
      right found rightView rightType profile environments heaps locals agrees actualTyped initialState missingFor uninitializedFor slot writable trace bounded next output invalid
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata,
      post⟩


include transport extension faithful observations environments heaps locals agrees actualTyped initialState in
theorem preserves_fault_reachable_bounded (budget : Nat)
    (boundedMeaning : RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.PreservesAt protocol (payloadModel values.checked registry functions) program context evidence source certificate faults size)) (errors : head.ReachableErrors registry faults)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program size context evidence source environment before assignment.target operator rhs reason after) (bounded : size ≤ budget)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact preserves_fault_bounded_with_diagnostics (functions := functions) (extension := extension)
    (program := program) (evidence := evidence) (protocol := protocol) (transport := transport)
    (faithful := faithful) (observations := observations) (head := head) (environments := environments)
    (heaps := heaps) (locals := locals) (agrees := agrees) (actualTyped := actualTyped) (initialState := initialState)
    budget boundedMeaning (ProtectedPlaceReachedDiagnostics.ShapeErrors.of_uniform errors) trace bounded next output

include transport extension faithful observations environments heaps locals agrees actualTyped initialState in
theorem reflects_bounded_with_diagnostics (budget : Nat)
    (boundedReflection : RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.ReflectsAt protocol (payloadModel values.checked registry functions) program context evidence source certificate faults size)) (functionTypes : FunctionRuntimeViews functions) (errors : ProtectedPlaceReachedDiagnostics.ShapeErrors values registry functions protocol source context certificate
      scope administrative environment assignment.target head.prepared operator head.invalid initialState faults head.shape)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    {size : Nat} (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore) (bounded : size ≤ budget) :
    ProtectedStateAssignmentHeadContracts.ResultAt protocol size values.checked registry functions program context evidence source faults
      scope (head.writtenContext actualContext) assignment.target operator rhs environment canonical actual
      before store mapping world initialState (next.rename ξ) output value finalStore := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  change ProtectedPlaceReachedDiagnostics.ShapeErrors values registry functions protocol source context certificate
    scope administrative environment assignment.target prepared operator invalid initialState faults shape at errors
  cases errors with
  | @bare empty layout operands =>
    have result := ProtectedBareAssignment.Stateful.reflects_reachable_bounded protocol transport budget initialState layout empty extension boundedReflection observations right found rightView rightType profile
      environments heaps locals agrees actualTyped slot writable operands completed bounded
    cases result with
    | fault trace same matched finalHeaps maps worlds preservation metadata post =>
      exact .fault trace same matched finalHeaps maps worlds preservation metadata
        post
    | success trace _ finalHeaps maps worlds preservation metadata count typed strict remaining post =>
      exact .success trace finalHeaps maps worlds preservation metadata count
        (by simpa [GenericAssignmentStatements.Head.writtenContext, CompatibleRenamedPlaceSuccess.writtenContext, CompatibleBareAssignment.writtenContext,
          Prepared.optionalLeaf, SourceCoreCalls.packArguments, layout.sameType] using typed)
        post strict remaining
  | @projected codes leaf sourceTypes site layout ordinary missingFor uninitializedFor =>
    have result := ProtectedPlaceAssignmentReflection.Stateful.reflects_bounded_with_diagnostics budget layout ordinary extension protocol transport boundedReflection functionTypes faithful observations
      right found rightView rightType profile environments heaps agrees actualTyped initialState missingFor uninitializedFor locals slot writable completed bounded
    cases result with
    | fault trace same matched finalHeaps maps worlds frame metadata post =>
      exact .fault trace same matched finalHeaps maps worlds frame metadata post
    | committed trace finalHeaps maps worlds frame metadata count typed post strict remaining =>
      exact .success trace finalHeaps maps worlds frame metadata count typed post strict remaining


include transport extension faithful observations environments heaps locals agrees actualTyped initialState in
theorem reflects_reachable_bounded (budget : Nat)
    (boundedReflection : RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.ReflectsAt protocol (payloadModel values.checked registry functions) program context evidence source certificate faults size)) (functionTypes : FunctionRuntimeViews functions) (errors : head.ReachableErrors registry faults)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    {size : Nat} (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore) (bounded : size ≤ budget) :
    ProtectedStateAssignmentHeadContracts.ResultAt protocol size values.checked registry functions program context evidence source faults
      scope (head.writtenContext actualContext) assignment.target operator rhs environment canonical actual
      before store mapping world initialState (next.rename ξ) output value finalStore := by
  exact reflects_bounded_with_diagnostics (functions := functions) (extension := extension)
    (program := program) (evidence := evidence) (protocol := protocol) (transport := transport)
    (faithful := faithful) (observations := observations) (head := head) (environments := environments)
    (heaps := heaps) (locals := locals) (agrees := agrees) (actualTyped := actualTyped) (initialState := initialState)
    budget boundedReflection functionTypes (ProtectedPlaceReachedDiagnostics.ShapeErrors.of_uniform errors) completed bounded

end Solcore.SourceSemantics.CoreLowering.ProtectedAssignmentHeads.Stateful.Head
