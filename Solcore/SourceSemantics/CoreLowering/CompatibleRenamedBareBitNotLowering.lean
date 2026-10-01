import Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNotSource

/-! Actual absent-RHS lowering supplies the bare numeric layout and its lexical
slot. The source/runtime interface names the real inserted environment and
seven typed continuation slots. No source-expression child or helper execution
is an input to these consumers. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNot
open Core Frontend SourceInference GeneralHeap CoreProof DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatibleBareBitNotCertificates

variable {compilation : SourceCoreCompatibleDataPlaces.Context} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {scope : Scope} {assignment : AssignmentResolution} {site : SourceCoreElaboration.ErrorSite}
  {expression : ExpressionLowerer} {fuel : Nat} {operator : Syntax.ValueAssignOp} {next lowered : Expr} {output : Ty}
  {reasonAt : ExpressionId → Word} {invalid invalidOperand : Word} {missing : TypeSystem.Ty → Word}
  {administrativeContext actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  {identities : Dynamic.Value → Word → Prop}
  (rootTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
    WritableLocal context assignment.target.root binder.scheme.body)
  (bare : assignment.target.projections = [])
  (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
    SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
  (observations : FunctionObservations compilation.checked.catalog functions identities)
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
    mapping world administrativeContext scope environment canonical)
  (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)

include rootTyped bare profile observations environments heaps locals agrees

theorem reflects_of_lower
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (accepted : lower compilation compilation.checked.signatures expression fuel source scope site assignment operator none
      output next reasonAt invalid invalidOperand missing = .ok lowered)
    {faults : FaultRep} {value : Value} {finalStore : Store}
    (token : faults (.invalidUnaryOperand .bitNot) invalidOperand)
    (completed : Evaluates actual store (lowered.rename ξ) value finalStore) :
    ∃ prepared, Result compilation.checked registry functions program context evidence source faults prepared assignment.target
      environment before store mapping world actual actualContext ξ next output value finalStore := by
  obtain ⟨binder, prepared, index, binding, rootEq, view, slot, layout, lowering⟩ :=
    CompatibleBareBitNotCertificates.of_lower bare profile accepted
  refine ⟨prepared, ?_⟩
  exact reflects layout bare observations (view ▸ profile) environments heaps locals agrees actualTyped slot
    (rootEq ▸ rootTyped binder binding) token (lowering ▸ completed)

theorem preserves_prefix_of_lower
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (accepted : lower compilation compilation.checked.signatures expression fuel source scope site assignment operator none
      output next reasonAt invalid invalidOperand missing = .ok lowered)
    {updated : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
      environment before assignment.target updated after) :
    ∃ prepared replacement finalStore slots,
      ValueRep compilation.checked registry functions mapping world prepared.route.rootSourceType updated replacement prepared.route.rootType ∧
      HeapRepresents compilation.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes world (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions ∧
      ContinuationAgreement actual store (lowered.rename ξ) (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  obtain ⟨binder, prepared, index, binding, rootEq, view, slot, layout, lowering⟩ :=
    CompatibleBareBitNotCertificates.of_lower bare profile accepted
  obtain ⟨replacement, finalStore, slots, represented, finalHeaps, frame, metadata, count, typed, agreement⟩ :=
    preserves_prefix layout bare observations (view ▸ profile) environments heaps locals agrees actualTyped slot
      (rootEq ▸ rootTyped binder binding) trace (binaryOperator (prepared.route.leafType = .integer) operator) invalidOperand
  exact ⟨prepared, replacement, finalStore, slots, represented, finalHeaps, frame, metadata, count, typed,
    lowering.symm ▸ agreement next output⟩

theorem preserves_fault_of_lower
    (accepted : lower compilation compilation.checked.signatures expression fuel source scope site assignment operator none
      output next reasonAt invalid invalidOperand missing = .ok lowered)
    {after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (trace : Dynamic.SourcePlaceBitNotFaults program context evidence source environment before assignment.target reason after) :
    reason = .invalidUnaryOperand .bitNot ∧ after = before ∧
      Evaluates actual store (lowered.rename ξ) (.inLeft output (.word invalidOperand)) store := by
  obtain ⟨binder, prepared, index, binding, rootEq, view, slot, layout, lowering⟩ :=
    CompatibleBareBitNotCertificates.of_lower bare profile accepted
  rw [lowering]
  exact preserves_fault layout bare observations (view ▸ profile) environments heaps locals agrees slot
    (rootEq ▸ rootTyped binder binding) trace _ _ _ _

end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNot
