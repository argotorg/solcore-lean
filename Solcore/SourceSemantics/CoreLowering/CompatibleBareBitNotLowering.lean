import Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotFaults

/-! Actual compatible compiler success supplies the complete bare-root layout.
No child compiler/evaluation or helper typing premise remains in these bridges.
Writable-local/source numeric typing and authenticated heap/function leaves are
still independent semantic conditions; source checker admission is unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotLowering
open Core Frontend SourceInference GeneralHeap GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces

variable {compilation : SourceCoreCompatibleDataPlaces.Context}
  {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
  {faults : FaultRep} {assignment : AssignmentResolution} {administrativeContext : Core.Context}
  {expression : ExpressionLowerer} {fuel : Nat} {operator : Syntax.ValueAssignOp}
  {next lowered : Expr} {outputType : Ty} {reasonAt : ExpressionId → Word}
  {invalid invalidOperand : Word} {missing : TypeSystem.Ty → Word}
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
  {before after : Dynamic.Heap} {store finalStore : Store} {result : Value}
  (rootTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
    WritableLocal context assignment.target.root binder.scheme.body)
  (bare : assignment.target.projections = [])
  (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
    SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
  {identities : Dynamic.Value → Word → Prop}
  (observations : FunctionObservations compilation.checked.catalog functions identities)
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
  (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)

include rootTyped bare profile observations environments heaps locals

/-- Every completed actual compiler output has an independent unary failure
or snapshot-write trace. The real seven-slot continuation is recovered only
after the source write, and remains an output of reflection. -/
theorem reflects
    (accepted : lower compilation compilation.checked.signatures expression fuel source scope site assignment operator none
      outputType next reasonAt invalid invalidOperand missing = .ok lowered)
    (token : faults (.invalidUnaryOperand .bitNot) invalidOperand)
    (completed : Evaluates coreEnvironment store lowered result finalStore) :
    CompatiblePlaceBitNotMeaning.Result compilation.checked registry functions program context evidence source faults assignment.target
      environment coreEnvironment before store mapping world next outputType result finalStore := by
  obtain ⟨binder, prepared, index, binding, rootEq, view, slot, layout, lowering⟩ :=
    CompatibleBareBitNotCertificates.of_lower bare profile accepted
  exact CompatibleBareBitNotMeaning.reflects layout bare observations (view ▸ profile) environments heaps locals slot
    (rootEq ▸ rootTyped binder binding) token (lowering ▸ completed)

/-- An independent successful snapshot trace executes to Unit and the related
written heap through the actual compiler output, at the same world and map. -/
theorem preserves
    (accepted : lower compilation compilation.checked.signatures expression fuel source scope site assignment operator none
      .unit (LanguageResult.success .unit) reasonAt invalid invalidOperand missing = .ok lowered)
    {updated : Dynamic.Value}
    (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
      environment before assignment.target updated after) :
    ∃ finalStore, Evaluates coreEnvironment store lowered (.inRight .word .unit) finalStore ∧
      HeapRepresents compilation.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨binder, prepared, index, binding, rootEq, view, slot, layout, lowering⟩ :=
    CompatibleBareBitNotCertificates.of_lower bare profile accepted
  rw [lowering]
  exact CompatibleBareBitNotMeaning.preserves layout bare observations (view ▸ profile) environments heaps locals slot
    (rootEq ▸ rootTyped binder binding) trace _ _

/-- A source fault is exactly the absent unary operand; actual generated code
returns its token and preserves the entire native store. -/
theorem preserves_fault
    (accepted : lower compilation compilation.checked.signatures expression fuel source scope site assignment operator none
      outputType next reasonAt invalid invalidOperand missing = .ok lowered)
    {reason : Dynamic.SemanticFault}
    (trace : Dynamic.SourcePlaceBitNotFaults program context evidence source environment before assignment.target reason after) :
    reason = .invalidUnaryOperand .bitNot ∧ after = before ∧
      Evaluates coreEnvironment store lowered (.inLeft outputType (.word invalidOperand)) store := by
  obtain ⟨binder, prepared, index, binding, rootEq, view, slot, layout, lowering⟩ :=
    CompatibleBareBitNotCertificates.of_lower bare profile accepted
  rw [lowering]
  exact CompatibleBareBitNotMeaning.preserves_fault layout bare observations (view ▸ profile) environments heaps locals slot
    (rootEq ▸ rootTyped binder binding) trace _ _ _ _

end Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotLowering
