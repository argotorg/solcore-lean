import Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatementMeaning

/-! The existing bare unary Head exposes the independent source trace and
the actual strict native continuation. No expression child is invented for
the administrative Unit RHS. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatements
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning

namespace Head
variable   {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {identities : Dynamic.Value → Word → Prop}
  (observations : FunctionObservations values.checked.catalog functions identities)
  {assignment : AssignmentResolution}
  (head : Head context scope assignment)
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)

include observations environments heaps locals agrees actualTyped in
theorem reflects_sized (errors : head.Errors faults)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    {size : Nat} (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore) :
    (∃ sourceSize reason token after finalMap finalWorld,
      SourceExecutionSize.SourcePlaceBitNotFaults program sourceSize context evidence source environment before assignment.target reason after ∧
      value = .inLeft output (.word token) ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after) ∨
    (∃ sourceSize updated after written finalMap finalWorld slots remainingSize,
      SourceExecutionSize.SourcePlaceSnapshotUpdate program sourceSize context evidence source Dynamic.BitNotSnapshot
        environment before assignment.target updated after ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after written ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap written ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      remainingSize < size ∧ EvaluationSize remainingSize (slots ++ actual) written (shift 7 (next.rename ξ)) value finalStore) := by
  cases CompatibleRenamedBareBitNot.reflects_sized (compilation := values) head.layout head.bare observations head.profile
    environments heaps locals agrees actualTyped head.slot head.writable errors completed with
  | fault trace same matched stores =>
    subst finalStore
    exact .inl ⟨_, _, _, before, mapping, world, trace, same, matched, heaps, .refl _, .refl _, .refl _ _, .refl _⟩
  | success trace _ finalHeaps frame metadata count typed smaller continuation =>
    exact .inr ⟨_, _, _, _, mapping, world, _, _, trace, finalHeaps, .refl _, .refl _, frame, metadata, count, typed, smaller, continuation⟩

end Head
end Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatements
