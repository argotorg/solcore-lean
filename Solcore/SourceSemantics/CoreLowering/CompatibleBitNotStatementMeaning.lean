import Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatementHead

/-! Bare unary head semantics close the actual numeric update/fault and retain
all seven real administrative values. The RHS slot is Unit, not a source child. -/
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
theorem preserves_prefix {updated : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
      environment before assignment.target updated after) :
    ∃ finalStore finalMap finalWorld slots,
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  obtain ⟨_, finalStore, slots, _, finalHeaps, frame, metadata, count, typed, continuation⟩ :=
    CompatibleRenamedBareBitNot.preserves_prefix (compilation := values) head.layout head.bare observations head.profile
      environments heaps locals agrees actualTyped head.slot head.writable trace (binaryOperator (head.prepared.route.leafType = .integer) .equal) head.invalid
  exact ⟨finalStore, mapping, world, slots, finalHeaps, .refl _, .refl _, frame, metadata, count, typed, continuation⟩

include observations environments heaps locals agrees in
theorem preserves_fault (errors : head.Errors faults)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceBitNotFaults program context evidence source environment before assignment.target reason after)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨rfl, rfl, evaluated⟩ := CompatibleRenamedBareBitNot.preserves_fault (compilation := values)
    head.layout head.bare observations head.profile environments heaps locals agrees head.slot head.writable trace
      next output (binaryOperator (head.prepared.route.leafType = .integer) .equal) head.invalid
  exact ⟨head.invalid, store, mapping, world, evaluated, errors, heaps, .refl _, .refl _, .refl _ _, .refl _⟩

include observations environments heaps locals agrees actualTyped in
theorem reflects (errors : head.Errors faults)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    (completed : Evaluates actual store ((head.emit next output).rename ξ) value finalStore) :
    (∃ reason token after finalMap finalWorld,
      Dynamic.SourcePlaceBitNotFaults program context evidence source environment before assignment.target reason after ∧
      value = .inLeft output (.word token) ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after) ∨
    (∃ updated after written finalMap finalWorld slots,
      Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
        environment before assignment.target updated after ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after written ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap written ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      Evaluates (slots ++ actual) written (shift 7 (next.rename ξ)) value finalStore) := by
  cases CompatibleRenamedBareBitNot.reflects (compilation := values) head.layout head.bare observations head.profile
    environments heaps locals agrees actualTyped head.slot head.writable errors completed with
  | fault trace same matched stores =>
    subst finalStore
    exact .inl ⟨_, _, before, mapping, world, trace, same, matched, heaps, .refl _, .refl _, .refl _ _, .refl _⟩
  | success trace _ finalHeaps frame metadata count typed continuation =>
    exact .inr ⟨_, _, _, mapping, world, _, trace, finalHeaps, .refl _, .refl _, frame, metadata, count, typed, continuation⟩

end Head
end Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatements
