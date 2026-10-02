import Solcore.SourceSemantics.CoreLowering.GenericAssignmentReachableDiagnostics

/-! Shared assignment composition consumes a typed expression meaning contract.
Concrete clients discharge that contract with their own expression Tree theorem.
Seven actual temporary values retain post-write typing and closure captures. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatements
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning

namespace Head
variable {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel values.checked registry functions)
    program context evidence source certificate faults)
  (reflection : TypedGenericExpressionMeaning.Reflects (payloadModel values.checked registry functions)
    program context evidence source certificate faults)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : Head values source context certificate scope administrative ambient.definitions assignment operator rhs)
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)

include extension meaning faithful observations environments heaps locals agrees actualTyped in
theorem preserves_prefix {updated : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before assignment.target rhs updated after) :
    ∃ finalStore finalMap finalWorld slots,
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  cases shape with
  | bare empty layout =>
    obtain ⟨_, finalStore, finalMap, finalWorld, slots, _, finalHeaps, maps, worlds, frame, metadata, count, typed, continuation⟩ :=
      CompatibleBareAssignment.preserves_prefix layout empty extension meaning observations right found rightView rightType profile
        environments heaps locals agrees actualTyped slot writable trace invalid
    exact ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, frame, metadata, count, by simpa [Head.writtenContext, CompatibleRenamedPlaceSuccess.writtenContext, CompatibleBareAssignment.writtenContext, Prepared.optionalLeaf, SourceCoreCalls.packArguments, layout.sameType] using typed, continuation⟩
  | projected layout ordinary =>
    obtain ⟨_, finalStore, finalMap, finalWorld, _, finalHeaps, maps, worlds, frame, metadata, slots, count, typed, continuation⟩ :=
      CompatibleRenamedPlaceSuccess.preserves_prefix layout ordinary extension meaning faithful observations right found rightView rightType profile
        environments heaps locals agrees actualTyped slot writable trace invalid
    exact ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, frame, metadata, count, typed, continuation⟩

include extension meaning faithful observations environments heaps locals agrees actualTyped in
theorem preserves_fault_reachable (errors : head.ReachableErrors registry faults)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target operator rhs reason after)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  cases shape with
  | bare empty layout =>
    exact CompatibleBareAssignment.preserves_fault_reachable layout empty extension meaning observations right found rightView rightType profile
      environments heaps locals agrees actualTyped slot writable trace next output invalid errors.operands
  | projected layout ordinary =>
    exact CompatibleRenamedPlaceFaults.preserves layout ordinary extension meaning faithful observations
      errors.missing errors.uninitialized right found rightView rightType profile environments heaps locals agrees actualTyped slot writable trace next output invalid

include extension meaning faithful observations environments heaps locals agrees actualTyped in
/-- Compatibility entry point retaining the original diagnostic receipt. -/
theorem preserves_fault (errors : head.Errors registry faults)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target operator rhs reason after)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  exact preserves_fault_reachable functions extension program evidence meaning faithful observations head environments heaps locals agrees actualTyped errors.reachable trace next output

include extension meaning reflection faithful observations environments heaps locals agrees actualTyped in
theorem reflects_reachable (functionTypes : FunctionRuntimeViews functions) (errors : head.ReachableErrors registry faults)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    (completed : Evaluates actual store ((head.emit next output).rename ξ) value finalStore) :
    (∃ reason token after finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target operator rhs reason after ∧
      value = .inLeft output (.word token) ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after) ∨
    (∃ updated after written finalMap finalWorld slots,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before assignment.target rhs updated after ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after written ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap written ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      Evaluates (slots ++ actual) written (shift 7 (next.rename ξ)) value finalStore) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  cases shape with
  | bare empty layout =>
    have result := CompatibleBareAssignment.reflects_reachable layout empty extension reflection observations right found rightView rightType profile
      environments heaps locals agrees actualTyped slot writable errors.operands completed
    cases result with
    | fault trace same matched finalHeaps maps worlds frame metadata => exact .inl ⟨_, _, _, _, _, trace, same, matched, finalHeaps, maps, worlds, frame, metadata⟩
    | success trace _ finalHeaps maps worlds frame metadata count typed continuation =>
      exact .inr ⟨_, _, _, _, _, _, trace, finalHeaps, maps, worlds, frame, metadata, count, by simpa [Head.writtenContext, CompatibleRenamedPlaceSuccess.writtenContext, CompatibleBareAssignment.writtenContext, Prepared.optionalLeaf, SourceCoreCalls.packArguments, layout.sameType] using typed, continuation⟩
  | projected layout ordinary =>
    rcases CompatibleRenamedPlaceReflection.reflects layout ordinary extension reflection meaning functionTypes faithful observations
      errors.missing errors.uninitialized right found rightView rightType profile environments heaps agrees actualTyped locals slot writable completed with
      ⟨_, _, _, _, _, trace, same, matched, finalHeaps, maps, worlds, frame, metadata⟩ |
      ⟨_, _, _, _, _, _, trace, finalHeaps, maps, worlds, frame, metadata, count, typed, continuation⟩
    · exact .inl ⟨_, _, _, _, _, trace, same, matched, finalHeaps, maps, worlds, frame, metadata⟩
    · exact .inr ⟨_, _, _, _, _, _, trace, finalHeaps, maps, worlds, frame, metadata, count, typed, continuation⟩
include extension meaning reflection faithful observations environments heaps locals agrees actualTyped in
/-- Compatibility entry point retaining the original diagnostic receipt. -/
theorem reflects (functionTypes : FunctionRuntimeViews functions) (errors : head.Errors registry faults)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    (completed : Evaluates actual store ((head.emit next output).rename ξ) value finalStore) :
    (∃ reason token after finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target operator rhs reason after ∧
      value = .inLeft output (.word token) ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after) ∨
    (∃ updated after written finalMap finalWorld slots,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before assignment.target rhs updated after ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after written ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap written ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      Evaluates (slots ++ actual) written (shift 7 (next.rename ξ)) value finalStore) := by
  exact reflects_reachable functions extension program evidence meaning reflection faithful observations head environments heaps locals agrees actualTyped functionTypes errors.reachable completed

end Head
end Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatements
