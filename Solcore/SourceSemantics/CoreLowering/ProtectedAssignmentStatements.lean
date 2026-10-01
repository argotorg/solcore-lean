import Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatementCertificates
import Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentReflection

/-! Projected assignment composition consumes a guarded expression meaning contract.
Concrete clients discharge it with their own expression Tree theorem while retaining actual installed observations.
Seven actual temporary values retain post-write typing and closure captures. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedAssignmentStatements
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning

abbrev ValuesContext := SourceCoreCompatibleValues.Context

abbrev Head := GenericAssignmentStatements.Head

namespace Head
variable {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (meaning : ProtectedExpressionMeaning.Preserves (payloadModel values.checked registry functions)
    program context evidence source certificate faults entry)
  (reflection : ProtectedExpressionMeaning.Reflects (payloadModel values.checked registry functions)
    program context evidence source certificate faults entry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : Head values source context certificate scope administrative ambient.definitions assignment operator rhs)
  (projected : head.prepared.steps ≠ [])
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (installed : entry scope mapping world before store canonical)

include projected transport extension meaning faithful observations environments heaps locals agrees actualTyped installed in
theorem preserves_prefix {updated : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before assignment.target rhs updated after) :
    ∃ finalStore finalMap finalWorld slots,
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      entry scope finalMap finalWorld after finalStore canonical ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  cases shape with
  | bare empty layout => exact (projected layout.steps).elim
  | projected layout ordinary =>
    obtain ⟨_, finalStore, finalMap, finalWorld, _, finalHeaps, maps, worlds, frame, metadata, slots, count, typed, continuation⟩ :=
      ProtectedPlaceAssignmentSuccess.preserves_prefix layout ordinary extension transport meaning faithful observations right found rightView rightType profile
        environments heaps locals agrees actualTyped installed slot writable trace invalid
    exact ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, frame, metadata, count, typed, transport.extend installed maps worlds frame metadata, continuation⟩

include projected transport extension meaning faithful observations environments heaps locals agrees actualTyped installed in
theorem preserves_fault (errors : head.Errors registry faults)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target operator rhs reason after)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      entry scope finalMap finalWorld after finalStore canonical := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  cases shape with
  | bare empty layout => exact (projected layout.steps).elim
  | projected layout ordinary =>
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata⟩ :=
      ProtectedPlaceAssignmentFaults.preserves layout ordinary extension transport meaning faithful observations
      errors.missing errors.uninitialized right found rightView rightType profile environments heaps locals agrees actualTyped installed slot writable trace next output invalid
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata,
      transport.extend installed maps worlds frame metadata⟩

include projected transport extension meaning reflection faithful observations environments heaps locals agrees actualTyped installed in
theorem reflects (functionTypes : FunctionRuntimeViews functions) (errors : head.Errors registry faults)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    (completed : Evaluates actual store ((head.emit next output).rename ξ) value finalStore) :
    (∃ reason token after finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target operator rhs reason after ∧
      value = .inLeft output (.word token) ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      entry scope finalMap finalWorld after finalStore canonical) ∨
    (∃ updated after written finalMap finalWorld slots,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before assignment.target rhs updated after ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after written ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap written ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      entry scope finalMap finalWorld after written canonical ∧
      Evaluates (slots ++ actual) written (shift 7 (next.rename ξ)) value finalStore) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  cases shape with
  | bare empty layout => exact (projected layout.steps).elim
  | projected layout ordinary =>
    rcases ProtectedPlaceAssignmentReflection.reflects layout ordinary extension transport reflection meaning functionTypes faithful observations
      errors.missing errors.uninitialized right found rightView rightType profile environments heaps agrees actualTyped installed locals slot writable completed with
      ⟨_, _, _, _, _, trace, same, matched, finalHeaps, maps, worlds, frame, metadata⟩ |
      ⟨_, _, _, _, _, _, trace, finalHeaps, maps, worlds, frame, metadata, count, typed, continuation⟩
    · exact .inl ⟨_, _, _, _, _, trace, same, matched, finalHeaps, maps, worlds, frame, metadata, transport.extend installed maps worlds frame metadata⟩
    · exact .inr ⟨_, _, _, _, _, _, trace, finalHeaps, maps, worlds, frame, metadata, count, typed, transport.extend installed maps worlds frame metadata, continuation⟩
end Head
end Solcore.SourceSemantics.CoreLowering.ProtectedAssignmentStatements
