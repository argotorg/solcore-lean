import Solcore.SourceSemantics.CoreLowering.GenericAssignmentReachableDiagnostics
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCallMeaning
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatementCertificates
import Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignmentPreservation
import Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignmentReflection
import Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentReflection

/-! A single guarded assignment head covers actual bare and projected layouts.
Source snapshots, latest reads, native typing and seven-slot continuations are
retained together with the original installed global/capture/history authority.
Runtime child meaning belongs to this inner composition interface only. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedAssignmentHeads
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
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (installed : entry scope mapping world before store canonical)

include transport extension meaning faithful observations environments heaps locals agrees actualTyped installed in
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
  | bare empty layout =>
    obtain ⟨_, finalStore, finalMap, finalWorld, slots, _, finalHeaps, maps, worlds, preservation, metadata, count, typed, continuation⟩ :=
      ProtectedBareAssignment.preserves_prefix layout empty extension meaning observations right found rightView rightType profile
        environments heaps locals agrees actualTyped installed slot writable trace invalid
    exact ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, preservation, metadata, count,
      by simpa [GenericAssignmentStatements.Head.writtenContext, CompatibleRenamedPlaceSuccess.writtenContext, CompatibleBareAssignment.writtenContext,
        Prepared.optionalLeaf, SourceCoreCalls.packArguments, layout.sameType] using typed,
      transport.extend installed maps worlds preservation metadata, continuation⟩
  | projected layout ordinary =>
    obtain ⟨_, finalStore, finalMap, finalWorld, _, finalHeaps, maps, worlds, frame, metadata, slots, count, typed, continuation⟩ :=
      ProtectedPlaceAssignmentSuccess.preserves_prefix layout ordinary extension transport meaning faithful observations right found rightView rightType profile
        environments heaps locals agrees actualTyped installed slot writable trace invalid
    exact ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, frame, metadata, count, typed, transport.extend installed maps worlds frame metadata, continuation⟩

include transport extension meaning faithful observations environments heaps locals agrees actualTyped installed in
theorem preserves_fault_reachable (errors : head.ReachableErrors registry faults)
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
  | bare empty layout =>
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata⟩ :=
      ProtectedBareAssignment.preserves_fault_reachable layout empty extension meaning observations right found rightView rightType profile
        environments heaps locals agrees actualTyped installed slot writable trace next output invalid errors.operands
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata,
      transport.extend installed maps worlds preservation metadata⟩
  | projected layout ordinary =>
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata⟩ :=
      ProtectedPlaceAssignmentFaults.preserves layout ordinary extension transport meaning faithful observations
      errors.missing errors.uninitialized right found rightView rightType profile environments heaps locals agrees actualTyped installed slot writable trace next output invalid
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata,
      transport.extend installed maps worlds frame metadata⟩

include transport extension meaning faithful observations environments heaps locals agrees actualTyped installed in
/-- Compatibility entry point retaining the original diagnostic receipt. -/
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
  exact preserves_fault_reachable functions extension program evidence transport meaning faithful observations head
    environments heaps locals agrees actualTyped installed errors.reachable trace next output

include transport extension meaning reflection faithful observations environments heaps locals agrees actualTyped installed in
theorem reflects_reachable (functionTypes : FunctionRuntimeViews functions) (errors : head.ReachableErrors registry faults)
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
  | bare empty layout =>
    have result := ProtectedBareAssignment.reflects_reachable layout empty extension reflection observations right found rightView rightType profile
      environments heaps locals agrees actualTyped installed slot writable errors.operands completed
    cases result with
    | fault trace same matched finalHeaps maps worlds preservation metadata =>
      exact .inl ⟨_, _, _, _, _, trace, same, matched, finalHeaps, maps, worlds, preservation, metadata,
        transport.extend installed maps worlds preservation metadata⟩
    | success trace _ finalHeaps maps worlds preservation metadata count typed continuation =>
      exact .inr ⟨_, _, _, _, _, _, trace, finalHeaps, maps, worlds, preservation, metadata, count,
        by simpa [GenericAssignmentStatements.Head.writtenContext, CompatibleRenamedPlaceSuccess.writtenContext, CompatibleBareAssignment.writtenContext,
          Prepared.optionalLeaf, SourceCoreCalls.packArguments, layout.sameType] using typed,
        transport.extend installed maps worlds preservation metadata, continuation⟩
  | projected layout ordinary =>
    rcases ProtectedPlaceAssignmentReflection.reflects layout ordinary extension transport reflection meaning functionTypes faithful observations
      errors.missing errors.uninitialized right found rightView rightType profile environments heaps agrees actualTyped installed locals slot writable completed with
      ⟨_, _, _, _, _, trace, same, matched, finalHeaps, maps, worlds, frame, metadata⟩ |
      ⟨_, _, _, _, _, _, trace, finalHeaps, maps, worlds, frame, metadata, count, typed, continuation⟩
    · exact .inl ⟨_, _, _, _, _, trace, same, matched, finalHeaps, maps, worlds, frame, metadata, transport.extend installed maps worlds frame metadata⟩
    · exact .inr ⟨_, _, _, _, _, _, trace, finalHeaps, maps, worlds, frame, metadata, count, typed, transport.extend installed maps worlds frame metadata, continuation⟩

include transport extension meaning reflection faithful observations environments heaps locals agrees actualTyped installed in
/-- Compatibility entry point retaining the original diagnostic receipt. -/
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
  exact reflects_reachable functions extension program evidence transport meaning reflection faithful observations head
    environments heaps locals agrees actualTyped installed functionTypes errors.reachable completed

end Head
end Solcore.SourceSemantics.CoreLowering.ProtectedAssignmentHeads

namespace Solcore.SourceSemantics.CoreLowering.NamedAssignmentHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning CallableAncestryPairedLookup
abbrev ValuesContext := SourceCoreCompatibleValues.Context

/-! Concrete named argument/body trees close the only guarded RHS meaning
interface. Both empty and nonempty projection paths retain real installed
observations; no execution is added to a static assignment Head. -/
variable {checked : CallableAncestryPairedLookup.Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {source : TypedSource} {program : Program}
  {context : SourceSemantics.Context} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head values source context
    (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt) scope administrative ambient.definitions assignment operator rhs)
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope mapping world before store canonical)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (runtimeViews : FunctionRuntimeViews functions)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))


include extension faithful observations environments heaps locals agrees actualTyped installed valid unique owners runtimeViews
  uninitialized missing bodyUninitialized bodyMissing in
theorem preserves_prefix {updated : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before assignment.target rhs updated after) :
    ∃ finalStore finalMap finalWorld slots,
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope finalMap finalWorld after finalStore canonical ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  exact ProtectedAssignmentHeads.Head.preserves_prefix functions extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
      uninitialized missing bodyUninitialized bodyMissing unique owners) faithful observations head environments heaps locals agrees actualTyped installed trace

include extension faithful observations environments heaps locals agrees actualTyped installed valid unique owners runtimeViews
  uninitialized missing bodyUninitialized bodyMissing in
theorem preserves_fault_reachable (errors : head.ReachableErrors registry faults)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target operator rhs reason after)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope finalMap finalWorld after finalStore canonical := by
  exact ProtectedAssignmentHeads.Head.preserves_fault_reachable functions extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
      uninitialized missing bodyUninitialized bodyMissing unique owners) faithful observations head environments heaps locals agrees actualTyped installed errors trace next output

include extension faithful observations environments heaps locals agrees actualTyped installed valid unique owners runtimeViews
  uninitialized missing bodyUninitialized bodyMissing in
/-- Compatibility entry point retaining the original diagnostic receipt. -/
theorem preserves_fault (errors : head.Errors registry faults)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target operator rhs reason after)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope finalMap finalWorld after finalStore canonical := by
  exact preserves_fault_reachable functions extension evidence faithful observations head environments heaps locals agrees actualTyped installed
    valid unique owners runtimeViews uninitialized missing bodyUninitialized bodyMissing errors.reachable trace next output

include extension faithful observations environments heaps locals agrees actualTyped installed valid unique owners runtimeViews
  uninitialized missing bodyUninitialized bodyMissing in
theorem reflects_reachable (errors : head.ReachableErrors registry faults)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    (completed : Evaluates actual store ((head.emit next output).rename ξ) value finalStore) :
    (∃ reason token after finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target operator rhs reason after ∧
      value = .inLeft output (.word token) ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope finalMap finalWorld after finalStore canonical) ∨
    (∃ updated after written finalMap finalWorld slots,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before assignment.target rhs updated after ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after written ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap written ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope finalMap finalWorld after written canonical ∧
      Evaluates (slots ++ actual) written (shift 7 (next.rename ξ)) value finalStore) := by
  exact ProtectedAssignmentHeads.Head.reflects_reachable functions extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    (NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence valid
      uninitialized missing bodyUninitialized bodyMissing) faithful observations head environments heaps locals agrees actualTyped installed runtimeViews errors completed

include extension faithful observations environments heaps locals agrees actualTyped installed valid unique owners runtimeViews
  uninitialized missing bodyUninitialized bodyMissing in
/-- Compatibility entry point retaining the original diagnostic receipt. -/
theorem reflects (errors : head.Errors registry faults)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    (completed : Evaluates actual store ((head.emit next output).rename ξ) value finalStore) :
    (∃ reason token after finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target operator rhs reason after ∧
      value = .inLeft output (.word token) ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope finalMap finalWorld after finalStore canonical) ∨
    (∃ updated after written finalMap finalWorld slots,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before assignment.target rhs updated after ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after written ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap written ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope finalMap finalWorld after written canonical ∧
      Evaluates (slots ++ actual) written (shift 7 (next.rename ξ)) value finalStore) := by
  exact reflects_reachable functions extension evidence faithful observations head environments heaps locals agrees actualTyped installed
    valid unique owners runtimeViews uninitialized missing bodyUninitialized bodyMissing errors.reachable completed

end Solcore.SourceSemantics.CoreLowering.NamedAssignmentHeads
