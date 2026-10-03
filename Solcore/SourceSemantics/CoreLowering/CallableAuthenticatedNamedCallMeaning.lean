import Solcore.SourceSemantics.CoreLowering.CallableAuthenticatedNamedCallCertificates
import Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallMeaning

/-! Authenticated expression heads consume the actual emitted call and the
existing bounded argument/body proofs. Tree induction closes children; catalog
mutual meaning closes ordinary callee bodies at every finite grade. Static
profiles and real Entry/capture/history receipts remain separate assumptions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAuthenticatedNamedCallMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup
open CallableCoercionExpressionCertificates CallableCoercionExpressionMeaning
open CallableCoercionRawNamedCallCertificates CallableCoercionRawNamedCallMeaning
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableAuthenticatedNamedCallCertificates

section RawLaws
variable {checked : Checked} {base : Base checked}
  {ancestry : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {compilerProgram : CheckedProgram}
  {headers : Inventory ancestry values ambient.definitions (Program.ofChecked compilerProgram)} {locations : Locations} {capturePrefix : Nat}
  {bodyCompilation : Header ancestry values ambient.definitions (Program.ofChecked compilerProgram) → SourceCoreFunctions.Context}
  {expressionSyntax : Header ancestry values ambient.definitions (Program.ofChecked compilerProgram) → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : ((Program.ofChecked compilerProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (bodyCompilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      ProfileFor diagnosticPolicy headers header (bodyCompilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)


variable {compilation : SourceCoreFunctions.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {reasonAt : ExpressionId → Word} {readFuel fuel : Nat}
  (valid : CompatibleExpressionLiterals.ContextValid compilation.solvedRequirements context evidence)
  (sourceUnique : NodeOccurrencesUnique source)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {project : Projector} {callerFunction : Specialized} {child : SourceCoreEvidence.Child}
  {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
  {instantiation : DeclarationInstantiation} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : Lowered}
  (receipt : Direct compilerProgram project callerFunction compilation child fuel source scope id callee arguments
    instantiation reasonAt policy node output)
  {header : Header ancestry values ambient.definitions (Program.ofChecked compilerProgram)}
  {children : GenericExpressionMeaning.Certificate}
  (certified : RawCall receipt context children (headers := headers) header)
  {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {actualContext : Core.Context}
  {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrative
    scope environment canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (installed : RecursiveNamedCatalog.Entry headers locations capturePrefix compilation.administrativePrefix
    scope mapping world before store canonical)

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles
  certified environments heaps locals agrees actualTyped installed in
/-- Every raw argument/body obligation is supplied by catalog mutual induction.
The only source execution input is the independent original raw-form trace. -/
private theorem raw_preserves_with_children
    (argumentMeaning : ProtectedExpressionMeaning.Preserves
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) (Program.ofChecked compilerProgram)
      context evidence source children faults (protectedEntry headers locations capturePrefix compilation.administrativePrefix)) :
    RawFormPreserves (compilerProgram := compilerProgram) (context := context) (evidence := evidence) (registry := registry)
      functions faults source environment before actual mapping world store node ξ receipt.operand := by
  intro outcome after raw
  have form := receipt.form
  rw [certified.reached.metadata] at form
  have predicates : header.instantiation.predicates = [] := by
    rw [← certified.reached.metadata]
    exact certified.reached.predicates
  obtain ⟨size, trace⟩ := raw_inv form certified.calleeFound predicates certified.evidence raw
  have packed : header.named.signature.parameterType = (SourceCoreCalls.packArguments receipt.loweredArguments).type := by
    rw [← certified.reached.signature]
    exact receipt.native.inputType
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, admin, metadata, _⟩ :=
    RecursiveNamedExpressionHeadBounds.call_preserves_bounded functions certified.sequence certified.nativeTypes packed size
      (fun n _ => RecursiveNamedBoundedContracts.preserves_at_of_unbounded argumentMeaning n)
      (fun n _ => RecursiveNamedCatalogMutualMeaning.preserves_at functions extension faithful observations runtimeViews owners
        uninitialized missing escaped prefixMatches profiles n header certified.reached.member)
      owners certified.reached.member installed environments heaps locals agrees actualTyped trace (Nat.le_refl size)
  refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, admin, metadata⟩
  · simpa only [receipt.native.emitted, certified.reached.signature, certified.reached.slot,
      NamedCalls.Arguments.call_rename] using evaluated
  · simpa only [certified.rawType, receipt.native.emitted, certified.reached.signature, header.resultType] using represented

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles
  certified environments heaps locals agrees actualTyped installed in
/-- Only the actual native completion is measured. Reflection constructs its
independent source trace and never consumes preservation or a source run. -/
private theorem raw_reflects_with_children
    (argumentMeaning : ProtectedExpressionMeaning.Reflects
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) (Program.ofChecked compilerProgram)
      context evidence source children faults (protectedEntry headers locations capturePrefix compilation.administrativePrefix)) :
    RawFormReflects (compilerProgram := compilerProgram) (context := context) (evidence := evidence) (registry := registry)
      functions faults source environment before actual mapping world store node ξ receipt.operand := by
  intro value finalStore completed
  obtain ⟨size, measured⟩ := evaluation_has_size completed
  have packed : header.named.signature.parameterType = (SourceCoreCalls.packArguments receipt.loweredArguments).type := by
    rw [← certified.reached.signature]
    exact receipt.native.inputType
  simp only [receipt.native.emitted, certified.reached.signature, certified.reached.slot,
    NamedCalls.Arguments.call_rename] at measured
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, admin, metadata, _⟩ :=
    RecursiveNamedExpressionHeadBounds.call_reflects_bounded functions certified.sequence certified.nativeTypes packed size
      (fun n _ => RecursiveNamedBoundedContracts.reflects_at_of_unbounded argumentMeaning n)
      (fun n _ => RecursiveNamedCatalogMutualMeaning.reflects_at functions extension faithful observations runtimeViews
        uninitialized missing escaped prefixMatches profiles n header certified.reached.member)
      certified.reached.member installed environments heaps locals agrees actualTyped measured (Nat.le_refl size)
  have form := receipt.form
  rw [certified.reached.metadata] at form
  have produced : Dynamic.DirectCallProducesEvidence context evidence node.requirements node.coercions
      header.instantiation.predicates header.function.evidence := by
    simpa only [certified.reached.metadata, certified.evidence] using certified.dictionary evidence
  refine ⟨outcome, after, finalMap, finalWorld,
    raw_intro form certified.calleeFound certified.calleeForm certified.calleeRequirements certified.calleeCoercions certified.valid produced trace,
    ?_, finalHeaps, maps, worlds, admin, metadata⟩
  simpa only [certified.rawType, receipt.native.emitted, certified.reached.signature, header.resultType] using represented

end RawLaws

section TreeLaws
variable {checked : Checked} {base : Base checked}
  {ancestry : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {compilerProgram : CheckedProgram}
  {headers : Inventory ancestry values ambient.definitions (Program.ofChecked compilerProgram)} {locations : Locations} {capturePrefix : Nat}
  {bodyCompilation : Header ancestry values ambient.definitions (Program.ofChecked compilerProgram) → SourceCoreFunctions.Context}
  {expressionSyntax : Header ancestry values ambient.definitions (Program.ofChecked compilerProgram) → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : ((Program.ofChecked compilerProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (bodyCompilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      ProfileFor diagnosticPolicy headers header (bodyCompilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)


variable {compilation : SourceCoreFunctions.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {reasonAt : ExpressionId → Word} {readFuel fuel : Nat}
  (valid : CompatibleExpressionLiterals.ContextValid compilation.solvedRequirements context evidence)
  (sourceUnique : NodeOccurrencesUnique source)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles sourceUnique in
private theorem head_preserves {children : GenericExpressionMeaning.Certificate}
    (argumentMeaning : ProtectedExpressionMeaning.Preserves
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) (Program.ofChecked compilerProgram)
      context evidence source children faults (protectedEntry headers locations capturePrefix compilation.administrativePrefix)) :
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      (Program.ofChecked compilerProgram) context evidence source
      (CallableAuthenticatedNamedCallCertificates.Head headers compilerProgram compilation source context reasonAt children)
      faults (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
  intro scope id lowered head
  cases head with
  | direct receipt certified metadata sourceType =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees typed installed trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨caller⟩ := installed
    obtain ⟨size, measured⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size trace
    have form := receipt.form
    rw [certified.reached.metadata] at form
    have predicates : _ := certified.reached.predicates
    rw [certified.reached.metadata] at predicates
    have independent := RecursiveNamedArgumentTraceBounds.source_inv metadata form certified.calleeFound predicates certified.evidence sourceUnique measured
    have packed : _ := receipt.native.inputType
    rw [certified.reached.signature] at packed
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preserved, heapMetadata, _⟩ :=
      RecursiveNamedExpressionHeadBounds.call_preserves_bounded functions certified.sequence certified.nativeTypes packed size
        (fun n _ => RecursiveNamedBoundedContracts.preserves_at_of_unbounded argumentMeaning n)
        (fun n _ => RecursiveNamedCatalogMutualMeaning.preserves_at functions extension faithful observations runtimeViews owners
          uninitialized missing escaped prefixMatches profiles n _ certified.reached.member)
        owners certified.reached.member caller environments heaps locals agrees typed independent (Nat.le_refl size)
    have emitted := certified.emitted receipt metadata.coercions
    have outputType := congrArg (fun code : Lowered => code.type) emitted
    refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, preserved, heapMetadata⟩
    · simpa only [emitted, NamedCalls.Arguments.call_rename] using evaluated
    · simpa only [sourceType, outputType] using represented

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles in
private theorem head_reflects {children : GenericExpressionMeaning.Certificate}
    (argumentMeaning : ProtectedExpressionMeaning.Reflects
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) (Program.ofChecked compilerProgram)
      context evidence source children faults (protectedEntry headers locations capturePrefix compilation.administrativePrefix)) :
    ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      (Program.ofChecked compilerProgram) context evidence source
      (CallableAuthenticatedNamedCallCertificates.Head headers compilerProgram compilation source context reasonAt children)
      faults (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
  intro scope id lowered head
  cases head with
  | direct receipt certified metadata sourceType =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees typed installed completed
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨caller⟩ := installed
    obtain ⟨size, measured⟩ := evaluation_has_size completed
    have emitted := certified.emitted receipt metadata.coercions
    have packed : _ := receipt.native.inputType
    rw [certified.reached.signature] at packed
    simp only [emitted, NamedCalls.Arguments.call_rename] at measured
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preserved, heapMetadata, _⟩ :=
      RecursiveNamedExpressionHeadBounds.call_reflects_bounded functions certified.sequence certified.nativeTypes packed size
        (fun n _ => RecursiveNamedBoundedContracts.reflects_at_of_unbounded argumentMeaning n)
        (fun n _ => RecursiveNamedCatalogMutualMeaning.reflects_at functions extension faithful observations runtimeViews
          uninitialized missing escaped prefixMatches profiles n _ certified.reached.member)
        certified.reached.member caller environments heaps locals agrees typed measured (Nat.le_refl size)
    have form := receipt.form
    rw [certified.reached.metadata] at form
    have predicates : _ := certified.reached.predicates
    rw [certified.reached.metadata] at predicates
    obtain ⟨_, independent⟩ := RecursiveNamedArgumentTraceBounds.source_intro metadata form certified.calleeFound
      certified.calleeForm certified.calleeRequirements certified.calleeCoercions certified.valid predicates certified.evidence trace
    have outputType := congrArg (fun code : Lowered => code.type) emitted
    exact ⟨outcome, after, finalMap, finalWorld, independent.sound, by simpa only [sourceType, outputType] using represented,
      finalHeaps, maps, worlds, preserved, heapMetadata⟩

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles valid sourceUnique callerUninitialized callerMissing in
/-- Every child law comes from the generic structural Tree induction. The
ordinary catalog body family is closed by the existing all-grade mutual theorem. -/
theorem preserves :
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      (Program.ofChecked compilerProgram) context evidence source
      (Tree headers compilerProgram compilation readFuel source context reasonAt)
      faults (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
  apply CompatibleExpressionCalls.preserves functions extension faithful observations runtimeViews
    (Program.ofChecked compilerProgram) evidence valid callerUninitialized callerMissing entry_transport sourceUnique
  intro children meaning
  exact head_preserves functions extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles
    sourceUnique meaning

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles valid callerUninitialized callerMissing in
/-- Reflection consumes only the original native completion, reconstructing
independent source grades and the exact first-fault state. -/
theorem reflects :
    ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      (Program.ofChecked compilerProgram) context evidence source
      (Tree headers compilerProgram compilation readFuel source context reasonAt)
      faults (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
  apply CompatibleExpressionCalls.reflects functions extension faithful observations runtimeViews
    (Program.ofChecked compilerProgram) evidence valid callerUninitialized callerMissing entry_transport
  intro children meaning
  exact head_reflects functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles meaning

end TreeLaws

end Solcore.SourceSemantics.CoreLowering.CallableAuthenticatedNamedCallMeaning
