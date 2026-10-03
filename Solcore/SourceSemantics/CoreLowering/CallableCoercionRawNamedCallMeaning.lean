import Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallCertificates
import Solcore.SourceSemantics.CoreLowering.CallableCoercionExpressionMeaning

/-! Raw ordinary calls retain their original requirement/coercion lists.
Actual argument and callee grades are consumed by the existing bounded call
proof; the catalog mutual theorem closes both meaning families internally.
Source and Core grades are independent. Initial catalog and method authority,
and static profiles at actual body entries, remain explicit. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup
open CallableCoercionExpressionCertificates CallableCoercionExpressionMeaning
open CallableCoercionRawNamedCallCertificates RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds

private theorem dictionary_empty {context : SourceSemantics.Context}
    {caller result : Dynamic.EvidenceEnvironment} {requirements : List RequirementId}
    {coercions : List CoercionStep}
    (produced : Dynamic.DirectCallProducesEvidence context caller requirements coercions [] result) : result = [] := by
  cases produced with
  | intro _ _ produced => simpa using produced.length_eq.2.symm

section RawTrace
variable {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {node calleeNode : ExpressionNode} {callee : ExpressionId} {arguments : List ExpressionId}
  {instantiation : DeclarationInstantiation} {invocation : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}

theorem raw_inv
    (form : node.form = .call callee arguments (.declaration instantiation))
    (found : source.lookupExpression? callee = some calleeNode)
    (predicates : instantiation.predicates = []) (empty : invocation = [])
    (trace : RawOutcome program context evidence source environment before node outcome after) :
    ∃ size, RecursiveNamedArgumentTraceBounds.TraceAt program context evidence invocation source environment before
      arguments instantiation size outcome after := by
  subst invocation
  cases outcome with
  | value value =>
    obtain ⟨size, raw⟩ := SourceExecutionSize.ExpressionFormEvaluates.has_size trace
    refine ⟨size, ?_⟩
    rw [form] at raw
    cases raw with
    | directCall _ _ _ _ _ evaluated produced applied =>
      rw [predicates] at produced
      cases dictionary_empty produced
      exact .apply evaluated (.value applied)
        (SourceExecutionSize.child_lt_stepSize (by simp)) (SourceExecutionSize.child_lt_stepSize (by simp))
  | fault reason =>
    obtain ⟨size, raw⟩ := SourceExecutionSize.ExpressionFormFaults.has_size trace
    refine ⟨size, ?_⟩
    rw [form] at raw
    cases raw with
    | directCalleeMissing absent =>
      exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent (lookupExpression?_sound found))
    | directArguments _ _ failed =>
      exact .argumentFault failed (SourceExecutionSize.child_lt_stepSize (by simp))
    | directRequirements _ failed =>
      rw [predicates] at failed
      have impossible : ∀ ids bad, ¬ Dynamic.RequirementsFault context evidence ids [] bad := by intro ids bad h; cases h
      exact False.elim (impossible _ _ failed)
    | directApply evaluated produced failed =>
      rw [predicates] at produced
      cases dictionary_empty produced
      exact .apply evaluated (.fault failed)
        (SourceExecutionSize.child_lt_stepSize (by simp)) (SourceExecutionSize.child_lt_stepSize (by simp))

theorem raw_intro {name : String} {size : Nat}
    (form : node.form = .call callee arguments (.declaration instantiation))
    (found : source.lookupExpression? callee = some calleeNode)
    (calleeForm : calleeNode.form = .reference name (.declaration instantiation))
    (requirements : calleeNode.requirements = []) (coercions : calleeNode.coercions = [])
    (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation)
    (produced : Dynamic.DirectCallProducesEvidence context evidence node.requirements node.coercions instantiation.predicates invocation)
    (trace : RecursiveNamedArgumentTraceBounds.TraceAt program context evidence invocation source environment before
      arguments instantiation size outcome after) :
    RawOutcome program context evidence source environment before node outcome after := by
  cases trace with
  | argumentFault failed _ =>
    change Dynamic.ExpressionFormFaults _ _ _ _ _ _ _ _ _ _ _
    rw [form]
    exact .directArguments (lookupExpression?_sound found) calleeForm failed.sound
  | apply evaluated called _ _ =>
    cases called with
    | value applied =>
      change Dynamic.ExpressionFormEvaluates _ _ _ _ _ _ _ _ _ _ _
      rw [form]
      exact .directCall (lookupExpression?_sound found) calleeForm requirements coercions valid evaluated.sound produced applied.sound
    | fault failed =>
      change Dynamic.ExpressionFormFaults _ _ _ _ _ _ _ _ _ _ _
      rw [form]
      exact .directApply evaluated.sound produced failed.sound
end RawTrace

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
  (certified : Certificate receipt readFuel context (headers := headers) header)
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

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles valid sourceUnique callerUninitialized callerMissing
  certified environments heaps locals agrees actualTyped installed in
/-- Every raw argument/body obligation is supplied by catalog mutual induction.
The only source execution input is the independent original raw-form trace. -/
theorem raw_preserves :
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
    RecursiveNamedExpressionHeadBounds.call_preserves_bounded functions certified.children certified.nativeTypes packed size
      (fun n _ => RecursiveNamedCatalogMutualMeaning.expression_preserves_at functions extension faithful observations runtimeViews owners
        uninitialized missing escaped prefixMatches profiles evidence valid sourceUnique callerUninitialized callerMissing n)
      (fun n _ => RecursiveNamedCatalogMutualMeaning.preserves_at functions extension faithful observations runtimeViews owners
        uninitialized missing escaped prefixMatches profiles n header certified.reached.member)
      owners certified.reached.member installed environments heaps locals agrees actualTyped trace (Nat.le_refl size)
  refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, admin, metadata⟩
  · simpa only [receipt.native.emitted, certified.reached.signature, certified.reached.slot,
      NamedCalls.Arguments.call_rename] using evaluated
  · simpa only [certified.rawType, receipt.native.emitted, certified.reached.signature, header.resultType] using represented

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles valid callerUninitialized callerMissing
  certified environments heaps locals agrees actualTyped installed in
/-- Only the actual native completion is measured. Reflection constructs its
independent source trace and never consumes preservation or a source run. -/
theorem raw_reflects :
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
    RecursiveNamedExpressionHeadBounds.call_reflects_bounded functions certified.children certified.nativeTypes packed size
      (fun n _ => RecursiveNamedCatalogMutualMeaning.expression_reflects_at functions extension faithful observations runtimeViews
        uninitialized missing escaped prefixMatches profiles evidence valid callerUninitialized callerMissing n)
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

section Outer
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {compilerProgram : CheckedProgram}
  {headers : Inventory prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram)} {locations : Locations} {capturePrefix : Nat}
  {bodyCompilation : Header prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram) → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram) → ExpressionId → Prop}
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
  {header : Header prepared.ancestry values ambient.definitions (Program.ofChecked compilerProgram)}
  (certified : Certificate receipt readFuel context (headers := headers) header)
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

variable {raw : Workspace.RawWorkspace} {checkFuel : Nat}
  (checkedAccepted : checkProgram raw checkFuel = .ok compilerProgram)
  (definitions : prepared.layouts.definitions = ambient.definitions)
  (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
  {methods : CallableCoercionPathMeaning.Profiles (prepared := prepared) (values := values)
    (program := Program.ofChecked compilerProgram) (context := context) (evidence := evidence)}
  (methodUninitialized : ∀ method ∈ methods, ∀ id location,
    faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (methodMissing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
  {calls : List CallableCoercionSpine.Call}
  (emitted : CallableCoercionMethodEntries.Emitted compilerProgram project compilation callerFunction receipt.available
    scope node policy ξ receipt.operand methods output calls)
  (steps : methods.map (·.step) = node.coercions)
  (chain : CallableCoercionPathMeaning.Chain node.rawType receipt.operand.type methods node.type output.type)
  (ledger : context.solvedRequirements = callerFunction.function.solvedRequirements)
  (methodEntry : CallableCoercionMethodEntries.Entry methods ambient.definitions actual mapping world before store)

include checkedAccepted extension definitions registered faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles
  valid sourceUnique callerUninitialized callerMissing certified environments heaps locals agrees actualTyped installed
  methodUninitialized methodMissing emitted steps chain ledger methodEntry in
/-- The final consumer closes raw arguments and recursive ordinary bodies and
then preserves the independent original ordered output path. -/
theorem preserves
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (output.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (CallableCoercionMethodEntries.Entry methods ambient.definitions actual finalMap finalWorld after finalStore) := by
  exact CallableCoercionExpressionMeaning.preserves functions checkedAccepted extension definitions registered faithful observations runtimeViews
    methodUninitialized methodMissing receipt.toOutput emitted steps chain ledger methodEntry sourceUnique
    (by intros; simp [receipt.form])
    (raw_preserves functions extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles
      valid sourceUnique callerUninitialized callerMissing receipt certified environments heaps locals agrees actualTyped installed) trace

include extension definitions registered faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles
  valid callerUninitialized callerMissing certified environments heaps locals agrees actualTyped installed
  methodUninitialized methodMissing emitted steps chain methodEntry in
/-- Original native completion supplies both the raw call and the ordered path
completion. No prior source execution or preservation law is an input. -/
theorem reflects
    {value : Value} {finalStore : Store}
    (completed : Evaluates actual store (output.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (CallableCoercionMethodEntries.Entry methods ambient.definitions actual finalMap finalWorld after finalStore) := by
  exact CallableCoercionExpressionMeaning.reflects functions extension definitions registered faithful observations runtimeViews
    methodUninitialized methodMissing receipt.toOutput emitted steps chain methodEntry
    (raw_reflects functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles
      valid callerUninitialized callerMissing receipt certified environments heaps locals agrees actualTyped installed) completed
end Outer

end Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallMeaning
