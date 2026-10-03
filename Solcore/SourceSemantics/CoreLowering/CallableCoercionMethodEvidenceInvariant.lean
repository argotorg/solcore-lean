import Solcore.SourceSemantics.CoreLowering.CallableCoercionPathMeaning

/-! The concrete builtin body certificate does not inspect a runtime source
dictionary. Its source validity uses only coverage; all retained ledger rows,
source code, actual parameter/frame hooks and saved capture observations are
unchanged. This unit permits a different covering dictionary for the same
source BodyInstance. It does not assert that two selections have that body,
that evidence trees are equal, or that arbitrary bodies ignore evidence. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodEvidenceInvariant
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames CallableCoercionMethodEntries
open CallableCoercionPathMeaning (MethodProfile Profiles)

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {values : ValuesContext} {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment}

/-- A proof-facing closure view, not a mutation of the actual saved closure. -/
def view (method : MethodProfile (prepared := prepared) (values := values) (program := program)
    (context := context) (evidence := evidence)) (dictionary : Dynamic.EvidenceEnvironment) : Dynamic.Closure :=
  {method.function with evidence := dictionary}

/-- Source attribution and roots are preserved in full; only coverage changes. -/
theorem frame (method : MethodProfile (prepared := prepared) (values := values) (program := program)
    (context := context) (evidence := evidence)) (dictionary : Dynamic.EvidenceEnvironment)
    (covers : dictionary.Covers method.sourceBody.context) :
    CallableCoercionMethodFrame.Frame method.sourceBody (view method dictionary) :=
  {method.frame with covers}

private theorem covers_extended {owner : Resolved.DeclarationId}
    {initial final : SourceSemantics.Context} {binders : List TypedBinder} {types : List TypeSystem.Ty}
    {dictionary : Dynamic.EvidenceEnvironment}
    (extension : MonoBindersExtend owner initial binders types final)
    (covers : dictionary.Covers initial) : dictionary.Covers final := by
  have same : final.signatures = initial.signatures := by
    clear covers
    induction extension with
    | nil => rfl
    | cons _ head _ ih => exact ih.trans head.context_fields.1
  simpa only [Dynamic.EvidenceEnvironment.Covers, same, extension.assumptions_eq] using covers

/-- The ordered retained requirement ledger and its validity are unchanged.
Monomorphic binder extension preserves the covered assumptions. -/
theorem valid (method : MethodProfile (prepared := prepared) (values := values) (program := program)
    (context := context) (evidence := evidence)) (dictionary : Dynamic.EvidenceEnvironment)
    (covers : dictionary.Covers method.sourceBody.context) :
    CompatibleExpressionLiterals.ContextValid method.named.specialized.function.solvedRequirements
      method.context dictionary :=
  {method.valid with covers := covers_extended method.extended (method.frame.context.symm ▸ covers)}

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : prepared.layouts.definitions = ambient.definitions)
  (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
  {faults : FunctionCalls.FaultRep} {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {methods : Profiles (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence)}
  (uninitialized : ∀ method ∈ methods, ∀ id location, faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (missing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))

private theorem arguments {method : MethodProfile (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence)}
    {mapping : LocationMap} {world : StoreTyping} {input : Dynamic.Value} {native : Value}
    (represented : ValueRep values.checked registry functions mapping world method.step.source input native method.call.signature.parameterType) :
    Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world method.named.inputs [input] [native] := by
  rw [method.bindings]
  apply Arguments.cons _ Arguments.nil
  change ValueRep _ _ _ _ _ method.input.scheme.body _ _ _
  simpa only [method.inputType] using represented

include extension definitions registered faithful observations runtimeViews uninitialized missing in
/-- An independent body derivation may use any covering dictionary for this
exact source body. The same compiled call and saved capture execute it. No
equality with the actual selected dictionary is required. -/
theorem preserves {method : MethodProfile (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence)}
    (member : method ∈ methods) {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {store : Store} {input : Dynamic.Value} {native : Value}
    (entry : Entry methods ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world method.step.source input native method.call.signature.parameterType)
    {outcome : Dynamic.ExpressionOutcome} (dictionary : Dynamic.EvidenceEnvironment)
    (covers : dictionary.Covers method.sourceBody.context)
    (trace : BodyOutcome program method.sourceBody dictionary before [input] outcome after)
    (reason : Word) :
    ∃ value finalStore finalMap finalWorld,
      CallableCoercionSpine.Invoke caller reason method.call store (.inRight .word native) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        method.step.target method.call.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  obtain ⟨capture⟩ := entry.captures method member
  have parameterEq : method.function.parameters = method.named.inputs.map Prod.fst := by simp only [method.parameters, method.bindings, List.map_cons, List.map_nil]
  have inputEq : method.function.source.inputs = method.named.inputs.map Prod.fst := by simp only [method.inputs, method.bindings, List.map_cons, List.map_nil]
  have parametersCompiled := method.compiled.parametersCompiled
  rw [← method.source] at parametersCompiled
  have reference : (native :: capture.captured)[capture.embedding.lift (prepared.base.globals.length + 1)]? =
      some (.cellRef prepared.ancestry.layout.frame.type entry.frameLocation) := by
    simpa only [Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ] using capture.capturedReference
  obtain ⟨value, finalStore, finalMap, finalWorld, invoked, related, finalHeaps, maps, worlds, frame, metadata, _, _⟩ :=
    CallableCoercionMethodBody.invoke_preserves (prepared := prepared.ancestry) (functions := functions)
      (extension := extension) (program := program) (onError := allocationError) (function := view method dictionary) (certificate := method.certificate)
      (parameters := parameterEq) (inputs := inputEq) (extended := method.extended) (contextValid := valid method dictionary covers)
      (unique := method.unique) (uninitialized := uninitialized method member) (missing := missing method member)
      (faithful := faithful) (functionLeaves := observations) (functionTypes := runtimeViews)
      (acceptedPrefix := parametersCompiled) (definitions := definitions) (registered := registered)
      (acceptedHook := method.compiled.hook) (represented := arguments functions represented)
      (environments := capture.environments) (heaps := heaps) (initialLocals := capture.locals)
      (actualLayout := by
        intro index value found
        exact Core.ReadOnly.EnvironmentsAgree.lift capture.layout native found)
      (actualTyped := .cons represented.runtime_hasType capture.typed)
      (canonicalReference := capture.reference) (actualReference := reference) (unmapped := entry.unmapped)
      (typed := entry.typed) (caller := entry.frame) (snapshots := entry.snapshots) (sourceFrame := frame method dictionary covers)
      rfl rfl rfl capture.installed trace
  exact ⟨value, finalStore, finalMap, finalWorld, invoked, by simpa only [view, method.result, method.signature] using related,
    finalHeaps, maps, worlds, frame, metadata, ⟨entry.extend maps worlds frame metadata⟩⟩

include extension definitions registered faithful observations runtimeViews uninitialized missing in
/-- A completed actual call reflects at any covering dictionary for this exact
body. This does not identify dictionary trees or source method selections. -/
theorem reflects {method : MethodProfile (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence)}
    (member : method ∈ methods) {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before : Dynamic.Heap} {store finalStore : Store} {input : Dynamic.Value} {native value : Value} {reason : Word}
    (entry : Entry methods ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world method.step.source input native method.call.signature.parameterType)
    (dictionary : Dynamic.EvidenceEnvironment)
    (covers : dictionary.Covers method.sourceBody.context)
    (completed : CallableCoercionSpine.Invoke caller reason method.call store (.inRight .word native) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      BodyOutcome program method.sourceBody dictionary before [input] outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        method.step.target method.call.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  obtain ⟨capture⟩ := entry.captures method member
  have parameterEq : method.function.parameters = method.named.inputs.map Prod.fst := by simp only [method.parameters, method.bindings, List.map_cons, List.map_nil]
  have inputEq : method.function.source.inputs = method.named.inputs.map Prod.fst := by simp only [method.inputs, method.bindings, List.map_cons, List.map_nil]
  have parametersCompiled := method.compiled.parametersCompiled
  rw [← method.source] at parametersCompiled
  have reference : (native :: capture.captured)[capture.embedding.lift (prepared.base.globals.length + 1)]? =
      some (.cellRef prepared.ancestry.layout.frame.type entry.frameLocation) := by
    simpa only [Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ] using capture.capturedReference
  obtain ⟨outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, frame, metadata, _, _⟩ :=
    CallableCoercionMethodBody.invoke_reflects (prepared := prepared.ancestry) (functions := functions)
      (extension := extension) (program := program) (onError := allocationError) (function := view method dictionary) (certificate := method.certificate)
      (parameters := parameterEq) (inputs := inputEq) (extended := method.extended) (contextValid := valid method dictionary covers)
      (unique := method.unique) (uninitialized := uninitialized method member) (missing := missing method member)
      (faithful := faithful) (functionLeaves := observations) (functionTypes := runtimeViews)
      (acceptedPrefix := parametersCompiled) (definitions := definitions) (registered := registered)
      (acceptedHook := method.compiled.hook) (represented := arguments functions represented)
      (environments := capture.environments) (heaps := heaps) (initialLocals := capture.locals)
      (actualLayout := by
        intro index value found
        exact Core.ReadOnly.EnvironmentsAgree.lift capture.layout native found)
      (actualTyped := .cons represented.runtime_hasType capture.typed)
      (canonicalReference := capture.reference) (actualReference := reference) (unmapped := entry.unmapped)
      (typed := entry.typed) (caller := entry.frame) (snapshots := entry.snapshots) (sourceFrame := frame method dictionary covers)
      rfl rfl rfl capture.installed completed
  exact ⟨outcome, after, finalMap, finalWorld, trace, by simpa only [view, method.result, method.signature] using related,
    finalHeaps, maps, worlds, frame, metadata, ⟨entry.extend maps worlds frame metadata⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodEvidenceInvariant
