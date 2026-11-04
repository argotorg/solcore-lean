import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallBounds
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.AssignmentContracts
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTupleCertificates
import Solcore.SourceSemantics.CoreLowering.ProtectedStatePlaceAssignment
import Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionSequenceProducer
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCallTree
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCallMeaning
import Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionReady
import Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionOperandTyping

/-!
# Recursive named rows: expression heads

Head bounds of expressions, tuples and data expressions, with their Source bounds.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionHeadBounds
/-! Bounded ordinary named heads combine the actual ordered argument trace and
retained callee envelope. Child obligations are chosen only below the original
source or native cost. This leaf interface does not close the whole expression
and called-body grammar. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedParameterCertificates RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
abbrev Scope := SourceCoreLocalCell.Scope
abbrev Below := RecursiveNamedBoundedContracts.Below

private theorem values_arguments {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} (bindings : List Binding)
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values model mapping world
      (bindings.map (fun binding => binding.1.scheme.body)) (bindings.map Prod.snd) sources payloads) :
    CallableIndexedParameterMeaning.Arguments model mapping world bindings sources payloads := by
  induction bindings generalizing sources payloads with
  | nil => cases represented; exact .nil
  | cons binding rest ih => cases represented with
    | cons head tail => exact .cons head (ih tail)

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {capturePrefix callerPrefix : Nat}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {faults : FunctionCalls.FaultRep}
  {header : Header prepared values ambient.definitions program}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : Scope} {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr}
  {certificate : GenericExpressionMeaning.Certificate}
  (children : DataExpressionSequence.Tree source certificate scope ids
    (header.bindings.map (fun binding => binding.1.scheme.body)) codes)
  (nativeTypes : codes.map (·.type) = header.bindings.map Prod.snd)
  (packedType : header.named.signature.parameterType = (SourceCoreCalls.packArguments codes).type)

include functions children nativeTypes packedType in
theorem call_preserves_bounded_for (P : ProtectedExpressionMeaning.Entry)
    (transport : ProtectedExpressionMeaning.Transport P)
    (condition : BodyCondition (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header)
    (authorized : BodyAuthorization (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header condition)
    (budget : Nat)
    (argumentMeaning : Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      P))
    (bodyMeaning : Below budget (BodyPreservesAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
      functions registry header faults condition))
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (member : header ∈ headers)
    {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
    {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    (caller : Entry headers locations capturePrefix callerPrefix scope mapping world before store canonical)
    (callerP : P scope mapping world before store canonical)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {size : Nat} {reason : Word} {outcome : Dynamic.ExpressionOutcome}
    (trace : RecursiveNamedArgumentTraceBounds.TraceAt program context evidence header.function.evidence source environment before ids
      header.instantiation size outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (SourceCoreCalls.call header.named.signature (ξ (scope.length + callerPrefix + header.slot))
        ((SourceCoreCalls.packArguments codes).expression.rename ξ) reason) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      P scope finalMap finalWorld after finalStore canonical := by
  have argumentsMeaning : ∀ child, child < budget → ProtectedDataExpressionSequence.ExpressionPreservesAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      P := by
    intro child smaller
    exact RecursiveNamedPlaceKeyContracts.preserves_at (argumentMeaning child smaller)
  cases trace with
  | argumentFault failed smaller =>
    obtain ⟨token, finalStore, finalMap, finalWorld, argumentEvaluation, matched, finalHeaps, maps, worlds, frame, metadata⟩ :=
      ProtectedDataExpressionSequence.preserves_fault_bounded transport budget children argumentsMeaning environments heaps locals agrees typed
        callerP failed (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller within))
    refine ⟨_, finalStore, finalMap, finalWorld, SourceCoreCalls.call_argument_failure (packedType.symm ▸ argumentEvaluation),
      (by simpa only [header.resultType] using (FunctionCalls.ResultRepresents.fault (model := CompatibleAmbientHeap.payloadModel values.checked registry functions) (mapping := finalMap) (world := finalWorld) (sourceType := header.function.resultType) (type := header.named.signature.resultType) matched)), finalHeaps, maps, worlds, frame, metadata,
      transport.extend callerP maps worlds frame metadata⟩
  | @apply argumentsSize callSize arguments middle outcome after evaluated called argumentsSmaller callSmaller =>
    obtain ⟨payloads, middleStore, middleMap, middleWorld, argumentEvaluation, represented, middleHeaps, argumentMaps, argumentWorlds,
      argumentFrame, argumentMetadata⟩ :=
      ProtectedDataExpressionSequence.preserves_values_bounded transport budget children argumentsMeaning environments heaps locals agrees typed
        callerP evaluated (Nat.le_of_lt (Nat.lt_of_lt_of_le argumentsSmaller within))
    rw [nativeTypes] at represented
    have related := values_arguments header.bindings represented
    have arity : header.function.parameters.length = arguments.length := by rw [header.parameters, List.length_map]; exact related.length.1
    obtain ⟨bodySize, bodyTrace, bodySmaller⟩ := RecursiveNamedCallBounds.source_call_body owners header.frame arity called
    let next := caller.extend argumentMaps argumentWorlds argumentFrame argumentMetadata
    obtain ⟨capture, value, finalStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps, bodyMaps, bodyWorlds, bodyFrame,
      bodyMetadata, _finalEntry⟩ := invocation_preserves_bounded_with condition authorized budget bodyMeaning next member related middleHeaps bodyTrace
      (Nat.le_of_lt (Nat.lt_trans bodySmaller (Nat.lt_of_lt_of_le callSmaller within)))
    have selected := OptionalCell.read_success reason
      (show Evaluates (DataPatternValues.packValues payloads :: actual) middleStore
        (.var (ξ (scope.length + callerPrefix + header.slot) + 1))
        (.cellRef (OptionalCell.cellType header.named.signature.functionType) (locations header)) middleStore
        from .var (agrees (caller.globals header member))) capture.read
    exact ⟨value, finalStore, finalMap, finalWorld, SourceCoreCalls.call_success argumentEvaluation selected bodyEvaluation,
      result, finalHeaps, argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds, argumentFrame.trans bodyFrame,
      argumentMetadata.trans bodyMetadata,
      transport.extend callerP (argumentMaps.trans bodyMaps) (argumentWorlds.trans bodyWorlds) (argumentFrame.trans bodyFrame) (argumentMetadata.trans bodyMetadata)⟩

include functions children nativeTypes packedType in
theorem call_preserves_bounded (budget : Nat)
    (argumentMeaning : Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      (protectedEntry headers locations capturePrefix callerPrefix)))
    (bodyMeaning : Below budget (BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
      functions registry header faults))
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (member : header ∈ headers)
    {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
    {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    (caller : Entry headers locations capturePrefix callerPrefix scope mapping world before store canonical)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {size : Nat} {reason : Word} {outcome : Dynamic.ExpressionOutcome}
    (trace : RecursiveNamedArgumentTraceBounds.TraceAt program context evidence header.function.evidence source environment before ids
      header.instantiation size outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (SourceCoreCalls.call header.named.signature (ξ (scope.length + callerPrefix + header.slot))
        ((SourceCoreCalls.packArguments codes).expression.rename ξ) reason) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact call_preserves_bounded_for functions children nativeTypes packedType _ entry_transport (fun _ => True)
    (by unfold BodyAuthorization; intros; trivial) budget argumentMeaning
    (by
      intro child smaller arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry result after _ trace
      exact bodyMeaning child smaller entry trace) owners member caller ⟨caller⟩ environments heaps locals agrees typed trace within


include functions children nativeTypes packedType in
theorem call_reflects_bounded_for (P : ProtectedExpressionMeaning.Entry)
    (transport : ProtectedExpressionMeaning.Transport P)
    (condition : BodyCondition (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header)
    (authorized : BodyAuthorization (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header condition)
    (budget : Nat)
    (argumentMeaning : Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      P))
    (bodyMeaning : Below budget (BodyReflectsAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
      functions registry header faults condition))
    (member : header ∈ headers)
    {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    (caller : Entry headers locations capturePrefix callerPrefix scope mapping world before store canonical)
    (callerP : P scope mapping world before store canonical)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {size : Nat} {reason : Word}
    (completed : EvaluationSize size actual store (SourceCoreCalls.call header.named.signature (ξ (scope.length + callerPrefix + header.slot))
      ((SourceCoreCalls.packArguments codes).expression.rename ξ) reason) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedArgumentTraceBounds.TraceAt program context evidence header.function.evidence source environment before ids
        header.instantiation sourceSize outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      P scope finalMap finalWorld after finalStore canonical := by
  have argumentsMeaning : ∀ child, child < budget → ProtectedDataExpressionSequence.ExpressionReflectsAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      P := by
    intro child smaller
    exact RecursiveNamedPlaceKeyContracts.reflects_at (argumentMeaning child smaller)
  obtain ⟨argumentSize, argumentValue, middleStore, argumentSmaller, argumentEvaluation⟩ := RecursiveNamedCallBounds.call_arguments completed
  obtain ⟨sourceSize, argumentOutcome, middle, middleMap, middleWorld, argumentTrace, represented, middleHeaps,
    argumentMaps, argumentWorlds, argumentFrame, argumentMetadata⟩ :=
    ProtectedDataExpressionSequence.reflects_bounded transport budget children argumentsMeaning environments heaps locals agrees typed
      callerP argumentEvaluation (Nat.lt_of_lt_of_le argumentSmaller within)
  cases represented with
  | fault matched =>
    cases argumentTrace with
    | fault failed =>
      have evaluation := SourceCoreCalls.call_argument_failure (signature := header.named.signature)
        (index := ξ (scope.length + callerPrefix + header.slot)) (internalReason := reason) (packedType.symm ▸ argumentEvaluation.sound)
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound evaluation
      exact ⟨SourceExecutionSize.stepSize [sourceSize], .fault _, middle, middleMap, middleWorld,
        .argumentFault failed (SourceExecutionSize.child_lt_stepSize (by simp)), (by simpa only [header.resultType] using (FunctionCalls.ResultRepresents.fault (model := CompatibleAmbientHeap.payloadModel values.checked registry functions) (mapping := middleMap) (world := middleWorld) (sourceType := header.function.resultType) (type := header.named.signature.resultType) matched)),
        middleHeaps, argumentMaps, argumentWorlds, argumentFrame, argumentMetadata,
        transport.extend callerP argumentMaps argumentWorlds argumentFrame argumentMetadata⟩
  | values represented =>
    cases argumentTrace with
    | values evaluatedArguments =>
      rw [nativeTypes] at represented
      have related := values_arguments header.bindings represented
      let next := caller.extend argumentMaps argumentWorlds argumentFrame argumentMetadata
      obtain ⟨capture⟩ := next.authority.captures header member
      obtain ⟨bodyNativeSize, bodySmaller, bodyEvaluation⟩ := RecursiveNamedCallBounds.call_body
        argumentEvaluation.sound (agrees (caller.globals header member)) capture.read completed
      obtain ⟨bodySourceSize, outcome, after, finalMap, finalWorld, bodyTrace, result, finalHeaps, bodyMaps, bodyWorlds, bodyFrame,
        bodyMetadata, _finalEntry⟩ := invocation_reflects_bounded_with condition authorized budget bodyMeaning next member related middleHeaps capture bodyEvaluation
        (Nat.le_of_lt (Nat.lt_of_lt_of_le bodySmaller within))
      have called := RecursiveNamedCallBounds.call_of_body (context := context) (caller := evidence) header.frame bodyTrace
      refine ⟨SourceExecutionSize.stepSize [sourceSize, SourceExecutionSize.stepSize [bodySourceSize]], outcome, after, finalMap, finalWorld,
        .apply evaluatedArguments called (SourceExecutionSize.child_lt_stepSize (by simp))
          (SourceExecutionSize.child_lt_stepSize (by simp)), result, finalHeaps,
        argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds, argumentFrame.trans bodyFrame,
        argumentMetadata.trans bodyMetadata,
      transport.extend callerP (argumentMaps.trans bodyMaps) (argumentWorlds.trans bodyWorlds) (argumentFrame.trans bodyFrame) (argumentMetadata.trans bodyMetadata)⟩

include functions children nativeTypes packedType in
theorem call_reflects_bounded (budget : Nat)
    (argumentMeaning : Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      (protectedEntry headers locations capturePrefix callerPrefix)))
    (bodyMeaning : Below budget (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
      functions registry header faults))
    (member : header ∈ headers)
    {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    (caller : Entry headers locations capturePrefix callerPrefix scope mapping world before store canonical)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {size : Nat} {reason : Word}
    (completed : EvaluationSize size actual store (SourceCoreCalls.call header.named.signature (ξ (scope.length + callerPrefix + header.slot))
      ((SourceCoreCalls.packArguments codes).expression.rename ξ) reason) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedArgumentTraceBounds.TraceAt program context evidence header.function.evidence source environment before ids
        header.instantiation sourceSize outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact call_reflects_bounded_for functions children nativeTypes packedType _ entry_transport (fun _ => True)
    (by unfold BodyAuthorization; intros; trivial) budget argumentMeaning
    (by
      intro child smaller arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry result after _ trace
      exact bodyMeaning child smaller entry trace) member caller ⟨caller⟩ environments heaps locals agrees typed completed within


variable {compilation : SourceCoreFunctions.Context}

/-- A pointwise expression theorem at the existing static named head. The
argument and body obligations are internal smaller-trace contracts. -/
theorem preserves_at_for (P : ProtectedExpressionMeaning.Entry)
    (transport : ProtectedExpressionMeaning.Transport P)
    (catalog : ∀ {scope mapping world heap store canonical}, P scope mapping world heap store canonical →
      protectedEntry headers locations capturePrefix compilation.administrativePrefix scope mapping world heap store canonical)
    (conditions : ∀ header, BodyCondition (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header)
    (authorized : ∀ header, header ∈ headers → BodyAuthorization (headers := headers) (locations := locations)
      (capturePrefix := capturePrefix) functions registry header (conditions header))
    (budget size : Nat) (within : size ≤ budget)
    (unique : NodeOccurrencesUnique source)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (argumentMeaning : Below budget (fun child => RecursiveNamedBoundedContracts.PreservesAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      P))
    (bodyMeaning : ∀ header, header ∈ headers → Below budget
      (BodyPreservesAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults (conditions header))) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (RecursiveNamedCatalog.Head headers compilation source context certificate) faults
      P := by
  intro scope id lowered head
  cases head with
  | @named callee arguments header node calleeNode name codes expression member metadata sourceType form calleeFound calleeForm
      calleeRequirements calleeCoercions valid predicates evidenceEmpty arity emission selectedSlot sequence nativeTypes =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees typed installed trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨caller⟩ := catalog installed
    have independent := RecursiveNamedArgumentTraceBounds.source_inv metadata form calleeFound predicates evidenceEmpty unique trace
    obtain ⟨emitted, packed, target, selected⟩ := emission.equation
    change expression = _ at emitted
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preserved, heapMetadata, _⟩ :=
      call_preserves_bounded_for functions sequence nativeTypes packed P transport (conditions header) (authorized header member) budget argumentMeaning (bodyMeaning header member) owners member
        caller installed environments heaps locals agrees typed independent within
    refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, preserved, heapMetadata⟩
    · change Evaluates actual store (expression.rename ξ) value finalStore
      rw [emitted, NamedCalls.Arguments.call_rename, selectedSlot]
      exact evaluated
    · simpa only [sourceType] using represented

theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (unique : NodeOccurrencesUnique source)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (argumentMeaning : Below budget (fun child => RecursiveNamedBoundedContracts.PreservesAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix)))
    (bodyMeaning : ∀ header, header ∈ headers → Below budget
      (BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (RecursiveNamedCatalog.Head headers compilation source context certificate) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  preserves_at_for functions _ entry_transport (fun entry => entry) (fun _ => fun {_ _ _ _ _ _ _ _ _ _ _ _} _ => True)
    (fun _ _ => by unfold BodyAuthorization; intros; trivial) budget size within unique owners argumentMeaning
    (by
      intro header member child smaller arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry result after _ trace
      exact bodyMeaning header member child smaller entry trace)

/-- Whole original native completion reconstructs a separately measured source
expression. No source trace is an input to this reflection theorem. -/
theorem reflects_at_for (P : ProtectedExpressionMeaning.Entry)
    (transport : ProtectedExpressionMeaning.Transport P)
    (catalog : ∀ {scope mapping world heap store canonical}, P scope mapping world heap store canonical →
      protectedEntry headers locations capturePrefix compilation.administrativePrefix scope mapping world heap store canonical)
    (conditions : ∀ header, BodyCondition (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header)
    (authorized : ∀ header, header ∈ headers → BodyAuthorization (headers := headers) (locations := locations)
      (capturePrefix := capturePrefix) functions registry header (conditions header))
    (budget size : Nat) (within : size ≤ budget)
    (argumentMeaning : Below budget (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      P))
    (bodyMeaning : ∀ header, header ∈ headers → Below budget
      (BodyReflectsAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults (conditions header))) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (RecursiveNamedCatalog.Head headers compilation source context certificate) faults
      P := by
  intro scope id lowered head
  cases head with
  | @named callee arguments header node calleeNode name codes expression member metadata sourceType form calleeFound calleeForm
      calleeRequirements calleeCoercions valid predicates evidenceEmpty arity emission selectedSlot sequence nativeTypes =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees typed installed evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨caller⟩ := catalog installed
    obtain ⟨emitted, packed, target, selected⟩ := emission.equation
    change expression = _ at emitted
    change EvaluationSize size actual store (expression.rename ξ) value finalStore at evaluated
    rw [emitted, NamedCalls.Arguments.call_rename, selectedSlot] at evaluated
    obtain ⟨traceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preserved, heapMetadata, _⟩ :=
      call_reflects_bounded_for functions sequence nativeTypes packed P transport (conditions header) (authorized header member) budget argumentMeaning (bodyMeaning header member) member
        caller installed environments heaps locals agrees typed evaluated within
    obtain ⟨sourceSize, independent⟩ := RecursiveNamedArgumentTraceBounds.source_intro metadata form calleeFound calleeForm
      calleeRequirements calleeCoercions valid predicates evidenceEmpty trace
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, independent, by simpa only [sourceType] using represented,
      finalHeaps, maps, worlds, preserved, heapMetadata⟩

theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (argumentMeaning : Below budget (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix)))
    (bodyMeaning : ∀ header, header ∈ headers → Below budget
      (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (RecursiveNamedCatalog.Head headers compilation source context certificate) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) :=
  reflects_at_for functions _ entry_transport (fun entry => entry) (fun _ => fun {_ _ _ _ _ _ _ _ _ _ _ _} _ => True)
    (fun _ _ => by unfold BodyAuthorization; intros; trivial) budget size within argumentMeaning
    (by
      intro header member child smaller arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry result after _ trace
      exact bodyMeaning header member child smaller entry trace)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionHeadBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedTupleHeadBounds
/-! Pointwise finite tuple correspondence consumes the original sequence trace
and original native children. The source cost reconstructed by reflection is
independent of its native cost. Ordered child effects retain the caller entry. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedTupleHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CompatibleExpressionTuples RecursiveNamedCallBounds RecursiveNamedBoundedContracts

variable {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {children : GenericExpressionMeaning.Certificate} {faults : FunctionCalls.FaultRep}

namespace Stateful
universe u v
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)

/-- The original tuple Source proof consumes one real whole-sequence
producer; no child admission is erased to arbitrary sequence input. -/
theorem preserves_after_sequence_bounded (budget size : Nat) (within : size ≤ budget)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {ids : List ExpressionId} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (receipt : Header values source id node ids types codes)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (sequence : ProtectedStateExpressionSequenceProducer.Preserves
      (program := program) (context := context) (evidence := evidence) (source := source)
      (environment := environment) (actual := actual) (ξ := ξ) (ids := ids) (sourceTypes := types)
      (codes := codes) (faults := faults) (CompatibleAmbientHeap.payloadModel values.checked registry functions) initial (budget + 1))
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (sequenceSize : Nat) {sourceOutcome : DataExpressionSequence.Outcome}
    (sourceTrace : ProtectedDataExpressionSequence.TraceAt program sequenceSize context evidence source environment before ids sourceOutcome after)
    (packed : CompatibleExpressionProducts.PacksOutcome sourceOutcome outcome)
    (sequenceSmaller : sequenceSize < size) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type (SourceCoreCalls.packArguments codes).type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
    sequence sourceTrace (by omega)
  obtain ⟨actualOutcome, actualPacked, payload⟩ := sequence_result represented
  have sameOutcome := actualPacked.functional packed
  subst outcome
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated,
    by simpa only [receipt.sourceType] using payload, finalHeaps, maps, worlds, frame, metadata, transition⟩

theorem preserves_bounded_with_sequence (budget size : Nat) (within : size ≤ budget)
    (unique : NodeOccurrencesUnique source)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {ids : List ExpressionId} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (receipt : Header values source id node ids types codes)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (sequence : ProtectedStateExpressionSequenceProducer.Preserves
      (program := program) (context := context) (evidence := evidence) (source := source)
      (environment := environment) (actual := actual) (ξ := ξ) (ids := ids) (sourceTypes := types)
      (codes := codes) (faults := faults) (CompatibleAmbientHeap.payloadModel values.checked registry functions) initial (budget + 1))
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : ExpressionOutcome program size context evidence source environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type (SourceCoreCalls.packArguments codes).type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sequenceSize, sourceOutcome, sourceTrace, packed, sequenceSmaller⟩ :=
    source_inv_at receipt.metadata receipt.form unique trace
  exact preserves_after_sequence_bounded functions program evidence protocol budget size within receipt initial
    sequence sequenceSize sourceTrace packed sequenceSmaller

/-- Reflection retains the sequence's exact reached state and original
native strict budget, then reconstructs an independent whole Source grade. -/
theorem reflects_bounded_with_sequence (budget size : Nat) (within : size ≤ budget)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {ids : List ExpressionId} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (receipt : Header values source id node ids types codes)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (sequence : ProtectedStateExpressionSequenceProducer.Reflects
      (program := program) (context := context) (evidence := evidence) (source := source)
      (environment := environment) (actual := actual) (ξ := ξ) (ids := ids) (sourceTypes := types)
      (codes := codes) (faults := faults) (CompatibleAmbientHeap.payloadModel values.checked registry functions) initial (budget + 1))
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type (SourceCoreCalls.packArguments codes).type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sequenceSize, sourceOutcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
    sequence evaluated (by omega)
  obtain ⟨outcome, packed, payload⟩ := sequence_result represented
  have trace := source_intro receipt.metadata receipt.form sourceTrace.sound packed
  obtain ⟨sourceSize, measured⟩ := ExpressionOutcome.has_size trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, measured,
    by simpa only [receipt.sourceType] using payload, finalHeaps, maps, worlds, frame, metadata, transition⟩

theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (unique : NodeOccurrencesUnique source)
    (meaning : ∀ childSize, childSize ≤ budget → ProtectedStateTransition.PreservesAt protocol
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source children faults childSize) :
    ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate values source children) faults size := by
  intro scope id lowered certified
  obtain ⟨node, ids, types, codes, emitted, receipt, sequence⟩ := certified
  subst lowered
  intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped installed trace
  have same := Option.some.inj (receipt.metadata.found.symm.trans found)
  subst root
  obtain ⟨sequenceSize, sourceOutcome, sourceTrace, packed, sequenceSmaller⟩ :=
    source_inv_at receipt.metadata receipt.form unique trace
  exact preserves_after_sequence_bounded functions program evidence protocol budget size within receipt installed
    (ProtectedStateExpressionSequenceProducer.Preserves.of_uniform installed (budget + 1) sequence
      (fun n bound => ProtectedStateTransition.SequenceBridge.preserves_at protocol (meaning n (by omega)))
      environments heaps locals agrees actualTyped) sequenceSize sourceTrace packed sequenceSmaller

theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → ProtectedStateTransition.ReflectsAt protocol
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source children faults childSize) :
    ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate values source children) faults size := by
  intro scope id lowered certified
  obtain ⟨node, ids, types, codes, emitted, receipt, sequence⟩ := certified
  subst lowered
  intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped installed evaluated
  have same := Option.some.inj (receipt.metadata.found.symm.trans found)
  subst root
  exact reflects_bounded_with_sequence functions program evidence protocol budget size within receipt installed
    (ProtectedStateExpressionSequenceProducer.Reflects.of_uniform installed (budget + 1) sequence
      (fun n bound => ProtectedStateTransition.SequenceBridge.reflects_at protocol (meaning n (by omega)))
      environments heaps locals agrees actualTyped) evaluated

end Stateful

variable {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
include transport

theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (unique : NodeOccurrencesUnique source)
    (meaning : ∀ childSize, childSize ≤ budget → PreservesAt childSize
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source children faults entry) :
    PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate values source children) faults entry := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped installedEntry trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.preserves_at functions program evidence (ProtectedStatePlaceAssignment.legacyProtocol entry) budget size within unique
      (fun child bound => ProtectedStatePlaceAssignment.legacy_preserves transport (meaning child bound))
      certified found environments heaps locals agrees actualTyped (PLift.up installedEntry) trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → ReflectsAt childSize
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source children faults entry) :
    ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate values source children) faults entry := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped installedEntry evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.reflects_at functions program evidence (ProtectedStatePlaceAssignment.legacyProtocol entry) budget size within
      (fun child bound => ProtectedStatePlaceAssignment.legacy_reflects transport (meaning child bound))
      certified found environments heaps locals agrees actualTyped (PLift.up installedEntry) evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedTupleHeadBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedDataExpressionSourceBounds
/-! Original constructor arguments and member/index operands retain their
source costs and order. The mapping terminal remains the existing independent
lookup/default judgment; it adds no expression child or body execution law. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedDataExpressionSourceBounds
open Core Frontend SourceInference GeneralHeap CompatiblePayload CoreProof
open CompatibleExpressionPrimitives CompatibleExpressionMembers CompatibleExpressionIndices
open RecursiveNamedCallBounds RecursiveNamedExpressionSourceBounds

variable {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {id : ExpressionId}
  {node : ExpressionNode} {type : Ty} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {outcome : Dynamic.ExpressionOutcome} {size : Nat}

theorem constructor_inv {instantiation : DataConstructorInstantiation} {arguments : List ExpressionId} (metadata : Metadata checked source id node type)
    (form : node.form = .constructor instantiation arguments) (unique : NodeOccurrencesUnique source)
    (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
    (trace : ExpressionOutcome program size context evidence source environment before id outcome after) :
    ∃ child sequence, ProtectedDataExpressionSequence.TraceAt program child context evidence source environment before arguments sequence after ∧
      CompatibleExpressionConstructors.PacksOutcome instantiation sequence outcome ∧ child < size := by
  cases trace with
  | value evaluated =>
    obtain ⟨_, raw, smaller⟩ := evaluation_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | constructor _ _ children => exact ⟨_, _, .values children, .values _, Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller⟩
  | fault failed =>
    obtain ⟨_, raw, smaller⟩ := fault_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | constructorArgument _ children => exact ⟨_, _, .fault children, .fault _, Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller⟩
    | constructorMetadata _ badMetadata => exact False.elim (CompatibleExpressionConstructors.metadata_fault_excluded valid badMetadata)

inductive SourceMember (program : Program) (size : Nat) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (environment : Dynamic.Environment) (before : Dynamic.Heap) (base : ExpressionId)
    (index : Nat) : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | value {baseSize metadata arguments selected after}
      (baseTrace : SourceExecutionSize.ExpressionEvaluates program baseSize context evidence source environment before base (.constructed metadata arguments) after)
      (field : Dynamic.ValueAt arguments index selected)
      (baseSizeSmaller : baseSize < size) : SourceMember program size context evidence source environment before base index (.value selected) after
  | failure {baseSize reason after}
      (baseTrace : SourceExecutionSize.ExpressionFaults program baseSize context evidence source environment before base reason after)
      (baseSizeSmaller : baseSize < size) :
      SourceMember program size context evidence source environment before base index (.fault reason) after
  | shape {baseSize value after}
      (baseTrace : SourceExecutionSize.ExpressionEvaluates program baseSize context evidence source environment before base value after)
      (invalid : ¬ Dynamic.ConstructedValue value)
      (baseSizeSmaller : baseSize < size) : SourceMember program size context evidence source environment before base index (.fault .invalidProjection) after
  | position {baseSize metadata arguments after}
      (baseTrace : SourceExecutionSize.ExpressionEvaluates program baseSize context evidence source environment before base (.constructed metadata arguments) after)
      (missing : Dynamic.ValueIndexMissing arguments index)
      (baseSizeSmaller : baseSize < size) : SourceMember program size context evidence source environment before base index (.fault .invalidProjection) after

theorem member_inv {base : ExpressionId} {name : String} {index : Nat} (metadata : Metadata checked source id node type)
    (form : node.form = .member base name index) (unique : NodeOccurrencesUnique source)
    (trace : ExpressionOutcome program size context evidence source environment before id outcome after) :
    SourceMember program size context evidence source environment before base index outcome after := by
  cases trace with
  | value evaluated =>
    obtain ⟨_, raw, smaller⟩ := evaluation_raw_sized unique (lookupExpression?_sound metadata.found) (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | member _ base field => refine .value base field ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
  | fault failed =>
    obtain ⟨_, raw, smaller⟩ := fault_raw_sized unique (lookupExpression?_sound metadata.found) (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | memberBase _ base => refine .failure base ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | memberShape _ base invalid => refine .shape base invalid ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | memberIndex _ base missing => refine .position base missing ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller


inductive SourceIndex (program : Program) (size : Nat) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (environment : Dynamic.Environment) (before : Dynamic.Heap) (base key : ExpressionId) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | found {baseSize keySize sourceKey sourceValue entries lookup value middle after}
      (baseTrace : SourceExecutionSize.ExpressionEvaluates program baseSize context evidence source environment before base (.mapping sourceKey sourceValue entries) middle)
      (keyTrace : SourceExecutionSize.ExpressionEvaluates program keySize context evidence source environment middle key lookup after)
      (located : Dynamic.MappingLookup lookup entries value)
      (baseSizeSmaller : baseSize < size)
      (keySizeSmaller : keySize < size) :
      SourceIndex program size context evidence source environment before base key (.value value) after
  | default {baseSize keySize sourceKey sourceValue entries lookup value middle after}
      (baseTrace : SourceExecutionSize.ExpressionEvaluates program baseSize context evidence source environment before base (.mapping sourceKey sourceValue entries) middle)
      (keyTrace : SourceExecutionSize.ExpressionEvaluates program keySize context evidence source environment middle key lookup after)
      (absent : Dynamic.MappingAbsent lookup entries) (defaulted : Dynamic.DefaultValue sourceValue value)
      (baseSizeSmaller : baseSize < size)
      (keySizeSmaller : keySize < size) :
      SourceIndex program size context evidence source environment before base key (.value value) after
  | baseFailure {baseSize reason after}
      (failed : SourceExecutionSize.ExpressionFaults program baseSize context evidence source environment before base reason after)
      (baseSizeSmaller : baseSize < size) :
      SourceIndex program size context evidence source environment before base key (.fault reason) after
  | keyFailure {baseSize keySize baseValue reason middle after}
      (baseTrace : SourceExecutionSize.ExpressionEvaluates program baseSize context evidence source environment before base baseValue middle)
      (failed : SourceExecutionSize.ExpressionFaults program keySize context evidence source environment middle key reason after)
      (baseSizeSmaller : baseSize < size)
      (keySizeSmaller : keySize < size) :
      SourceIndex program size context evidence source environment before base key (.fault reason) after
  | shape {baseSize keySize baseValue lookup middle after}
      (baseTrace : SourceExecutionSize.ExpressionEvaluates program baseSize context evidence source environment before base baseValue middle)
      (keyTrace : SourceExecutionSize.ExpressionEvaluates program keySize context evidence source environment middle key lookup after)
      (invalid : ¬ Dynamic.MappingValue baseValue)
      (baseSizeSmaller : baseSize < size)
      (keySizeSmaller : keySize < size) :
      SourceIndex program size context evidence source environment before base key (.fault .invalidProjection) after
  | keyType {baseSize keySize sourceKey sourceValue entries lookup actual middle after}
      (baseTrace : SourceExecutionSize.ExpressionEvaluates program baseSize context evidence source environment before base (.mapping sourceKey sourceValue entries) middle)
      (keyTrace : SourceExecutionSize.ExpressionEvaluates program keySize context evidence source environment middle key lookup after)
      (typed : Dynamic.ValueRuntimeType lookup actual)
      (mismatch : Dynamic.runtimeType actual ≠ Dynamic.runtimeType sourceKey)
      (baseSizeSmaller : baseSize < size)
      (keySizeSmaller : keySize < size) :
      SourceIndex program size context evidence source environment before base key (.fault (.typeMismatch sourceKey (Dynamic.runtimeType actual))) after
  | unavailable {baseSize keySize sourceKey sourceValue entries lookup middle after}
      (baseTrace : SourceExecutionSize.ExpressionEvaluates program baseSize context evidence source environment before base (.mapping sourceKey sourceValue entries) middle)
      (keyTrace : SourceExecutionSize.ExpressionEvaluates program keySize context evidence source environment middle key lookup after)
      (typed : Dynamic.ValueRuntimeTypeMatches lookup sourceKey)
      (absent : Dynamic.MappingAbsent lookup entries) (missing : ¬ Dynamic.Defaultable sourceValue)
      (baseSizeSmaller : baseSize < size)
      (keySizeSmaller : keySize < size) :
      SourceIndex program size context evidence source environment before base key (.fault (.missingMappingDefault sourceValue)) after

theorem index_inv {base key : ExpressionId} (metadata : CompatibleExpressionReads.Metadata checked source id node type)
    (form : node.form = .index base key) (unique : NodeOccurrencesUnique source)
    (trace : ExpressionOutcome program size context evidence source environment before id outcome after) :
    SourceIndex program size context evidence source environment before base key outcome after := by
  cases trace with
  | value evaluated =>
    obtain ⟨_, raw, smaller⟩ := evaluation_raw_sized unique (lookupExpression?_sound metadata.found) (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | indexFound _ base key found => refine .found base key found ?_ ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | indexDefault _ base key absent defaulted => refine .default base key absent defaulted ?_ ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
  | fault failed =>
    obtain ⟨_, raw, smaller⟩ := fault_raw_sized unique (lookupExpression?_sound metadata.found) (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | indexBase _ failed => refine .baseFailure failed ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | indexKey _ base failed => refine .keyFailure base failed ?_ ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | indexShape _ base key shape => refine .shape base key shape ?_ ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | indexKeyType _ base key typed mismatch => refine .keyType base key typed mismatch ?_ ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | indexDefaultUnavailable _ base key typed absent missing => refine .unavailable base key typed absent missing ?_ ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller


theorem SourceIndex.split {base key : ExpressionId}
    (trace : SourceIndex program size context evidence source environment before base key outcome after) :
    (∃ reason child, outcome = .fault reason ∧
      SourceExecutionSize.ExpressionFaults program child context evidence source environment before base reason after ∧ child < size) ∨
    (∃ baseValue middle first, SourceExecutionSize.ExpressionEvaluates program first context evidence source environment before base baseValue middle ∧ first < size ∧
      ((∃ reason second, outcome = .fault reason ∧ SourceExecutionSize.ExpressionFaults program second context evidence source environment middle key reason after ∧ second < size) ∨
       (∃ keyValue second, SourceExecutionSize.ExpressionEvaluates program second context evidence source environment middle key keyValue after ∧ second < size ∧ Terminal baseValue keyValue outcome))) := by
  cases trace with
  | baseFailure failed smaller => exact .inl ⟨_, _, rfl, failed, smaller⟩
  | keyFailure base failed firstSmaller secondSmaller => exact .inr ⟨_, _, _, base, firstSmaller, .inl ⟨_, _, rfl, failed, secondSmaller⟩⟩
  | found base key found firstSmaller secondSmaller => exact .inr ⟨_, _, _, base, firstSmaller, .inr ⟨_, _, key, secondSmaller, .found rfl found⟩⟩
  | default base key absent defaulted firstSmaller secondSmaller => exact .inr ⟨_, _, _, base, firstSmaller, .inr ⟨_, _, key, secondSmaller, .default rfl absent defaulted⟩⟩
  | shape base key invalid firstSmaller secondSmaller => exact .inr ⟨_, _, _, base, firstSmaller, .inr ⟨_, _, key, secondSmaller, .shape invalid⟩⟩
  | keyType base key typed mismatch firstSmaller secondSmaller => exact .inr ⟨_, _, _, base, firstSmaller, .inr ⟨_, _, key, secondSmaller, .keyType rfl typed mismatch⟩⟩
  | unavailable base key typed absent missing firstSmaller secondSmaller => exact .inr ⟨_, _, _, base, firstSmaller, .inr ⟨_, _, key, secondSmaller, .unavailable rfl typed absent missing⟩⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedDataExpressionSourceBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedDataExpressionHeadBounds
/-! Finite budgets compose the constructor/member/index cases of the existing
static head. Actual child states pass through their real reached effects.
This layer neither changes the expression grammar nor closes its recursive
call/body obligations. Reflected source costs are independent of native costs. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedDataExpressionHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleExpressionPrimitives
open CompatibleExpressionConditionals CompatibleExpressionConstructors CompatibleExpressionMembers
open CompatibleExpressionIndices CoreProof
open GenericExpressionMeaning (agree_prefix rename_prefix)
open DataPatternValues
open RecursiveNamedCallBounds RecursiveNamedBoundedContracts
open CompatibleExpressionCalls (Head CallHeads)
/-- Only the data cases of the existing head are selected by this layer. -/
inductive Data {calls : CallHeads} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {context : SourceSemantics.Context}
    {reasonAt : ExpressionId → Word} {children : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} :
    {id : ExpressionId} → {lowered : SourceCoreBasic.LoweredExpr} →
    Head calls values source context reasonAt children scope id lowered → Prop where
  | constructor {id node instantiation ids tag header codes}
      (receipt : CompatibleExpressionConstructors.Header values source id node instantiation tag header codes)
      (form : node.form = .constructor instantiation ids)
      (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
      (sequence : DataExpressionSequence.Tree source children scope ids instantiation.payloadTypes codes) :
      Data (.constructor receipt form valid sequence)
  | member {id node base baseNode name index identity branches result child}
      (metadata : Metadata values.checked source id node result)
      (baseMetadata : Metadata values.checked source base baseNode child.type)
      (form : node.form = .member base name index)
      (layout : CompatibleExpressionMembers.Layout values.checked (.occurrence id.occurrence) baseNode.type node.type index identity branches result)
      (certified : children scope base child) :
      Data (.member metadata baseMetadata form layout certified)
  | index {id node base key baseNode keyNode layout comparison first second}
      (header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second)
      (keyFound : source.lookupExpression? key = some keyNode)
      (form : node.form = .index base key)
      (sourceType : baseNode.type = .mapping keyNode.type node.type)
      (baseCertified : children scope base first) (keyCertified : children scope key second) :
      Data (.index header keyFound form sourceType baseCertified keyCertified)

def Certificate (calls : CallHeads) (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (reasonAt : ExpressionId → Word)
    (children : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate := fun scope id lowered =>
  ∃ head : Head calls values source context reasonAt children scope id lowered, Data head

private theorem valuesRep {values : SourceCoreCompatibleValues.Context} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {types : List TypeSystem.Ty} {natives : List Ty}
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world types natives sources payloads) :
    ValuesRep values.checked registry functions mapping world types sources payloads natives := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih => exact .cons head ih

private theorem missing_excludes {values : List Dynamic.Value} {index : Nat} {value : Dynamic.Value}
    (missing : Dynamic.ValueIndexMissing values index) (selected : Dynamic.ValueAt values index value) : False := by
  induction missing with
  | nil => cases selected
  | tail rest ih => cases selected with | tail child => exact ih child

private theorem at_functional {values : List Dynamic.Value} {index : Nat} {first second : Dynamic.Value}
    (left : Dynamic.ValueAt values index first) (right : Dynamic.ValueAt values index second) : first = second := by
  induction left with
  | head => cases right; rfl
  | tail _ ih => cases right with | tail rest => exact ih rest

private def ReflectsRawAt (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : GenericExpressionMeaning.Certificate) (faults : FunctionCalls.FaultRep) (entry : ProtectedExpressionMeaning.Entry) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    entry scope mapping world before store canonical →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after


variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))


namespace Stateful
universe u v
variable {calls : CallHeads} {certificate : GenericExpressionMeaning.Certificate}
  {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
private def ReflectsRawAt {Records : Type v} (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : GenericExpressionMeaning.Certificate) (faults : FunctionCalls.FaultRep) (protocol : ProtectedStateTransition.Protocol.{u, v} Records) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩


include extension in
/-- The constructor's original Source suffix consumes its actual ordered
sequence receipt and keeps that sequence's exact reached state. -/
theorem constructor_preserves_after_sequence (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {instantiation : DataConstructorInstantiation} {ids : List ExpressionId}
    {tag : ConstructorId} {header : Word} {codes : List SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionConstructors.Header values source id node instantiation tag header codes)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (sequence : ProtectedStateExpressionSequenceProducer.Preserves
      (program := program) (context := context) (evidence := evidence) (source := source)
      (environment := environment) (actual := actual) (ξ := ξ) (ids := ids)
      (sourceTypes := instantiation.payloadTypes) (codes := codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) initial budget)
    {sequenceSize : Nat} {sourceOutcome : DataExpressionSequence.Outcome}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (sourceTrace : ProtectedDataExpressionSequence.TraceAt program sequenceSize context evidence source environment before ids sourceOutcome after)
    (packed : CompatibleExpressionConstructors.PacksOutcome instantiation sourceOutcome outcome)
    (within : sequenceSize ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCompatibleDataExpressions.construct tag header (SourceCoreCalls.packArguments codes).expression).rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type (.namedData tag.owner) faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
    sequence sourceTrace within
  cases represented with
  | @values sources payloadValues payloads =>
    cases packed
    have projected := receipt.metadata.projected
    rw [receipt.sourceType] at projected
    refine ⟨.inRight .word (.constructed tag (.pair (.word header) (packValues payloadValues))), finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩
    · rw [CompatibleExpressionConstructors.construct_rename]; exact CompatibleExpressionConstructors.construct_success tag header evaluated
    · rw [receipt.sourceType]
      exact .value (.constructed (receipt.original.extend extension) (extension.signatures.trans values.registryOwner)
        receipt.selected projected receipt.registered (valuesRep payloads))
  | fault matched =>
    cases packed
    exact ⟨_, finalStore, finalMap, finalWorld, by rw [CompatibleExpressionConstructors.construct_rename]; exact CompatibleExpressionConstructors.construct_failure tag header evaluated,
      .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩


include extension in
/-- The original measured constructor argument child supplies the same actual
post. Native result determinism retains the original final store. -/
theorem constructor_reflects_after_sequence (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {instantiation : DataConstructorInstantiation} {ids : List ExpressionId}
    {tag : ConstructorId} {header : Word} {codes : List SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionConstructors.Header values source id node instantiation tag header codes)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (form : node.form = .constructor instantiation ids)
    (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
    (sequence : ProtectedStateExpressionSequenceProducer.Reflects
      (program := program) (context := context) (evidence := evidence) (source := source)
      (environment := environment) (actual := actual) (ξ := ξ) (ids := ids)
      (sourceTypes := instantiation.payloadTypes) (codes := codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) initial budget)
    {sequenceSize : Nat} {childValue value : Value} {childStore finalStore : Store}
    (child : EvaluationSize sequenceSize actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) childValue childStore)
    (within : sequenceSize < budget)
    (complete : Evaluates actual store (SourceCoreCompatibleDataExpressions.construct tag header ((SourceCoreCalls.packArguments codes).expression.rename ξ)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type (.namedData tag.owner) faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, sourceOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, transition⟩ := sequence child within
  cases represented with
  | fault matched =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (CompatibleExpressionConstructors.construct_failure tag header child.sound)
    exact ⟨_, after, finalMap, finalWorld, constructor_intro receipt.metadata form valid trace.sound (.fault _),
      .fault matched, finalHeaps, maps, worlds, frame, metadata, transition⟩
  | values payloads =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (CompatibleExpressionConstructors.construct_success tag header child.sound)
    have projected := receipt.metadata.projected
    rw [receipt.sourceType] at projected
    refine ⟨_, after, finalMap, finalWorld, constructor_intro receipt.metadata form valid trace.sound (.values _),
      ?_, finalHeaps, maps, worlds, frame, metadata, transition⟩
    rw [receipt.sourceType]
    exact .value (.constructed (receipt.original.extend extension) (extension.signatures.trans values.registryOwner)
      receipt.selected projected receipt.registered (valuesRep payloads))

namespace WithReady
open ProtectedStateExpressionOperandTyping
variable (ready : ∀ {index : ProtectedStateTransition.Index}, protocol.State index → Prop)

private theorem forget_reached {initial final : ProtectedStateTransition.Index}
    {first : protocol.State initial} {outcome : Dynamic.ExpressionOutcome}
    (post : ProtectedStateTransition.WithReady.Reached protocol ready outcome first final) :
    ProtectedStateTransition.Transition protocol first final := by
  obtain ⟨reached, related, _⟩ := post
  exact ⟨reached, related⟩

/-- Constructor arguments use only the actual parent's ordered operands and
one whole-sequence producer at the genuine caller input. -/
def SequencePreservesFor (budget : Nat) (scope : SourceCoreLocalCell.Scope) (root : ExpressionNode) : Prop :=
  ∀ {ids types codes}, ids = actualOperandIds root.form →
    DataExpressionSequence.Tree source certificate scope ids types codes →
  ∀ {mapping world administrative environment canonical actual actualContext before store ξ},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩, ready initial →
    ProtectedStateExpressionSequenceProducer.Preserves
      (program := program) (context := context) (evidence := evidence) (source := source)
      (environment := environment) (actual := actual) (ξ := ξ) (ids := ids) (sourceTypes := types)
      (codes := codes) (faults := faults) (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      initial (budget + 1)

/-- Constructor arguments use only the actual parent's ordered operands and
one whole-sequence producer at the genuine caller input. -/
def SequenceReflectsFor (budget : Nat) (scope : SourceCoreLocalCell.Scope) (root : ExpressionNode) : Prop :=
  ∀ {ids types codes}, ids = actualOperandIds root.form →
    DataExpressionSequence.Tree source certificate scope ids types codes →
  ∀ {mapping world administrative environment canonical actual actualContext before store ξ},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩, ready initial →
    ProtectedStateExpressionSequenceProducer.Reflects
      (program := program) (context := context) (evidence := evidence) (source := source)
      (environment := environment) (actual := actual) (ξ := ξ) (ids := ids) (sourceTypes := types)
      (codes := codes) (faults := faults) (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      initial (budget + 1)

include transport extension faithful functionLeaves functionTypes unique missing in
theorem Head.preserves_at (budget size : Nat) (bounded : size ≤ budget)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {root : ExpressionNode} (certified : Certificate calls values source context reasonAt certificate scope id lowered)
    (found : source.lookupExpression? id = some root)
    (meaning : ∀ childId, childId ∈ actualOperandIds root.form → ∀ childSize, childSize ≤ budget →
      ProtectedStateTransition.WithReady.PreservesAt protocol ready
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source
        (fun current expression code => expression = childId ∧ certificate current expression code) faults childSize)
    (sequences : SequencePreservesFor (values := values) (source := source) (context := context)
      (registry := registry) (faults := faults) (certificate := certificate) functions program evidence protocol ready budget scope root) :
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrativeContext scope environment canonical ambient.definitions →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩, ready initial →
    ExpressionOutcome program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld root.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨head, data⟩ := certified
  cases data with
  | @constructor node instantiation ids tag header codes receipt form valid sequence =>
    intro mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry initialReady trace
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    obtain ⟨sequenceSize, sourceOutcome, sourceTrace, packed, sequenceSmaller⟩ := RecursiveNamedDataExpressionSourceBounds.constructor_inv receipt.metadata form unique valid trace
    exact constructor_preserves_after_sequence functions extension program evidence protocol (budget + 1) receipt installedEntry
      (sequences (by simp only [form, actualOperandIds]) sequence environments heaps locals agrees actualTyped installedEntry initialReady)
      sourceTrace packed (by omega)

  | @member node base baseNode name index identity branches result child metadata baseMetadata form layout childTree =>
    intro mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry initialReady trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have ih := fun n (bound : n ≤ budget) => @meaning base (by rw [form]; change base ∈ [base]; simp) n bound _ _ _ ⟨rfl, childTree⟩
    have raw := RecursiveNamedDataExpressionSourceBounds.member_inv metadata form unique trace
    cases raw with
    | value childTrace selected childSmaller =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        ih _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨actualMetadata, sources, sourceChild, native, shape, sourceAt, related, completed⟩ := member_success layout payload evaluated
        cases shape
        have same := at_functional sourceAt selected
        subst sourceChild
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [member_rename layout]; exact completed,
          .value related, finalHeaps, maps, worlds, frame, heapMetadata, forget_reached protocol ready transition⟩
    | failure childTrace childSmaller =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        ih _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [member_rename layout]; exact LanguageResult.bind_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, forget_reached protocol ready transition⟩
    | shape childTrace invalid childSmaller =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, _⟩ :=
        ih _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨_, _, _, _, shape, _⟩ := member_success layout payload evaluated
        subst_vars
        exact False.elim (invalid .intro)
    | position childTrace missing childSmaller =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, _⟩ :=
        ih _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨_, _, _, _, shape, selected, _⟩ := member_success layout payload evaluated
        cases shape
        exact False.elim (missing_excludes missing selected)

  | @index node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree =>
    intro mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped installedEntry initialReady trace
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst root
    have firstIH := fun n (bound : n ≤ budget) => @meaning base (by rw [form]; change base ∈ [base, key]; simp) n bound _ _ _ ⟨rfl, firstTree⟩
    have secondIH := fun n (bound : n ≤ budget) => @meaning key (by rw [form]; change key ∈ [base, key]; simp) n bound _ _ _ ⟨rfl, secondTree⟩
    rcases (RecursiveNamedDataExpressionSourceBounds.index_inv header.metadata form unique trace).split with ⟨reason, baseSize, rfl, failed, baseSmaller⟩ | ⟨baseSource, middle, baseSize, baseTrace, baseSmaller, tail⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
        firstIH _ (Nat.le_trans (Nat.le_of_lt baseSmaller) bounded) header.baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady (.fault failed)
      cases represented with
      | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps, maps, worlds, frame, metadata, forget_reached protocol ready transition⟩
        rw [index_rename comparison header.registered header.comparisonType]
        exact LanguageResult.bind_failure _ evaluated
    · obtain ⟨value, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstTransition⟩ :=
        firstIH _ (Nat.le_trans (Nat.le_of_lt baseSmaller) bounded) header.baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady (.value baseTrace)
      cases represented with
      | @value _ baseValue baseRep =>
        obtain ⟨middleState, firstRelated, firstReady⟩ := firstTransition
        have keyEnvironment := RuntimeEnvironmentHasTypes.cons baseRep.runtime_hasType (actualTyped.weaken firstWorlds)
        rcases tail with ⟨reason, keySize, rfl, failed, keySmaller⟩ | ⟨keySource, keySize, keyTrace, keySmaller, terminal⟩
        · obtain ⟨value, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
            secondIH _ (Nat.le_trans (Nat.le_of_lt keySmaller) bounded) keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) keyEnvironment middleState (firstReady _ rfl) (.fault failed)
          cases represented with
          | fault matched =>
            obtain ⟨finalState, secondRelated, _⟩ := transition
            refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
              firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, ⟨finalState, protocol.trans firstRelated secondRelated⟩⟩
            rw [index_rename comparison header.registered header.comparisonType]
            rw [rename_prefix] at secondEval
            exact LanguageResult.bind_success _ firstEval (LanguageResult.bind_failure _ secondEval)
        · obtain ⟨value, keyStore, keyMap, keyWorld, secondEval, represented, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata, keyTransition⟩ :=
            secondIH _ (Nat.le_trans (Nat.le_of_lt keySmaller) bounded) keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) keyEnvironment middleState (firstReady _ rfl) (.value keyTrace)
          cases represented with
          | @value _ keyValue keyRep =>
            obtain ⟨actualOutcome, result, finalStore, finalWorld, terminal', related, lookup, finalHeaps, worlds, frame, uniqueResult⟩ :=
              CompatibleGeneralIndex.finish header sourceType faithful functionLeaves functionTypes (baseRep.extend (.refl _) keyMaps keyWorlds) keyRep
                (actualTyped.weaken (firstWorlds.trans keyWorlds)) keyHeaps (reasonAt id) (missing id)
            obtain ⟨keyState, keyRelated, _⟩ := keyTransition
            obtain ⟨finalState, terminalRelated⟩ := transport.transition protocol keyState (.refl _) worlds frame (.refl _)
            have same := uniqueResult outcome terminal
            subst actualOutcome
            refine ⟨result, finalStore, keyMap, finalWorld, ?_, related, finalHeaps,
              firstMaps.trans keyMaps, (firstWorlds.trans keyWorlds).trans worlds,
              (firstFrame.trans keyFrame).trans frame, firstMetadata.trans keyMetadata, ⟨finalState, protocol.trans firstRelated (protocol.trans keyRelated terminalRelated)⟩⟩
            rw [index_rename comparison header.registered header.comparisonType]
            rw [rename_prefix] at secondEval
            apply SourceCoreCompatibleDataExpressions.index_completed layout (reasonAt id) firstEval secondEval
            simpa only [CompatibleMapping.Transport.expression_weaken] using lookup



include transport extension faithful functionLeaves functionTypes missing in
theorem Head.reflects_raw_at (budget size : Nat) (bounded : size ≤ budget)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {root : ExpressionNode} (certified : Certificate calls values source context reasonAt certificate scope id lowered)
    (found : source.lookupExpression? id = some root)
    (meaning : ∀ childId, childId ∈ actualOperandIds root.form → ∀ childSize, childSize ≤ budget →
      ProtectedStateTransition.WithReady.ReflectsAt protocol ready
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source
        (fun current expression code => expression = childId ∧ certificate current expression code) faults childSize)
    (sequences : SequenceReflectsFor (values := values) (source := source) (context := context)
      (registry := registry) (faults := faults) (certificate := certificate) functions program evidence protocol ready budget scope root) :
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrativeContext scope environment canonical ambient.definitions →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩, ready initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld root.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨head, data⟩ := certified
  cases data with
  | @constructor node instantiation ids tag header codes receipt form valid sequence =>
    intro mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry initialReady evaluated
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    rw [CompatibleExpressionConstructors.construct_rename] at evaluated
    have complete := evaluated.sound
    cases evaluated with
    | caseLeft childEvaluation branch =>
      exact constructor_reflects_after_sequence functions extension program evidence protocol (budget + 1) receipt installedEntry form valid
        (sequences (by simp only [form, actualOperandIds]) sequence environments heaps locals agrees actualTyped installedEntry initialReady)
        childEvaluation (by omega) complete
    | caseRight childEvaluation branch =>
      exact constructor_reflects_after_sequence functions extension program evidence protocol (budget + 1) receipt installedEntry form valid
        (sequences (by simp only [form, actualOperandIds]) sequence environments heaps locals agrees actualTyped installedEntry initialReady)
        childEvaluation (by omega) complete

  | @member node base baseNode name index identity branches result child metadata baseMetadata form layout childTree =>
    intro mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry initialReady evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have ih := fun n (bound : n ≤ budget) => @meaning base (by rw [form]; change base ∈ [base]; simp) n bound _ _ _ ⟨rfl, childTree⟩
    rw [member_rename layout] at evaluated
    have complete := evaluated.sound
    cases evaluated with
    | caseLeft baseEvaluation branch =>
      obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        ih _ (by omega) baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady baseEvaluation
      cases represented with
      | fault matched =>
        have expected := LanguageResult.bind_failure result baseEvaluation.sound (body := .matchData identity (LanguageResult.resultType result) (.var 0) branches)
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | fault failed =>
          exact ⟨_, after, finalMap, finalWorld, member_intro metadata form (.failure failed.sound), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, forget_reached protocol ready transition⟩
    | caseRight baseEvaluation branch =>
      obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        ih _ (by omega) baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady baseEvaluation
      cases represented with
      | value payload =>
        obtain ⟨actualMetadata, sources, selected, native, shape, sourceAt, related, expected⟩ := member_success layout payload baseEvaluation.sound
        subst_vars
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | value childTrace =>
          exact ⟨_, after, finalMap, finalWorld, member_intro metadata form (.value childTrace.sound sourceAt), .value related,
            finalHeaps, maps, worlds, frame, heapMetadata, forget_reached protocol ready transition⟩

  | @index node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree =>
    intro mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped installedEntry initialReady evaluated
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst root
    have firstIH := fun n (bound : n ≤ budget) => @meaning base (by rw [form]; change base ∈ [base, key]; simp) n bound _ _ _ ⟨rfl, firstTree⟩
    have secondIH := fun n (bound : n ≤ budget) => @meaning key (by rw [form]; change key ∈ [base, key]; simp) n bound _ _ _ ⟨rfl, secondTree⟩
    rw [index_rename comparison header.registered header.comparisonType] at evaluated
    have complete := evaluated.sound
    cases evaluated with
    | caseLeft baseEvaluation branch =>
      obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
        firstIH _ (by omega) header.baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady baseEvaluation
      cases represented with
      | fault matched =>
        have expected := LanguageResult.bind_failure layout.valueType baseEvaluation.sound (body :=
          LanguageResult.bind layout.valueType ((second.expression.rename ξ).weakenAt 0)
            (SourceCoreMappingWithDefault.lookup layout (reasonAt id) (comparison.expression.weakenAt 0 |>.weakenAt 0) (.var 1) (.var 0)))
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | fault failed => exact ⟨_, after, finalMap, finalWorld, index_intro header.metadata form (.baseFailure failed.sound),
            .fault matched, finalHeaps, maps, worlds, frame, metadata, forget_reached protocol ready transition⟩
    | caseRight baseEvaluation branch =>
      obtain ⟨childSourceSize, outcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstTransition⟩ :=
        firstIH _ (by omega) header.baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady baseEvaluation
      cases represented with
      | @value baseSource baseValue baseRep =>
        cases trace with
        | value baseTrace =>
          obtain ⟨middleState, firstRelated, firstReady⟩ := firstTransition
          have keyEnvironment := RuntimeEnvironmentHasTypes.cons baseRep.runtime_hasType (actualTyped.weaken firstWorlds)
          cases branch with
          | caseLeft keyEvaluation ignored =>
            rw [← rename_prefix] at keyEvaluation
            obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
              secondIH _ (by omega) keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (agree_prefix agrees _) keyEnvironment middleState (firstReady _ rfl) keyEvaluation
            cases represented with
            | fault matched =>
              obtain ⟨finalState, secondRelated, _⟩ := transition
              rw [rename_prefix] at keyEvaluation
              have expected := LanguageResult.bind_success layout.valueType baseEvaluation.sound
                (LanguageResult.bind_failure layout.valueType keyEvaluation.sound (body :=
                  SourceCoreMappingWithDefault.lookup layout (reasonAt id) (comparison.expression.weakenAt 0 |>.weakenAt 0) (.var 1) (.var 0)))
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
              cases trace with
              | fault failed => exact ⟨_, after, finalMap, finalWorld, index_intro header.metadata form (.keyFailure baseTrace.sound failed.sound),
                  .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, ⟨finalState, protocol.trans firstRelated secondRelated⟩⟩
          | caseRight keyEvaluation lookupEvaluation =>
            rw [← rename_prefix] at keyEvaluation
            obtain ⟨keySourceSize, outcome, after, keyMap, keyWorld, trace, represented, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata, keyTransition⟩ :=
              secondIH _ (by omega) keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (agree_prefix agrees _) keyEnvironment middleState (firstReady _ rfl) keyEvaluation
            cases represented with
            | @value keySource keyValue keyRep =>
              obtain ⟨outcome, result, endStore, finalWorld, terminal, related, lookup, finalHeaps, worlds, frame, uniqueResult⟩ :=
                CompatibleGeneralIndex.finish header sourceType faithful functionLeaves functionTypes (baseRep.extend (.refl _) keyMaps keyWorlds) keyRep
                  (actualTyped.weaken (firstWorlds.trans keyWorlds)) keyHeaps (reasonAt id) (missing id)
              rw [rename_prefix] at keyEvaluation
              have expected := SourceCoreCompatibleDataExpressions.index_completed (comparison := comparison.expression) layout (reasonAt id) baseEvaluation.sound keyEvaluation.sound
                (by simpa only [CompatibleMapping.Transport.expression_weaken] using lookup)
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
              obtain ⟨keyState, keyRelated, _⟩ := keyTransition
              obtain ⟨finalState, terminalRelated⟩ := transport.transition protocol keyState (.refl _) worlds frame (.refl _)
              cases trace with
              | value keyTrace =>
                exact ⟨outcome, after, keyMap, finalWorld, index_intro header.metadata form (terminal.trace baseTrace.sound keyTrace.sound),
                  related, finalHeaps, firstMaps.trans keyMaps, (firstWorlds.trans keyWorlds).trans worlds,
                  (firstFrame.trans keyFrame).trans frame, firstMetadata.trans keyMetadata, ⟨finalState, protocol.trans firstRelated (protocol.trans keyRelated terminalRelated)⟩⟩





end WithReady

include transport extension faithful functionLeaves functionTypes unique missing in
theorem preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults childSize)
 :
    ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate calls values source context reasonAt certificate) faults size := by
  intro scope id lowered ⟨head, data⟩ root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial execution
  cases data with
  | @constructor node instantiation ids tag header codes receipt form valid sequence =>
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    obtain ⟨sequenceSize, sourceOutcome, sourceTrace, packed, sequenceSmaller⟩ := RecursiveNamedDataExpressionSourceBounds.constructor_inv receipt.metadata form unique valid execution
    exact constructor_preserves_after_sequence functions extension program evidence protocol (budget + 1) receipt initial
      (ProtectedStateExpressionSequenceProducer.Preserves.of_uniform initial (budget + 1) sequence
        (fun n bound => ProtectedStateTransition.SequenceBridge.preserves_at protocol (meaning n (by omega)))
        environments heaps locals agrees actualTyped) sourceTrace packed (by omega)
  | member metadata baseMetadata form layout child =>
    have data := Data.member (calls := calls) (context := context) (reasonAt := reasonAt) metadata baseMetadata form layout child
    exact WithReady.Head.preserves_at functions extension faithful functionLeaves functionTypes program evidence unique missing
      protocol transport (fun _ => True) budget size bounded ⟨_, data⟩ found
      (fun child member n bound => ProtectedStateTransition.WithReady.PreservesAt.of_stateful protocol
        (fun {childScope expression code} (entry : expression = child ∧ certificate childScope expression code) => meaning n bound entry.2))
      (fun {ids types codes} same tree {mapping world administrative environment canonical actual actualContext before store ξ}
          env hp lc layout typed state _ =>
        ProtectedStateExpressionSequenceProducer.Preserves.of_uniform state (budget + 1) tree
          (fun n bound => ProtectedStateTransition.SequenceBridge.preserves_at protocol (meaning n (by omega)))
          env hp lc layout typed)
      environments heaps locals agrees actualTyped initial True.intro execution
  | index receipt keyFound form sourceType first second =>
    have data := Data.index (calls := calls) (context := context) (reasonAt := reasonAt) receipt keyFound form sourceType first second
    exact WithReady.Head.preserves_at functions extension faithful functionLeaves functionTypes program evidence unique missing
      protocol transport (fun _ => True) budget size bounded ⟨_, data⟩ found
      (fun child member n bound => ProtectedStateTransition.WithReady.PreservesAt.of_stateful protocol
        (fun {childScope expression code} (entry : expression = child ∧ certificate childScope expression code) => meaning n bound entry.2))
      (fun {ids types codes} same tree {mapping world administrative environment canonical actual actualContext before store ξ}
          env hp lc layout typed state _ =>
        ProtectedStateExpressionSequenceProducer.Preserves.of_uniform state (budget + 1) tree
          (fun n bound => ProtectedStateTransition.SequenceBridge.preserves_at protocol (meaning n (by omega)))
          env hp lc layout typed)
      environments heaps locals agrees actualTyped initial True.intro execution

include transport extension faithful functionLeaves functionTypes missing in
private theorem reflects_raw_at (budget size : Nat) (bounded : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults childSize)
 :
    ReflectsRawAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate calls values source context reasonAt certificate) faults protocol := by
  intro scope id lowered ⟨head, data⟩ root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial execution
  cases data with
  | @constructor node instantiation ids tag header codes receipt form valid sequence =>
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    rw [CompatibleExpressionConstructors.construct_rename] at execution
    have complete := execution.sound
    cases execution with
    | caseLeft childEvaluation branch =>
      exact constructor_reflects_after_sequence functions extension program evidence protocol (budget + 1) receipt initial form valid
        (ProtectedStateExpressionSequenceProducer.Reflects.of_uniform initial (budget + 1) sequence
          (fun n bound => ProtectedStateTransition.SequenceBridge.reflects_at protocol (meaning n (by omega)))
          environments heaps locals agrees actualTyped) childEvaluation (by omega) complete
    | caseRight childEvaluation branch =>
      exact constructor_reflects_after_sequence functions extension program evidence protocol (budget + 1) receipt initial form valid
        (ProtectedStateExpressionSequenceProducer.Reflects.of_uniform initial (budget + 1) sequence
          (fun n bound => ProtectedStateTransition.SequenceBridge.reflects_at protocol (meaning n (by omega)))
          environments heaps locals agrees actualTyped) childEvaluation (by omega) complete
  | member metadata baseMetadata form layout child =>
    have data := Data.member (calls := calls) (context := context) (reasonAt := reasonAt) metadata baseMetadata form layout child
    exact WithReady.Head.reflects_raw_at functions extension faithful functionLeaves functionTypes program evidence missing
      protocol transport (fun _ => True) budget size bounded ⟨_, data⟩ found
      (fun child member n bound => ProtectedStateTransition.WithReady.ReflectsAt.of_stateful protocol
        (fun {childScope expression code} (entry : expression = child ∧ certificate childScope expression code) => meaning n bound entry.2))
      (fun {ids types codes} same tree {mapping world administrative environment canonical actual actualContext before store ξ}
          env hp lc layout typed state _ =>
        ProtectedStateExpressionSequenceProducer.Reflects.of_uniform state (budget + 1) tree
          (fun n bound => ProtectedStateTransition.SequenceBridge.reflects_at protocol (meaning n (by omega)))
          env hp lc layout typed)
      environments heaps locals agrees actualTyped initial True.intro execution
  | index receipt keyFound form sourceType first second =>
    have data := Data.index (calls := calls) (context := context) (reasonAt := reasonAt) receipt keyFound form sourceType first second
    exact WithReady.Head.reflects_raw_at functions extension faithful functionLeaves functionTypes program evidence missing
      protocol transport (fun _ => True) budget size bounded ⟨_, data⟩ found
      (fun child member n bound => ProtectedStateTransition.WithReady.ReflectsAt.of_stateful protocol
        (fun {childScope expression code} (entry : expression = child ∧ certificate childScope expression code) => meaning n bound entry.2))
      (fun {ids types codes} same tree {mapping world administrative environment canonical actual actualContext before store ξ}
          env hp lc layout typed state _ =>
        ProtectedStateExpressionSequenceProducer.Reflects.of_uniform state (budget + 1) tree
          (fun n bound => ProtectedStateTransition.SequenceBridge.reflects_at protocol (meaning n (by omega)))
          env hp lc layout typed)
      environments heaps locals agrees actualTyped initial True.intro execution

include transport extension faithful functionLeaves functionTypes missing in
theorem reflects_at (budget size : Nat) (bounded : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → ProtectedStateTransition.ReflectsAt protocol
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults childSize) :
    ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate calls values source context reasonAt certificate) faults size := by
  intro scope id lowered head node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped installedEntry completed
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
    reflects_raw_at functions extension faithful functionLeaves functionTypes program evidence missing protocol transport budget size bounded meaning head found environments heaps locals agrees actualTyped installedEntry completed
  obtain ⟨sourceSize, sized⟩ := ExpressionOutcome.has_size trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sized, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩

end Stateful

variable {calls : CallHeads} {certificate : GenericExpressionMeaning.Certificate}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)

include transport extension faithful functionLeaves functionTypes unique missing in
theorem preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → RecursiveNamedBoundedContracts.PreservesAt childSize (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry)
 :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate calls values source context reasonAt certificate) faults entry := by
  intro scope id lowered head node found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped installedEntry trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.preserves_at functions extension faithful functionLeaves functionTypes program evidence unique missing
      (ProtectedStatePlaceAssignment.legacyProtocol entry) (ProtectedStatePlaceAssignment.legacyTransport transport) budget size bounded
      (fun childSize bound => ProtectedStatePlaceAssignment.legacy_preserves transport (meaning childSize bound))
      head found environments heaps locals agrees actualTyped ⟨installedEntry⟩ trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩

include transport extension faithful functionLeaves functionTypes missing in
theorem reflects_at (budget size : Nat) (bounded : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → RecursiveNamedBoundedContracts.ReflectsAt childSize
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults entry) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate calls values source context reasonAt certificate) faults entry := by
  intro scope id lowered head node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped installedEntry completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.reflects_at functions extension faithful functionLeaves functionTypes program evidence missing
      (ProtectedStatePlaceAssignment.legacyProtocol entry) (ProtectedStatePlaceAssignment.legacyTransport transport) budget size bounded
      (fun childSize bound => ProtectedStatePlaceAssignment.legacy_reflects transport (meaning childSize bound))
      head found environments heaps locals agrees actualTyped ⟨installedEntry⟩ completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedDataExpressionHeadBounds
end
