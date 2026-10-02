import Solcore.SourceSemantics.CoreLowering.RecursiveNamedArgumentTraceBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogInvocationBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPlaceKeyContracts

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
  have argumentsMeaning : ∀ child, child < budget → ProtectedDataExpressionSequence.ExpressionPreservesAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      (protectedEntry headers locations capturePrefix callerPrefix) := by
    intro child smaller
    exact RecursiveNamedPlaceKeyContracts.preserves_at (argumentMeaning child smaller)
  cases trace with
  | argumentFault failed smaller =>
    obtain ⟨token, finalStore, finalMap, finalWorld, argumentEvaluation, matched, finalHeaps, maps, worlds, frame, metadata⟩ :=
      ProtectedDataExpressionSequence.preserves_fault_bounded (RecursiveNamedCatalog.entry_transport (headers := headers) (locations := locations) (capturePrefix := capturePrefix) (callerPrefix := callerPrefix)) budget children argumentsMeaning environments heaps locals agrees typed
        ⟨caller⟩ failed (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller within))
    refine ⟨_, finalStore, finalMap, finalWorld, SourceCoreCalls.call_argument_failure (packedType.symm ▸ argumentEvaluation),
      (by simpa only [header.resultType] using (FunctionCalls.ResultRepresents.fault (model := CompatibleAmbientHeap.payloadModel values.checked registry functions) (mapping := finalMap) (world := finalWorld) (sourceType := header.function.resultType) (type := header.named.signature.resultType) matched)), finalHeaps, maps, worlds, frame, metadata,
      ⟨caller.extend maps worlds frame metadata⟩⟩
  | @apply argumentsSize callSize arguments middle outcome after evaluated called argumentsSmaller callSmaller =>
    obtain ⟨payloads, middleStore, middleMap, middleWorld, argumentEvaluation, represented, middleHeaps, argumentMaps, argumentWorlds,
      argumentFrame, argumentMetadata⟩ :=
      ProtectedDataExpressionSequence.preserves_values_bounded (RecursiveNamedCatalog.entry_transport (headers := headers) (locations := locations) (capturePrefix := capturePrefix) (callerPrefix := callerPrefix)) budget children argumentsMeaning environments heaps locals agrees typed
        ⟨caller⟩ evaluated (Nat.le_of_lt (Nat.lt_of_lt_of_le argumentsSmaller within))
    rw [nativeTypes] at represented
    have related := values_arguments header.bindings represented
    have arity : header.function.parameters.length = arguments.length := by rw [header.parameters, List.length_map]; exact related.length.1
    obtain ⟨bodySize, bodyTrace, bodySmaller⟩ := RecursiveNamedCallBounds.source_call_body owners header.frame arity called
    let next := caller.extend argumentMaps argumentWorlds argumentFrame argumentMetadata
    obtain ⟨capture, value, finalStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps, bodyMaps, bodyWorlds, bodyFrame,
      bodyMetadata, finalEntry⟩ := invocation_preserves_bounded budget bodyMeaning next member related middleHeaps bodyTrace
      (Nat.le_of_lt (Nat.lt_trans bodySmaller (Nat.lt_of_lt_of_le callSmaller within)))
    have selected := OptionalCell.read_success reason
      (show Evaluates (DataPatternValues.packValues payloads :: actual) middleStore
        (.var (ξ (scope.length + callerPrefix + header.slot) + 1))
        (.cellRef (OptionalCell.cellType header.named.signature.functionType) (locations header)) middleStore
        from .var (agrees (caller.globals header member))) capture.read
    exact ⟨value, finalStore, finalMap, finalWorld, SourceCoreCalls.call_success argumentEvaluation selected bodyEvaluation,
      result, finalHeaps, argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds, argumentFrame.trans bodyFrame,
      argumentMetadata.trans bodyMetadata, finalEntry⟩

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
  have argumentsMeaning : ∀ child, child < budget → ProtectedDataExpressionSequence.ExpressionReflectsAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      (protectedEntry headers locations capturePrefix callerPrefix) := by
    intro child smaller
    exact RecursiveNamedPlaceKeyContracts.reflects_at (argumentMeaning child smaller)
  obtain ⟨argumentSize, argumentValue, middleStore, argumentSmaller, argumentEvaluation⟩ := RecursiveNamedCallBounds.call_arguments completed
  obtain ⟨sourceSize, argumentOutcome, middle, middleMap, middleWorld, argumentTrace, represented, middleHeaps,
    argumentMaps, argumentWorlds, argumentFrame, argumentMetadata⟩ :=
    ProtectedDataExpressionSequence.reflects_bounded (RecursiveNamedCatalog.entry_transport (headers := headers) (locations := locations) (capturePrefix := capturePrefix) (callerPrefix := callerPrefix)) budget children argumentsMeaning environments heaps locals agrees typed
      ⟨caller⟩ argumentEvaluation (Nat.lt_of_lt_of_le argumentSmaller within)
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
        ⟨caller.extend argumentMaps argumentWorlds argumentFrame argumentMetadata⟩⟩
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
        bodyMetadata, finalEntry⟩ := invocation_reflects_bounded budget bodyMeaning next member related middleHeaps capture bodyEvaluation
        (Nat.le_of_lt (Nat.lt_of_lt_of_le bodySmaller within))
      have called := RecursiveNamedCallBounds.call_of_body (context := context) (caller := evidence) header.frame bodyTrace
      refine ⟨SourceExecutionSize.stepSize [sourceSize, SourceExecutionSize.stepSize [bodySourceSize]], outcome, after, finalMap, finalWorld,
        .apply evaluatedArguments called (SourceExecutionSize.child_lt_stepSize (by simp))
          (SourceExecutionSize.child_lt_stepSize (by simp)), result, finalHeaps,
        argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds, argumentFrame.trans bodyFrame,
        argumentMetadata.trans bodyMetadata, finalEntry⟩


variable {compilation : SourceCoreFunctions.Context}

/-- A pointwise expression theorem at the existing static named head. The
argument and body obligations are internal smaller-trace contracts. -/
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
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
  intro scope id lowered head
  cases head with
  | @named callee arguments header node calleeNode name codes expression member metadata sourceType form calleeFound calleeForm
      calleeRequirements calleeCoercions valid predicates evidenceEmpty arity emission selectedSlot sequence nativeTypes =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees typed installed trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨caller⟩ := installed
    have independent := RecursiveNamedArgumentTraceBounds.source_inv metadata form calleeFound predicates evidenceEmpty unique trace
    obtain ⟨emitted, packed, target, selected⟩ := emission.equation
    change expression = _ at emitted
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preserved, heapMetadata, _⟩ :=
      call_preserves_bounded functions sequence nativeTypes packed budget argumentMeaning (bodyMeaning header member) owners member
        caller environments heaps locals agrees typed independent within
    refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, preserved, heapMetadata⟩
    · change Evaluates actual store (expression.rename ξ) value finalStore
      rw [emitted, NamedCalls.Arguments.call_rename, selectedSlot]
      exact evaluated
    · simpa only [sourceType] using represented

/-- Whole original native completion reconstructs a separately measured source
expression. No source trace is an input to this reflection theorem. -/
theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (argumentMeaning : Below budget (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix)))
    (bodyMeaning : ∀ header, header ∈ headers → Below budget
      (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults)) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (RecursiveNamedCatalog.Head headers compilation source context certificate) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
  intro scope id lowered head
  cases head with
  | @named callee arguments header node calleeNode name codes expression member metadata sourceType form calleeFound calleeForm
      calleeRequirements calleeCoercions valid predicates evidenceEmpty arity emission selectedSlot sequence nativeTypes =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees typed installed evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨caller⟩ := installed
    obtain ⟨emitted, packed, target, selected⟩ := emission.equation
    change expression = _ at emitted
    change EvaluationSize size actual store (expression.rename ξ) value finalStore at evaluated
    rw [emitted, NamedCalls.Arguments.call_rename, selectedSlot] at evaluated
    obtain ⟨traceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preserved, heapMetadata, _⟩ :=
      call_reflects_bounded functions sequence nativeTypes packed budget argumentMeaning (bodyMeaning header member) member
        caller environments heaps locals agrees typed evaluated within
    obtain ⟨sourceSize, independent⟩ := RecursiveNamedArgumentTraceBounds.source_intro metadata form calleeFound calleeForm
      calleeRequirements calleeCoercions valid predicates evidenceEmpty trace
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, independent, by simpa only [sourceType] using represented,
      finalHeaps, maps, worlds, preserved, heapMetadata⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionHeadBounds
