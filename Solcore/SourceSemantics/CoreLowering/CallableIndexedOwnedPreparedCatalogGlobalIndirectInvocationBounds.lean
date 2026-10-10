import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogNamedBodyContinuations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedValueInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralFunctionSelection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCalls

/-! A global value keeps its actual selected Header, SourceFrame, dictionary
and complete native capture. Strict nested flow at that Header finishes the real body;
the original parameter prefix and caller restoration use the same reached pool.
Source admission is derived from genuine packed Source typing and the retained
instantiation. No whole-body execution law or live closure-slot read is supplied.
The parent argument/callee fold and public gate decisions remain separate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open RecursiveNamedCatalogInvocationBounds (Below)
open CallableIndexedOwnedPreparedCatalogNamedBodyContinuations (Profile ProfilesFor FlowPreserves FlowReflects)

section Invocation
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (captureZero : owner.key.capturePrefix = 0)
  (globals : header.globals = compiled.indexed.base.globals.length)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (beforeTyped : Dynamic.HeapWellTyped header.function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (profiles : ProfilesFor (registry := registry) (certificates := certificates)
    (expressionSyntax := expressionSyntax) functions owner (header := header))
  (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header)
    header.context (.statements true header.function.body) header.function.resultType)
  (sameLayouts : header.layouts = compiled.indexed.layouts)
  (member : header ∈ headers)
  (capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)

/-- All fields describe the original restored caller and ordered records. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (finalStore : Store) : Prop :=
  ∃ finalMap finalWorld,
    FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      finalMap finalWorld header.function.resultType header.output faults outcome value ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
    ProtectedStateTransition.Transition (protocol headers keys) caller
      ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩

include captureZero globals beforeTyped argumentsTyped stable wellFormed profiles syntaxTree sameLayouts member represented heaps in
/-- Actual source invocation consumes its strict body flow through the original
parameter continuation. No whole-body law or diagnostic receipt is an input. -/
theorem invocation_preserves_bounded (budget : Nat)
    (below : Below budget (fun child => ∀ administrative
      (profile : Profile (certificates := certificates)
        (expressionSyntax := expressionSyntax) header administrative),
      FlowPreserves (registry := registry) (faults := faults) (headers := headers) functions owner profile child))
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked compiled.sourceProgram) size header.sourceBody header.function.evidence before arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
        (header.code.rename capture.embedding.lift) value finalStore ∧
      ResultAt (functions := functions) (caller := caller) (header := header)
        (registry := registry) (faults := faults) outcome after value finalStore := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, frame, metadata, returned⟩ :=
    CallableIndexedOwnedNamedValueInvocationBounds.invocation_preserves_bounded_at
      (functions := functions) (registry := registry) (faults := faults) owner sameLayouts
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (headers := headers) (keys := keys)
        (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header)
      (CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
      budget caller member capture represented heaps
      (CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.source_continuation
        (functions := functions) (owner := owner) (caller := caller)
        (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped) (stable := stable)
        (captureZero := captureZero) (globals := globals) (wellFormed := wellFormed) (profiles := profiles) (syntaxTree := syntaxTree) budget below)
      trace within
  exact ⟨value, finalStore, evaluated, finalMap, finalWorld, result, finalHeaps, maps, worlds, frame, metadata, returned⟩

include captureZero globals beforeTyped argumentsTyped stable wellFormed profiles syntaxTree sameLayouts member represented heaps in
/-- The measured native prefix remains original. Its strict body flow returns
an independent Source grade and the same restored caller pool. -/
theorem invocation_reflects_bounded (budget : Nat)
    (below : Below budget (fun child => ∀ administrative
      (profile : Profile (certificates := certificates)
        (expressionSyntax := expressionSyntax) header administrative),
      FlowReflects (registry := registry) (faults := faults) (headers := headers) functions owner profile child))
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.BodyOutcome (Program.ofChecked compiled.sourceProgram) sourceSize header.sourceBody header.function.evidence before arguments outcome after ∧
      ResultAt (functions := functions) (caller := caller) (header := header)
        (registry := registry) (faults := faults) outcome after value finalStore := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, frame, metadata, returned⟩ :=
    CallableIndexedOwnedNamedValueInvocationBounds.invocation_reflects_bounded_at
      (functions := functions) (registry := registry) (faults := faults) owner sameLayouts
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (headers := headers) (keys := keys)
        (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header)
      (CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
      budget caller member capture represented heaps
      (CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.native_continuation
        (functions := functions) (owner := owner) (caller := caller)
        (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped) (stable := stable)
        (captureZero := captureZero) (globals := globals) (wellFormed := wellFormed) (profiles := profiles) (syntaxTree := syntaxTree) budget below)
      completed within
  exact ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, result, finalHeaps, maps, worlds, frame, metadata, returned⟩


include captureZero globals beforeTyped argumentsTyped stable wellFormed profiles syntaxTree sameLayouts member represented heaps in
/-- The actual global dictionary is preserved when selecting its strict body.
Missing declaration and arity alternatives are ruled out only by the retained
SourceFrame, actual owner uniqueness and physical represented argument count. -/
theorem global_preserves_bounded {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {source : Dynamic.GlobalFunction}
    (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD source)
    (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (budget : Nat)
    (below : Below budget (fun child => ∀ administrative
      (profile : Profile (certificates := certificates)
        (expressionSyntax := expressionSyntax) header administrative),
      FlowPreserves (registry := registry) (faults := faults) (headers := headers) functions owner profile child))
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size context callerEvidence source.evidence
      before (.global source) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
        (header.code.rename capture.embedding.lift) value finalStore ∧
      ResultAt (functions := functions) (caller := caller) (header := header)
        (registry := registry) (faults := faults) outcome after value finalStore := by
  have arity : header.function.parameters.length = arguments.length :=
    (congrArg List.length header.parameters).trans ((List.length_map Prod.fst).trans represented.length.1)
  have namedCall : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size context callerEvidence
      header.function.evidence before (.global ⟨source.instantiation, header.function.evidence⟩)
      arguments outcome after := by
    have dictionary := sourceAt.dictionary
    cases source with
    | mk instantiation evidence =>
      change header.function.evidence = evidence at dictionary
      simpa only [← dictionary] using called
  obtain ⟨child, trace, smaller⟩ := RecursiveNamedCallBounds.source_call_body owners sourceAt.frame arity namedCall
  exact invocation_preserves_bounded functions owner captureZero globals caller beforeTyped argumentsTyped stable wellFormed
    profiles syntaxTree sameLayouts member capture represented heaps budget below trace
    (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller within))

include captureZero globals beforeTyped argumentsTyped stable wellFormed profiles syntaxTree sameLayouts member represented heaps in
/-- Native invocation returns an independent Source grade for the same retained
global and dictionary, after restoring the real caller from the reached pool. -/
theorem global_reflects_bounded {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {source : Dynamic.GlobalFunction}
    (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD source)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (budget : Nat)
    (below : Below budget (fun child => ∀ administrative
      (profile : Profile (certificates := certificates)
        (expressionSyntax := expressionSyntax) header administrative),
      FlowReflects (registry := registry) (faults := faults) (headers := headers) functions owner profile child))
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context callerEvidence source.evidence before
        (.global source) arguments outcome after ∧
      ResultAt (functions := functions) (caller := caller) (header := header)
        (registry := registry) (faults := faults) outcome after value finalStore := by
  obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
    invocation_reflects_bounded functions owner captureZero globals caller beforeTyped argumentsTyped stable wellFormed
      profiles syntaxTree sameLayouts member capture represented heaps budget below completed within
  have called := RecursiveNamedCallBounds.call_of_body (context := context)
    (caller := callerEvidence) sourceAt.frame trace
  refine ⟨SourceExecutionSize.stepSize [sourceSize], outcome, after, ?_, result⟩
  have dictionary := sourceAt.dictionary
  cases source with
  | mk instantiation evidence =>
    change header.function.evidence = evidence at dictionary
    simpa only [dictionary] using called


/-- This is the exact complete carrier in the authentic General named row. -/
def carrier (identity descriptor : Word) : Value :=
  .pair (.pair (.inRight .unit (.word identity))
    (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
      (header.code.rename capture.embedding.lift) capture.captured)) (.word descriptor)

include captureZero globals beforeTyped argumentsTyped stable wellFormed profiles syntaxTree sameLayouts member represented heaps in
/-- The actual named carrier applies its retained body once, after the strict
Source body child has returned through the original caller restoration. -/
theorem application_preserves_at {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {source : Dynamic.GlobalFunction}
    (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD source)
    (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (identity descriptor : Word) (budget : Nat)
    (below : Below budget (fun child => ∀ administrative
      (profile : Profile (certificates := certificates)
        (expressionSyntax := expressionSyntax) header administrative),
      FlowPreserves (registry := registry) (faults := faults) (headers := headers) functions owner profile child))
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size context callerEvidence source.evidence
      before (.global source) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [carrier (header := header) (owner := owner) capture identity descriptor, DataPatternValues.packValues payloads] store
        CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (functions := functions) (caller := caller) (header := header)
        (registry := registry) (faults := faults) outcome after value finalStore := by
  obtain ⟨value, finalStore, invoked, result⟩ :=
    global_preserves_bounded functions owner captureZero globals caller beforeTyped argumentsTyped stable wellFormed
      profiles syntaxTree sameLayouts member capture represented heaps sourceAt owners budget below called within
  exact ⟨value, finalStore, .apply (.second (.first (.var rfl))) (.var rfl) invoked, result⟩

include captureZero globals beforeTyped argumentsTyped stable wellFormed profiles syntaxTree sameLayouts member represented heaps in
/-- The real measured apply rule yields a strict native body grade; the
Source grade and the same global dictionary are returned independently. -/
theorem application_reflects_at {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {source : Dynamic.GlobalFunction}
    (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD source)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (identity descriptor : Word) (budget : Nat)
    (below : Below budget (fun child => ∀ administrative
      (profile : Profile (certificates := certificates)
        (expressionSyntax := expressionSyntax) header administrative),
      FlowReflects (registry := registry) (faults := faults) (headers := headers) functions owner profile child))
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [carrier (header := header) (owner := owner) capture identity descriptor, DataPatternValues.packValues payloads] store
      CallableIndexedLambdaCalls.applyPayload value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context callerEvidence source.evidence before
        (.global source) arguments outcome after ∧
      ResultAt (functions := functions) (caller := caller) (header := header)
        (registry := registry) (faults := faults) outcome after value finalStore := by
  obtain ⟨bodySize, smaller, applied⟩ := completed.apply_body (.second (.first (.var rfl))) (.var rfl)
  exact global_reflects_bounded functions owner captureZero globals caller beforeTyped argumentsTyped stable wellFormed
    profiles syntaxTree sameLayouts member capture represented heaps sourceAt budget below applied
    (Nat.le_trans (Nat.le_of_lt smaller) within)

end Invocation

section SourceAdmission
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {source : Dynamic.GlobalFunction}

/-- Real Source attribution gives the input row at the exact retained body,
including its residual-variable scope and genuine ordered dictionary. -/
theorem source_certificate (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD source)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ∃ facts, Dynamic.FunctionInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram) source.instantiation header.sourceBody
      header.types header.context facts := by
  obtain ⟨types, lexical, facts, certified⟩ := sourceAt.frame.instantiated.certificate wellFormed
  have extended := header.extended
  rw [sourceAt.frame.source, sourceAt.frame.context, sourceAt.frame.parameters] at extended
  have contextEq := Dynamic.MonoBindersExtend.functional certified.typing.inputs_extend extended
  have typesEq := (Dynamic.MonoBindersExtend.bodyTypes_eq certified.typing.inputs_extend).symm.trans
    (Dynamic.MonoBindersExtend.bodyTypes_eq extended)
  exact ⟨facts, typesEq ▸ contextEq ▸ certified⟩

/-- The actual Source callable and packed argument typings authenticate the
callee heap and raw input types. Physical arity is independent of packed typing. -/
theorem arguments_at_global (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD source)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {context : SourceSemantics.Context} {bodySource : TypedSource} {before : Dynamic.Heap}
    {arguments : List Dynamic.Value} {packed : Dynamic.Value} {parameter result : TypeSystem.Ty}
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context bodySource)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (callableTyped : Dynamic.ValueHasType context before (.global source) (.function parameter result))
    (packing : Dynamic.ValuesPack arguments packed)
    (packedTyped : Dynamic.ValueHasType context before packed parameter)
    (arity : header.function.parameters.length = arguments.length) :
    Dynamic.HeapWellTyped header.function.context before ∧
      Dynamic.ValuesHaveTypes header.function.context before arguments header.types := by
  rcases callableTyped.global_inv with ordinary | staged
  · rcases ordinary with ⟨typeEq, _valid, _evidence⟩
    obtain ⟨facts, certified⟩ := source_certificate sourceAt wellFormed
    have parameterEq := (TypeSystem.Ty.function.inj (typeEq.trans certified.callable_type)).1
    rw [parameterEq] at packedTyped
    have signatures := certified.signatures_eq.trans runtime.signatures.symm
    have bodyHeap := heapTyped.transportClosed signatures runtime.closed certified.type_parameters_empty
      runtime.variables_closed certified.residual_type_variables_open
    have bodyPacked := packedTyped.transportClosed signatures runtime.closed certified.type_parameters_empty
      runtime.variables_closed certified.residual_type_variables_open
    have length : arguments.length = header.types.length := arity.symm.trans
      ((congrArg List.length sourceAt.frame.parameters).trans certified.typing.inputs_extend.length_eq)
    have bodyArguments := packing.unpackTypes bodyPacked length
    exact ⟨sourceAt.frame.context.symm ▸ bodyHeap, sourceAt.frame.context.symm ▸ bodyArguments⟩
  · rcases staged with ⟨inner, impossible, innerTyped⟩
    cases impossible

end SourceAdmission
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds
