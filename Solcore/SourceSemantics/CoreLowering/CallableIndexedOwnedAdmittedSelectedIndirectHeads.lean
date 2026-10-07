import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedIndirectHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedIndirectSequence

/-! The actual literal formation receipt feeds admitted ordered arguments at its
same caller state. The original whole Source trace authenticates successful
value and heap typing at the exact returned witness. Faults retain their real
post and all-row stability. No uniform admission or execution law is supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedSelectedIndirectHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedLambdaNestedRuntimeBodyMeaning
open CallableIndexedOwnedIndirectExpressionHeads CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedSelectedIndirectHeads CallableIndexedOwnedSourceAdmission
open RecursiveNamedCatalogInvocationBounds (Below)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : CallableIndexedOwnedFunctionValues.Header compiled program)
  (prefixZero : owner.key.capturePrefix = 0)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (head : Receipt (headers := headers) (registry := registry) (faults := faults)
    (source := source) (context := context) (evidence := evidence) caller certificate scope id lowered)
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {canonical actual : Environment} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {ξ : Renaming}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (initial : callerProtocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller _ (bridge.pool initial))
  (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)

include prefixZero complete globals slots related agrees typed stored in
/-- Admitted arguments consume the actual literal callee post. The original
whole Source derivation supplies successful value and heap typing at the exact
returned caller witness, with stable rows retained for either outcome. -/
theorem preserves_bounded
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (admitted : Admission bridge context initial)
    (parentTyped : ExpressionHasType source context id head.compiler.original.type)
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
    (budget : Nat)
    (arguments : Below budget (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      context evidence source certificate faults))
    (bodies : SourceContinuations (source := source) (context := context) (evidence := evidence)
      (environment := environment) (ids := head.ids) profile (formedReceipt owner caller prefixZero profile complete globals slots head bridge initial packet related agrees typed stored) (head.selected environment).escaped bridge initial budget)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment heap id outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld head.compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        PostAdmission bridge context head.compiler.original.type outcome reached := by
  obtain ⟨calleeSize, argumentsSize, callSize, calleeTrace, suffix, calleeSmall, argumentsSmall, callWithin⟩ :=
    suffix_of_source head.compiler.found head.compiler.originalForm head.parent.coercions
      head.compiler.argumentCoercions head.parent.arity head.lambda unique wellFormed runtime covers locals admitted.heap
      head.sourceArguments head.sourceCount trace
  rw [head.function_eq] at calleeTrace suffix
  obtain ⟨sourceCallee, nativeCallee⟩ := formed_receipts owner caller prefixZero profile complete globals slots head
    bridge initial packet related agrees typed stored
  have captures : FunctionValues.SourceCapturesValid heap (.closure (formed head.formation environment)) := locals
  let selected := head.selected environment
  obtain ⟨sourceSize, value, finalStore, finalMap, finalWorld, sourceParent, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, relatedPost⟩ :=
    preserves_bounded_with_sequence profile head.compiler head.prepared head.parent (formedReceipt owner caller prefixZero profile complete globals slots head bridge initial packet related agrees typed stored)
      selected.nativeTypes selected.escaped selected.rawResult selected.nativeResult
      locals captures wellFormed runtime covers admitted.heap head.sourceArguments head.sourceCount
      bridge initial admitted.rows budget
      (CallableIndexedOwnedAdmittedIndirectSequence.preserves profile (formedReceipt owner caller prefixZero profile complete globals slots head bridge initial packet related agrees typed stored)
        selected.children unique head.sourceArguments related heaps locals agrees typed bridge initial admitted budget arguments)
      bodies initial (ProtectedStateTransition.Protocol.refl callerProtocol initial) (.refl _) (.refl _) (.refl _ _) (.refl _)
      calleeTrace nativeCallee selected.stageAccepted selected.arityAccepted suffix
      (Nat.le_trans (Nat.le_of_lt argumentsSmall) within) (Nat.le_trans callWithin within)
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, relatedPost,
    after_expression_sized initial reached admitted wellFormed runtime covers locals parentTyped trace frame⟩

include prefixZero complete globals slots related agrees typed stored in
/-- Native reflection uses the authentic emitted literal and admitted argument
sequence. Its independently graded whole Source trace authenticates successful
admission at the exact returned caller witness. -/
theorem reflects_bounded
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (admitted : Admission bridge context initial)
    (parentTyped : ExpressionHasType source context id head.compiler.original.type)
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
    (budget : Nat)
    (arguments : Below budget (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      context evidence source certificate faults))
    (bodies : NativeContinuations (source := source) (context := context) (evidence := evidence)
      (environment := environment) (ids := head.ids) profile (formedReceipt owner caller prefixZero profile complete globals slots head bridge initial packet related agrees typed stored) (head.selected environment).escaped bridge initial budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment heap id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld head.compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        PostAdmission bridge context head.compiler.original.type outcome reached := by
  obtain ⟨sourceCallee, nativeCallee⟩ := formed_receipts owner caller prefixZero profile complete globals slots head
    bridge initial packet related agrees typed stored
  obtain ⟨calleeSize, calleeTrace⟩ := SourceExecutionSize.ExpressionEvaluates.has_size sourceCallee
  have captures : FunctionValues.SourceCapturesValid heap (.closure (formed head.formation environment)) := locals
  let selected := head.selected environment
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, relatedPost⟩ :=
    reflects_bounded_with_sequence profile head.compiler head.prepared head.parent (formedReceipt owner caller prefixZero profile complete globals slots head bridge initial packet related agrees typed stored)
      selected.nativeTypes selected.escaped selected.rawResult selected.nativeResult
      locals captures wellFormed runtime covers admitted.heap head.sourceArguments head.sourceCount
      bridge initial admitted.rows budget
      (CallableIndexedOwnedAdmittedIndirectSequence.reflects profile (formedReceipt owner caller prefixZero profile complete globals slots head bridge initial packet related agrees typed stored)
        selected.children unique head.sourceArguments related heaps locals agrees typed bridge initial admitted budget arguments)
      bodies initial (ProtectedStateTransition.Protocol.refl callerProtocol initial) (.refl _) (.refl _) (.refl _ _) (.refl _)
      calleeTrace nativeCallee selected.stageAccepted selected.arityAccepted completed within
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, relatedPost,
    after_expression_sized initial reached admitted wellFormed runtime covers locals parentTyped trace frame⟩

/-- This carrier projects only slot proofs; it retains the complete actual
nested packet pool and its receipt-aware return operation. -/
def nestedBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True)
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller) :=
  CallableIndexedOwnedIndirectCallerProtocol.forget_slots
    (CallableIndexedOwnedNestedCallerProtocol.carrier owner caller)

/-- A body continuation obligation is asked only at the authentic literal
producer and its real admitted input. The shared mutual closer can supply its
strict body children without a universal arbitrary closure representation. -/
def SourceBodiesAt (budget : Nat) : Prop :=
  ∀ {childScope childId childLowered},
  ∀ head : Receipt (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) caller certificate childScope childId childLowered,
  ∀ {mapping world administrative environment canonical actual actualContext heap store ξ},
  ∀ (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative childScope environment canonical compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) mapping world heap store)
    (_locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State
      ⟨childScope, mapping, world, heap, store, canonical⟩),
    Admission (nestedBridge (headers := headers) owner caller) context initial →
    SourceContinuations (source := source) (context := context) (evidence := evidence)
      (environment := environment) (ids := head.ids) profile
      (formedReceipt owner caller prefixZero profile complete globals slots head
        (nestedBridge (headers := headers) owner caller) initial initial.property related agrees typed heaps.runtime_hasTypes)
      (head.selected environment).escaped (nestedBridge (headers := headers) owner caller) initial budget

/-- Native continuation obligations retain the same actual producer/input and
its original parameter prefix. Their Source grade remains independent. -/
def NativeBodiesAt (budget : Nat) : Prop :=
  ∀ {childScope childId childLowered},
  ∀ head : Receipt (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) caller certificate childScope childId childLowered,
  ∀ {mapping world administrative environment canonical actual actualContext heap store ξ},
  ∀ (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative childScope environment canonical compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) mapping world heap store)
    (_locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State
      ⟨childScope, mapping, world, heap, store, canonical⟩),
    Admission (nestedBridge (headers := headers) owner caller) context initial →
    NativeContinuations (source := source) (context := context) (evidence := evidence)
      (environment := environment) (ids := head.ids) profile
      (formedReceipt owner caller prefixZero profile complete globals slots head
        (nestedBridge (headers := headers) owner caller) initial initial.property related agrees typed heaps.runtime_hasTypes)
      (head.selected environment).escaped (nestedBridge (headers := headers) owner caller) initial budget

/-- The existing admitted Tree head callback consumes its actual input
admission. The literal receipt selects one authentic formed producer, and all
argument/body effects are returned with the identical final packet witness. -/
theorem head_preserves_at
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source) (size : Nat)
    (arguments : Below size (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (nestedBridge (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      context evidence source certificate faults))
    (bodies : SourceBodiesAt (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) (certificate := certificate) owner caller prefixZero profile complete globals slots size) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (nestedBridge (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      context evidence source
      (Head (headers := headers) (registry := registry) (faults := faults)
        (source := source) (context := context) (evidence := evidence) caller certificate) faults size := by
  intro childScope childId childLowered certified node found parentTyped mapping world administrative environment canonical actual actualContext
    heap store ξ outcome after environments heaps locals agrees typed initial admitted trace
  obtain ⟨head⟩ := certified
  have same := Option.some.inj (head.compiler.found.symm.trans found)
  subst node
  exact preserves_bounded owner caller prefixZero profile complete globals slots head
    (nestedBridge (headers := headers) owner caller) initial initial.property environments agrees typed heaps.runtime_hasTypes
    heaps locals admitted parentTyped wellFormed runtime covers unique size arguments
    (bodies head environments heaps locals agrees typed initial admitted) trace (Nat.le_refl size)

/-- Native completion returns the same packet and an independently graded
whole Source trace with successful admission at that actual post. -/
theorem head_reflects_at
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source) (size : Nat)
    (arguments : Below size (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (nestedBridge (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      context evidence source certificate faults))
    (bodies : NativeBodiesAt (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) (certificate := certificate) owner caller prefixZero profile complete globals slots size) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (nestedBridge (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      context evidence source
      (Head (headers := headers) (registry := registry) (faults := faults)
        (source := source) (context := context) (evidence := evidence) caller certificate) faults size := by
  intro childScope childId childLowered certified node found parentTyped mapping world administrative environment canonical actual actualContext
    heap store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  obtain ⟨head⟩ := certified
  have same := Option.some.inj (head.compiler.found.symm.trans found)
  subst node
  exact reflects_bounded owner caller prefixZero profile complete globals slots head
    (nestedBridge (headers := headers) owner caller) initial initial.property environments agrees typed heaps.runtime_hasTypes
    heaps locals admitted parentTyped wellFormed runtime covers unique size arguments
    (bodies head environments heaps locals agrees typed initial admitted) completed (Nat.le_refl size)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedSelectedIndirectHeads
