import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.ExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallEvidence
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateForPost
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LoopAndMatchBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StageCalls
import Solcore.SourceSemantics.Staging.RecursiveErasure
import Solcore.SourceSemantics.Staging.RecursiveTraceSize
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeIndirectCalls
import Solcore.SourceSemantics.CoreLowering.LoopRenaming
import Solcore.SourceSemantics.CoreLowering.ReachedBuiltinFragmentOutcomePorts

/-!
# Admitted staged profile: expressions and terminals

Staged expression bounds and sequences, terminal statements and bodies, and builtin faults.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBodyReadyBounds
/-! The shared ready body result supplies the actual returned state. Genuine
Source body execution establishes successful value typing at that same state;
faults keep all-row stable history. These finite adapters add no body fold. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBodyReadyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {condition : Location → NativeFrame → Prop}
  {origin : CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  (wellFormed : ProgramWellFormed program)
  (syntaxTree : GenericImperativeMatch.Syntax origin.function.source origin.expressionSyntax
    origin.context (.statements true origin.function.body) origin.function.resultType)

include wellFormed syntaxTree in
/-- A genuine body trace adds successful Source typing to the same actual
ready finish witness supplied by the shared callee proof. -/
theorem preserves_at {size : Nat}
    (meaning : CallableRuntimeBodyReadyOrigins.PreservesAt callerProtocol (readiness bridge) condition
      (ProtectedStateImperativeTypedSourceSites.Facts origin.function.source origin.expressionSyntax)
      functions program origin size) :
    CallableIndexedOwnedAdmittedBodyEntries.PreservesAt bridge
      (condition := condition) (origin := origin) (functions := functions) size := by
  intro entry outcome after trace
  let readyEntry := CallableIndexedOwnedBodyReadyEntries.entry bridge entry syntaxTree
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related, _ready⟩ := meaning readyEntry trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds,
    frame, metadata, exit, reached, related,
    CallableIndexedOwnedAdmittedBodyEntries.after_body bridge wellFormed entry reached trace frame⟩

include wellFormed syntaxTree in
/-- The original native completion yields an independently graded Source
trace, which authenticates admission at the exact returned state. -/
theorem reflects_at {size : Nat}
    (meaning : CallableRuntimeBodyReadyOrigins.ReflectsAt callerProtocol (readiness bridge) condition
      (ProtectedStateImperativeTypedSourceSites.Facts origin.function.source origin.expressionSyntax)
      functions program origin size) :
    CallableIndexedOwnedAdmittedBodyEntries.ReflectsAt bridge
      (condition := condition) (origin := origin) (functions := functions) size := by
  intro entry value finalStore completed
  let readyEntry := CallableIndexedOwnedBodyReadyEntries.entry bridge entry syntaxTree
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
      frame, metadata, exit, reached, related, _ready⟩ := meaning readyEntry completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, exit, reached, related,
    CallableIndexedOwnedAdmittedBodyEntries.after_body bridge wellFormed entry reached trace frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBodyReadyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedSequenceHeads
/-! Tuple and contracted builtin heads use admitted children through one whole
ordered sequence at the actual caller input. The genuine parent Source typing
provides an independent operand row. Successful whole execution establishes
admission at the identical reached witness; faults retain stable rows. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedSequenceHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open ProtectedStateExpressionOperandTyping
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (evidence : Dynamic.EvidenceEnvironment)
  {children : GenericExpressionMeaning.Certificate} {faults : FunctionCalls.FaultRep}
  (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)

include wellFormed runtime covers unique

namespace Tuple

theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source children faults childSize) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source (CompatibleExpressionTuples.Certificate values source children) faults size := by
  intro scope id lowered certified
  obtain ⟨node, ids, types, codes, emitted, receipt, sequence⟩ := certified
  subst lowered
  intro root found parentTyped mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  have same := Option.some.inj (receipt.metadata.found.symm.trans found)
  subst root
  obtain ⟨originalTypes, typing⟩ := operand_types unique receipt.metadata.found parentTyped
  have argumentsTyped : ExpressionsHaveTypes source context ids originalTypes := by
    simpa only [receipt.form, actualOperandIds] using typing
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    RecursiveNamedTupleHeadBounds.Stateful.preserves_bounded_with_sequence functions program evidence callerProtocol
      budget size within unique receipt initial
      (CallableIndexedOwnedAdmittedSequenceProducer.preserves bridge initial admitted sequence unique argumentsTyped
        environments heaps locals agrees actualTyped (budget + 1) (fun n bound => meaning n (by omega))) trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed runtime covers locals parentTyped trace frame⟩

theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source children faults childSize) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source (CompatibleExpressionTuples.Certificate values source children) faults size := by
  intro scope id lowered certified
  obtain ⟨node, ids, types, codes, emitted, receipt, sequence⟩ := certified
  subst lowered
  intro root found parentTyped mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted evaluated
  have same := Option.some.inj (receipt.metadata.found.symm.trans found)
  subst root
  obtain ⟨originalTypes, typing⟩ := operand_types unique receipt.metadata.found parentTyped
  have argumentsTyped : ExpressionsHaveTypes source context ids originalTypes := by
    simpa only [receipt.form, actualOperandIds] using typing
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    RecursiveNamedTupleHeadBounds.Stateful.reflects_bounded_with_sequence functions program evidence callerProtocol
      budget size within receipt initial
      (CallableIndexedOwnedAdmittedSequenceProducer.reflects bridge initial admitted sequence unique argumentsTyped
        environments heaps locals agrees actualTyped (budget + 1) (fun n bound => meaning n (by omega))) evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed runtime covers locals parentTyped trace frame⟩
end Tuple

namespace Builtin
open BuiltinCalls BuiltinCalls.Protocol
open GenericExpressionMeaning (agree_prefix)
variable {identities : Dynamic.Value → Word → Prop}
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)

include functionLeaves in
theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source children faults childSize) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source (BuiltinCalls.Typed.Head values source children) faults size := by
  intro scope id lowered tree
  cases tree with
  | @contracted callee arguments function node codes identity contract unknown metadata form sourceType sequence nativeTypes =>
    intro root found parentTyped mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped initial admitted trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨originalTypes, typing⟩ := operand_types unique metadata.found parentTyped
    have argumentsTyped : ExpressionsHaveTypes source context arguments originalTypes := by
      simpa only [form, actualOperandIds] using typing
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related⟩ :=
      RecursiveNamedBuiltinHeadBounds.Stateful.Head.preserves_bounded_with_sequence functions functionLeaves
        program evidence unique callerProtocol budget size within metadata form sourceType nativeTypes initial
        (CallableIndexedOwnedAdmittedSequenceProducer.preserves bridge initial admitted sequence unique argumentsTyped
          environments heaps locals
          (agree_prefix (agree_prefix agrees (contractedValue function identity contract actual)) .unit)
          (RecursiveNamedBuiltinHeadBounds.Stateful.prefixed_typed actualTyped function identity contract)
          (budget + 1) (fun n bound => meaning n (by omega))) trace
    exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related,
      after_expression_sized initial reached admitted wellFormed runtime covers locals parentTyped trace frame⟩

include functionLeaves in
theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (meaning : ∀ childSize, childSize ≤ budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source children faults childSize) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source (BuiltinCalls.Typed.Head values source children) faults size := by
  intro scope id lowered tree
  cases tree with
  | @contracted callee arguments function node codes identity contract unknown metadata form sourceType sequence nativeTypes =>
    intro root found parentTyped mapping world administrative environment canonical actual actualContext before store ξ result finalStore
      environments heaps locals agrees actualTyped initial admitted completed
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨originalTypes, typing⟩ := operand_types unique metadata.found parentTyped
    have argumentsTyped : ExpressionsHaveTypes source context arguments originalTypes := by
      simpa only [form, actualOperandIds] using typing
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related⟩ :=
      RecursiveNamedBuiltinHeadBounds.Stateful.Head.reflects_bounded_with_sequence functions functionLeaves
        program evidence callerProtocol budget size within metadata form sourceType nativeTypes initial
        (CallableIndexedOwnedAdmittedSequenceProducer.reflects bridge initial admitted sequence unique argumentsTyped
          environments heaps locals
          (agree_prefix (agree_prefix agrees (contractedValue function identity contract actual)) .unit)
          (RecursiveNamedBuiltinHeadBounds.Stateful.prefixed_typed actualTyped function identity contract)
          (budget + 1) (fun n bound => meaning n (by omega))) completed
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related,
      after_expression_sized initial reached admitted wellFormed runtime covers locals parentTyped trace frame⟩
end Builtin
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedSequenceHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionCallsHeads
/-! Genuine parent Source typing and actual input admission select the existing
head producers. Each branch returns its own actual reached witness and post
admission. Calls retain an explicit producer for their authentic certificate;
this dispatcher adds no body-family closure or execution induction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionCallsHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {certificate : GenericExpressionMeaning.Certificate} {faults : FunctionCalls.FaultRep}
  {reasonAt : ExpressionId → Word}
  (unique : NodeOccurrencesUnique source)
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context)

include transport extension faithful functionLeaves functionTypes unique missing wellFormed runtime covers

theorem preserves_at_with_calls
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source certificate faults child)
    (callMeaning : CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source (calls certificate) faults size) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source
      (CompatibleExpressionCalls.Head calls (.initial compiled.compatible.checked) source context reasonAt certificate)
      faults size := by
  intro scope id lowered head node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  change ProtectedStateExpressionCallsHeads.WithFacts.PreservesResult
    (registry := registry) (faults := faults) functions callerProtocol
    (fun node outcome {_} reached => PostAdmission bridge context node.type outcome reached) initial node lowered actual ξ outcome after
  refine ProtectedStateExpressionCallsHeads.WithFacts.head_preserves_at_with_providers
    (functions := functions) (evidence := evidence) (stateProtocol := callerProtocol)
    (post := fun node outcome {_} reached => PostAdmission bridge context node.type outcome reached)
    (facts := fun _ id _ node => ExpressionHasType source context id node.type)
    (ready := Admission bridge context) (calls := calls)
    found initial ?_ ?_ ?_ ?_ ?_ head sourceTyped admitted trace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact CallableIndexedOwnedAdmittedCompositionsBounds.preserves_at bridge functions budget size within
      unique wellFormed runtime covers children branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact CallableIndexedOwnedAdmittedDataHeadBounds.preserves_at (calls := calls)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      bridge transport functions extension faithful functionLeaves functionTypes missing budget size within
      unique wellFormed runtime covers children branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact CallableIndexedOwnedAdmittedSequenceHeads.Builtin.preserves_at
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      bridge functions evidence wellFormed runtime covers unique functionLeaves budget size within children branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact CallableIndexedOwnedAdmittedSequenceHeads.Tuple.preserves_at
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      bridge functions evidence wellFormed runtime covers unique budget size within children branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact callMeaning branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace

theorem reflects_at_with_calls
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source certificate faults child)
    (callMeaning : CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source (calls certificate) faults size) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source
      (CompatibleExpressionCalls.Head calls (.initial compiled.compatible.checked) source context reasonAt certificate)
      faults size := by
  intro scope id lowered head node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted trace
  change ProtectedStateExpressionCallsHeads.WithFacts.ReflectsResult (program := program) (source := source) (context := context)
    (registry := registry) (faults := faults) functions evidence callerProtocol
    (fun node outcome {_} reached => PostAdmission bridge context node.type outcome reached) initial node id lowered environment value finalStore
  refine ProtectedStateExpressionCallsHeads.WithFacts.head_reflects_at_with_providers
    (functions := functions) (evidence := evidence) (stateProtocol := callerProtocol)
    (post := fun node outcome {_} reached => PostAdmission bridge context node.type outcome reached)
    (facts := fun _ id _ node => ExpressionHasType source context id node.type)
    (ready := Admission bridge context) (calls := calls)
    found initial ?_ ?_ ?_ ?_ ?_ head sourceTyped admitted trace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact CallableIndexedOwnedAdmittedCompositionsBounds.reflects_at bridge functions budget size within
      unique wellFormed runtime covers children branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact CallableIndexedOwnedAdmittedDataHeadBounds.reflects_at (calls := calls)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      bridge transport functions extension faithful functionLeaves functionTypes missing budget size within
      unique wellFormed runtime covers children branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact CallableIndexedOwnedAdmittedSequenceHeads.Builtin.reflects_at
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      bridge functions evidence wellFormed runtime covers unique functionLeaves budget size within children branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact CallableIndexedOwnedAdmittedSequenceHeads.Tuple.reflects_at
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      bridge functions evidence wellFormed runtime covers unique budget size within children branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact callMeaning branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionCallsHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds
/-! Graded interfaces and concrete admission adapters for the supported
recursive staged Source profile. Compiler producers use actual static receipts
and strict child hypotheses. Ordinary outcomes retain the original caller
PostAdmission. Stage failures keep their exact tag and scope and stable rows
at the same reached state. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission (Admission)
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (context : SourceSemantics.Context)

/-- The receipt is indexed by the actual reached state. A stage failure is
never projected to an ordinary Dynamic fault or given deep heap typing. -/
def PostAdmission (type : TypeSystem.Ty) (outcome : Staging.Recursive.Outcome)
    {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index) : Prop :=
  match outcome with
  | .value value =>
      CallableIndexedOwnedSourceAdmission.PostAdmission bridge context type (.value value) reached
  | .fault (.semantic reason) =>
      CallableIndexedOwnedSourceAdmission.PostAdmission bridge context type (.fault reason) reached
  | .fault (.stage _ _ _) => StableRows (bridge.pool reached)

variable {bridge context}

/-- Sequential successful children consume the original actual caller receipt
at precisely the reached heap and store. -/
theorem PostAdmission.at_value {type : TypeSystem.Ty} {value : Dynamic.Value}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : PostAdmission bridge context type (.value value) reached) :
    Dynamic.ValueHasType context index.heap value type ∧ Admission bridge context reached :=
  CallableIndexedOwnedSourceAdmission.PostAdmission.at_value post

theorem PostAdmission.rows {type : TypeSystem.Ty} {outcome : Staging.Recursive.Outcome}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : PostAdmission bridge context type outcome reached) : StableRows (bridge.pool reached) := by
  cases outcome with
  | value value => exact CallableIndexedOwnedSourceAdmission.PostAdmission.rows post
  | fault failure =>
    cases failure with
    | semantic reason => exact CallableIndexedOwnedSourceAdmission.PostAdmission.rows post
    | stage origin call reason => exact post

/-- A propagated fault keeps its exact tag and actual endpoint when the
enclosing expression has another type. Semantic success is impossible; stage
stability is the same receipt. Neither case adds deep heap typing. -/
theorem PostAdmission.at_fault_type {firstType lastType : TypeSystem.Ty}
    {failure : Staging.Recursive.Failure}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : PostAdmission bridge context firstType (.fault failure) reached) :
    PostAdmission bridge context lastType (.fault failure) reached := by
  cases failure with
  | semantic reason =>
    change CallableIndexedOwnedSourceAdmission.PostAdmission bridge context firstType (.fault reason) reached at post
    change CallableIndexedOwnedSourceAdmission.PostAdmission bridge context lastType (.fault reason) reached
    exact ⟨post.rows, by intro value same; cases same⟩
  | stage origin call reason => exact post

/-- The concrete graded Source trace authenticates only its ordinary successful
branch. Stability comes from both genuine endpoint pools and the exact actual
administrative frame. This theorem neither constructs nor substitutes a state. -/
theorem after_expression_sized {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    (admitted : Admission bridge context first)
    {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {environment : Dynamic.Environment} {id : ExpressionId} {type : TypeSystem.Ty}
    {outcome : Staging.Recursive.Outcome} {size : Nat}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
    (covers : invocation.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (typed : ExpressionHasType invocation.source context id type)
    (trace : Staging.Recursive.Size.Expression program registry size invocation context environment
      initial.heap id outcome reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    PostAdmission bridge context type outcome last := by
  cases outcome with
  | value value =>
    exact CallableIndexedOwnedSourceAdmission.after_expression first last admitted wellFormed runtime covers
      locals typed (.value trace.sound.value_plain) frame
  | fault failure =>
    cases failure with
    | semantic reason =>
      exact CallableIndexedOwnedSourceAdmission.after_expression first last admitted wellFormed runtime covers
        locals typed (.fault trace.sound.semanticFault_plain) frame
    | stage origin call reason =>
      exact StableRows.after_administrative (bridge.pool first) (bridge.pool last) admitted.rows frame

/-- Retain the producer's exact reached witness and its concrete record
relation when adding admission. Transient callee/argument effects remain in
reached.heap/reached.store and in the same dependent caller state. -/
theorem after_related_expression_sized {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    (related : callerProtocol.Relates first last)
    (admitted : Admission bridge context first)
    {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {environment : Dynamic.Environment} {id : ExpressionId} {type : TypeSystem.Ty}
    {outcome : Staging.Recursive.Outcome} {size : Nat}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
    (covers : invocation.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (typed : ExpressionHasType invocation.source context id type)
    (trace : Staging.Recursive.Size.Expression program registry size invocation context environment
      initial.heap id outcome reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    callerProtocol.Relates first last ∧ PostAdmission bridge context type outcome last :=
  ⟨related, after_expression_sized first last admitted wellFormed runtime covers locals typed trace frame⟩

section Expressions
variable (bridge) (context)
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (certificate : GenericExpressionMeaning.Certificate) (faults : RecursiveStageMeaning.FaultRep)

/-- Source size is the grade of the genuine staged trace. -/
def PreservesAt (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, invocation.source.lookupExpression? id = some node →
    ExpressionHasType invocation.source context id node.type →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    Staging.Recursive.Size.Expression program registry size invocation context environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.type outcome reached

/-- Native size is measured independently; reflection returns the actual
Source grade and the exact staged outcome, including a nested failing scope. -/
def ReflectsAt (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, invocation.source.lookupExpression? id = some node →
    ExpressionHasType invocation.source context id node.type →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program registry sourceSize invocation context environment before id outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.type outcome reached

def PreservesAtMost (budget : Nat) : Prop :=
  ∀ size, size ≤ budget → PreservesAt bridge context model registry invocation certificate faults size

def PreservesBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → PreservesAt bridge context model registry invocation certificate faults size

def ReflectsBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → ReflectsAt bridge context model registry invocation certificate faults size

end Expressions
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionSequence
/-! Ordered staged arguments are constructed from the actual compiler Tree
and strictly smaller expression results. Each successful child passes its
actual reached caller state to the next child. Both failure tags retain the
same originating scope, token and final state. Native reflection reconstructs
an independent Source grade from the original packed-helper computation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionSequence
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open DataPatternValues DataExpressionSequence
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

/-- Stable rows belong to the actual returned pool. Only a successful argument
list supplies the deep admission needed by a following application. -/
structure PostAdmission (outcome : Staging.Recursive.ValuesOutcome)
    {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index) : Prop where
  rows : StableRows (bridge.pool reached)
  successful : ∀ values, outcome = .values values → Admission bridge context reached

theorem PostAdmission.at_values {values : List Dynamic.Value}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : PostAdmission bridge (context := context) (.values values) reached) :
    Admission bridge context reached := post.successful values rfl

private def MemberTyping (ids : List ExpressionId) : Prop :=
  ∀ id, id ∈ ids → ∀ node, invocation.source.lookupExpression? id = some node →
    ExpressionHasType invocation.source context id node.type

private theorem member_typing {ids : List ExpressionId} {types : List TypeSystem.Ty}
    (unique : NodeOccurrencesUnique invocation.source)
    (typing : ExpressionsHaveTypes invocation.source context ids types) :
    MemberTyping (context := context) (invocation := invocation) ids := by
  intro id member node found
  exact CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typing member found

variable {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
  {sourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}

private theorem preserves_values_with_members (budget : Nat)
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (sourceTyped : MemberTyping (context := context) (invocation := invocation) ids)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial) {size : Nat}
    (execution : Staging.Recursive.Size.Expressions program registry size invocation context environment
      before ids (.values sources) after) (within : size ≤ budget) :
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) (.values sources) reached := by
  induction tree generalizing size mapping world actual actualContext before store ξ sources after with
  | nil =>
      cases execution
      exact ⟨[], store, mapping, world, .inRight .unit, .nil, heaps,
        .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial,
        admitted.rows, fun _ _ => admitted⟩
  | single found generated =>
      cases execution with
      | cons head tail =>
          cases tail
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
              maps, worlds, frame, metadata, reached, related, post⟩ :=
            children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within)
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted head
          cases represented with
          | value payload =>
              exact ⟨[_], finalStore, finalMap, finalWorld, evaluated, .cons payload .nil,
                finalHeaps, maps, worlds, frame, metadata, reached, related, post.rows,
                fun _ _ => post.at_value.2⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
      cases execution with
      | cons head rest =>
          obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
            children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within)
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted head
          cases represented with
          | @value sourceValue coreValue payload =>
              obtain ⟨values, finalStore, finalMap, finalWorld, second, restRep, finalHeaps,
                  maps, worlds, frame, metadata, reached, related, post⟩ :=
                ih (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
                  (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                  (agree_prefix layout coreValue)
                  (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                  middleState firstPost.at_value.2 rest
                  (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
              have nonempty : values ≠ [] := by
                intro absent
                have lengths := restRep.length.2
                simp [absent] at lengths
              refine ⟨coreValue :: values, finalStore, finalMap, finalWorld, ?_,
                .cons (model.extend payload maps worlds) restRep, finalHeaps,
                firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
                reached, callerProtocol.trans firstRelated related, post.rows, fun _ _ => post.at_values⟩
              rw [rename_prefix] at second
              have combined := LocalSequence.pair_success lowered.type
                (SourceCoreCalls.packArguments (nextCode :: codes)).type first second
              simpa [SourceCoreCalls.packArguments, pair_rename, packValues, nonempty] using combined

private theorem preserves_fault_with_members (budget : Nat)
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (sourceTyped : MemberTyping (context := context) (invocation := invocation) ids)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {failure : Staging.Recursive.Failure}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial) {size : Nat}
    (execution : Staging.Recursive.Size.Expressions program registry size invocation context environment
      before ids (.fault failure) after) (within : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults failure token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) (.fault failure) reached := by
  induction tree generalizing size mapping world actual actualContext before store ξ after with
  | nil => cases execution
  | single found generated =>
      cases execution with
      | headFault failed =>
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
              maps, worlds, frame, metadata, reached, related, post⟩ :=
            children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within)
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted failed
          cases represented with
          | fault matched =>
              exact ⟨_, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
                maps, worlds, frame, metadata, reached, related, post.rows, by intro _ impossible; cases impossible⟩
      | tailFault _ failed => cases failed
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
      cases execution with
      | headFault failed =>
          obtain ⟨value, finalStore, finalMap, finalWorld, first, represented, finalHeaps,
              maps, worlds, frame, metadata, reached, related, post⟩ :=
            children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within)
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted failed
          cases represented with
          | fault matched =>
              refine ⟨_, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps,
                maps, worlds, frame, metadata, reached, related, post.rows, by intro _ impossible; cases impossible⟩
              simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_left_failure lowered.type
                (SourceCoreCalls.packArguments (nextCode :: codes)).type first
      | tailFault head failed =>
          obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
            children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within)
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted head
          cases represented with
          | @value sourceValue coreValue payload =>
              obtain ⟨token, finalStore, finalMap, finalWorld, second, matched, finalHeaps,
                  maps, worlds, frame, metadata, reached, related, post⟩ :=
                ih (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
                  (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                  (agree_prefix layout coreValue)
                  (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                  middleState firstPost.at_value.2 failed
                  (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
              refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps,
                firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
                reached, callerProtocol.trans firstRelated related, post⟩
              rw [rename_prefix] at second
              simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_right_failure lowered.type
                (SourceCoreCalls.packArguments (nextCode :: codes)).type first second

/-- Actual list typing supplies each used child's stored type. The successful
prefix retains the same cumulative caller records at every reached state. -/
theorem preserves_values (budget : Nat) (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    {originalTypes : List TypeSystem.Ty} (unique : NodeOccurrencesUnique invocation.source)
    (typing : ExpressionsHaveTypes invocation.source context ids originalTypes) :
    ∀ (_children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    {mapping world administrativeContext actualContext environment canonical actual before after store ξ sources},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial → ∀ {size},
    Staging.Recursive.Size.Expressions program registry size invocation context environment before ids (.values sources) after →
    size ≤ budget →
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) (.values sources) reached :=
  preserves_values_with_members bridge budget tree (member_typing unique typing)

/-- A failing argument stops the original helper at the same reached caller
pool; no later argument runs and neither failure tag is relabeled. -/
theorem preserves_fault (budget : Nat) (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    {originalTypes : List TypeSystem.Ty} (unique : NodeOccurrencesUnique invocation.source)
    (typing : ExpressionsHaveTypes invocation.source context ids originalTypes) :
    ∀ (_children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    {mapping world administrativeContext actualContext environment canonical actual before after store ξ failure},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial → ∀ {size},
    Staging.Recursive.Size.Expressions program registry size invocation context environment before ids (.fault failure) after →
    size ≤ budget →
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults failure token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) (.fault failure) reached :=
  preserves_fault_with_members bridge budget tree (member_typing unique typing)

private theorem reflects_with_members (budget : Nat)
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (sourceTyped : MemberTyping (context := context) (invocation := invocation) ids)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model registry invocation certificate faults budget)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial) {size : Nat}
    (evaluated : EvaluationSize size actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
      value finalStore) (within : size < budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expressions program registry sourceSize invocation context environment before ids outcome after ∧
      RecursiveStageArguments.ResultFor model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) outcome reached := by
  induction tree generalizing size mapping world actual actualContext before store ξ value finalStore with
  | nil =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (show Evaluates actual store
        ((SourceCoreCalls.packArguments []).expression.rename ξ) (.inRight .word .unit) store from .inRight .unit)
      exact ⟨_, .values [], before, mapping, world, .nil, .values (values := []) .nil, heaps,
        .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial,
        admitted.rows, fun _ _ => admitted⟩
  | single found generated =>
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
          maps, worlds, frame, metadata, reached, related, post⟩ :=
        children _ within generated found (sourceTyped _ (by simp) _ found)
          environments heaps locals layout actualTyped initial admitted evaluated
      cases represented with
      | value payload =>
          exact ⟨_, .values [_], after, finalMap, finalWorld, .cons trace .nil,
            .values (values := [_]) (.cons payload .nil), finalHeaps, maps, worlds, frame, metadata,
            reached, related, post.rows, fun _ _ => post.at_value.2⟩
      | fault matched =>
          exact ⟨_, .fault _, after, finalMap, finalWorld, .headFault trace,
            .fault matched, finalHeaps, maps, worlds, frame, metadata,
            reached, related, post.rows, by intro _ impossible; cases impossible⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
      change EvaluationSize size actual store ((LocalSequence.pair lowered.type
        (SourceCoreCalls.packArguments (nextCode :: codes)).type lowered.expression
        (SourceCoreCalls.packArguments (nextCode :: codes)).expression).rename ξ) value finalStore at evaluated
      rw [pair_rename] at evaluated
      have complete := evaluated
      cases evaluated with
      | caseLeft first _ =>
          obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
              maps, worlds, frame, metadata, reached, related, post⟩ :=
            children _ (by omega) generated found (sourceTyped _ (by simp) _ found)
              environments heaps locals layout actualTyped initial admitted first
          cases represented with
          | fault matched =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                (LocalSequence.pair_left_failure lowered.type
                  (SourceCoreCalls.packArguments (nextCode :: codes)).type first.sound)
              exact ⟨_, .fault _, after, finalMap, finalWorld, .headFault trace, .fault matched,
                finalHeaps, maps, worlds, frame, metadata, reached, related, post.rows,
                by intro _ impossible; cases impossible⟩
      | caseRight first continuation =>
          obtain ⟨firstSize, outcome, middle, middleMap, middleWorld, firstTrace, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
            children _ (by omega) generated found (sourceTyped _ (by simp) _ found)
              environments heaps locals layout actualTyped initial admitted first
          cases represented with
          | @value sourceValue coreValue payload =>
              rename_i middleStore coreValue
              have nextLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical
                  (coreValue :: actual) := agree_prefix layout coreValue
              cases continuation with
              | caseLeft second _ =>
                  have shifted := second
                  rw [← rename_prefix] at shifted
                  obtain ⟨lastSize, outcome, after, finalMap, finalWorld, tailTrace, result, finalHeaps,
                      maps, worlds, frame, metadata, reached, related, post⟩ :=
                    ih (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
                      (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata) nextLayout
                      (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                      middleState firstPost.at_value.2 shifted (by omega)
                  cases result with
                  | fault matched =>
                      obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                        (LocalSequence.pair_right_failure lowered.type
                          (SourceCoreCalls.packArguments (nextCode :: codes)).type first.sound second.sound)
                      exact ⟨_, .fault _, after, finalMap, finalWorld, .tailFault firstTrace tailTrace, .fault matched,
                        finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                        firstFrame.trans frame, firstMetadata.trans metadata,
                        reached, callerProtocol.trans firstRelated related, post⟩
              | caseRight second _ =>
                  have shifted := second
                  rw [← rename_prefix] at shifted
                  obtain ⟨lastSize, outcome, after, finalMap, finalWorld, tailTrace, result, finalHeaps,
                      maps, worlds, frame, metadata, reached, related, post⟩ :=
                    ih (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
                      (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata) nextLayout
                      (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                      middleState firstPost.at_value.2 shifted (by omega)
                  cases result with
                  | @values sources values restRep =>
                      obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                        (LocalSequence.pair_success lowered.type
                          (SourceCoreCalls.packArguments (nextCode :: codes)).type first.sound second.sound)
                      have nonempty : values ≠ [] := by
                        intro absent
                        have lengths := restRep.length.2
                        simp [absent] at lengths
                      refine ⟨_, .values (sourceValue :: sources), after, finalMap, finalWorld,
                        .cons firstTrace tailTrace, ?_, finalHeaps,
                        firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
                        reached, callerProtocol.trans firstRelated related, post.rows, fun _ _ => post.at_values⟩
                      simpa [packValues, nonempty] using
                        RecursiveStageArguments.ResultFor.values (codes := lowered :: nextCode :: codes)
                          (.cons (model.extend payload maps worlds) restRep)

/-- Original packed-helper inversion supplies strict native child bounds.
Each reflected Source child contributes its own independent list grade. -/
theorem reflects (budget : Nat) (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    {originalTypes : List TypeSystem.Ty} (unique : NodeOccurrencesUnique invocation.source)
    (typing : ExpressionsHaveTypes invocation.source context ids originalTypes) :
    ∀ (_children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model registry invocation certificate faults budget)
    {mapping world administrativeContext actualContext environment canonical actual before store finalStore ξ value},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial → ∀ {size},
    EvaluationSize size actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore →
    size < budget →
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expressions program registry sourceSize invocation context environment before ids outcome after ∧
      RecursiveStageArguments.ResultFor model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) outcome reached :=
  reflects_with_members bridge budget tree (member_typing unique typing)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionSequence
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTerminalStatements
/-! Staged return and tail-expression composition uses the original lexical
return helper and strict expression hypotheses. Each result keeps its actual
reached caller state. Native reflection reconstructs an independent staged
Source grade and never projects a nested stage failure to a semantic failure. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTerminalStatements
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

/-- These are the actual two terminal statement forms compiled by the lexical
statement algebra. The receipt contains only source occurrences and form. -/
inductive Head (invocation : Staging.Recursive.Scope) (expression : ExpressionId) : List StatementId → Prop where
  | returning {id node} (rest : List StatementId)
      (contains : ContainsStatement invocation.source id node)
      (form : node.form = .returnStmt (some expression)) : Head invocation expression (id :: rest)
  | tail {id node} (contains : ContainsStatement invocation.source id node)
      (form : node.form = .expression expression false) : Head invocation expression [id]

def control (outcome : Staging.Recursive.Outcome) : Staging.Recursive.BodyOutcome :=
  match outcome with
  | .value value => .returned value
  | .fault failure => .fault failure

/-- Both terminal forms propagate the same nested failure. A successful
expression becomes the real returned control outcome. -/
theorem Head.trace {expression : ExpressionId} {statements : List StatementId}
    (head : Head invocation expression statements)
    {size : Nat} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Staging.Recursive.Outcome}
    (child : Staging.Recursive.Size.Expression program registry size invocation context environment
      before expression outcome after) :
    Staging.Recursive.Size.Statements program registry (Staging.Recursive.Size.stepSize [size])
      invocation context environment before statements context (control outcome) after := by
  cases head with
  | returning rest contains form =>
    cases outcome with
    | value value => exact .returnValue contains form child
    | fault failure => exact .returnFault contains form child
  | tail contains form =>
    cases outcome with
    | value value => exact .tail contains form child
    | fault failure => exact .expressionFault contains form child

/-- The original control envelope retains the expression payload or exact
fault token. It introduces no fallthrough or additional execution. -/
inductive ResultRepresents (model : GenericHeap.PayloadModel catalog projects definitions)
    (mapping : LocationMap) (world : StoreTyping) (sourceType : TypeSystem.Ty)
    (type : Ty) (faults : RecursiveStageMeaning.FaultRep) :
    Staging.Recursive.Outcome → Value → Prop where
  | returned {source value} (payload : model.Represents mapping world sourceType source value type) :
      ResultRepresents model mapping world sourceType type faults (.value source) (LocalLoop.returnedValue value)
  | fault {failure token} (matched : faults failure token) :
      ResultRepresents model mapping world sourceType type faults (.fault failure)
        (.inLeft (LocalLoop.controlType type) (.word token))

section Terminal
variable {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId}
  {statements : List StatementId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  (head : Head invocation expression statements)
  (certified : certificate scope expression lowered)
  (found : invocation.source.lookupExpression? expression = some node)
  (sourceTyped : ExpressionHasType invocation.source context expression node.type)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
  (heaps : GenericHeap.HeapRepresents model mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

include head certified found sourceTyped environments heaps locals agrees typed admitted in
/-- The real parent step gives a strict expression grade. The expression IH
runs once and the existing return helper preserves its exact endpoint. -/
theorem preserves (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    {childSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment
      before expression outcome after)
    (within : Staging.Recursive.Size.stepSize [childSize] ≤ budget) :
    Staging.Recursive.Size.Statements program registry (Staging.Recursive.Size.stepSize [childSize])
      invocation context environment before statements context (control outcome) after ∧
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.returnValue lowered.type lowered.expression).rename ξ) value finalStore ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  have strict : childSize < budget :=
    Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (child := childSize)
      (children := [childSize]) (by simp)) within
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    children childSize strict certified found sourceTyped environments heaps locals agrees typed initial admitted child
  refine ⟨head.trace child, ?_⟩
  cases represented with
  | value payload =>
    exact ⟨_, finalStore, finalMap, finalWorld,
      by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_success _ evaluated,
      .returned payload, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩
  | fault matched =>
    exact ⟨_, finalStore, finalMap, finalWorld,
      by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_failure _ evaluated,
      .fault matched, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩

include head certified found sourceTyped environments heaps locals agrees typed admitted in
/-- Native inversion uses the original sum bind and its strict child grade.
The Source result and parent grade are reconstructed from that one child IH. -/
theorem reflects (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model registry invocation certificate faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      ((LocalLoop.returnValue lowered.type lowered.expression).rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements program registry sourceSize invocation context environment
        before statements context (control outcome) after ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  have original := completed
  rw [LoopRenaming.returnValue] at original
  change EvaluationSize size actual store
    (LanguageResult.bind (LocalLoop.controlType lowered.type) (lowered.expression.rename ξ)
      (LocalLoop.returned (.var 0))) value finalStore at original
  cases CallableIndirectCallBounds.bind_completed original within with
  | failed child strict =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related, post⟩ :=
      children _ strict certified found sourceTyped environments heaps locals agrees typed initial admitted child
    cases represented with
    | fault matched =>
      exact ⟨_, _, after, finalMap, finalWorld, head.trace trace, .fault matched,
        finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩
  | continued child remaining strict _remainingStrict =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related, post⟩ :=
      children _ strict certified found sourceTyped environments heaps locals agrees typed initial admitted child
    cases represented with
    | value payload =>
      have expected := LocalLoop.returnValue_success lowered.type child.sound
      obtain ⟨same, stores⟩ := evaluation_deterministic original.sound expected
      cases same
      subst stores
      exact ⟨_, _, after, finalMap, finalWorld, head.trace trace, .returned payload,
        finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩
end Terminal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTerminalStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTerminalBody
/-! A terminal lexical body removes its original control envelope through the
existing toControl and finish helpers. Actual native prefix inversion supplies
the strict return-helper child; staged expression reflection reconstructs the
Source body at the same endpoint. No completed statement or body law is given. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTerminalBody
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head control)
universe u

def code (type : Ty) (flow : Expr) (escaped : Word) (fallback : Expr) : Expr :=
  LocalControl.finish type (LocalLoop.toControl type flow escaped) fallback

/-- The actual lexical insertion changes the flow and fallback together. -/
theorem code_rename (type : Ty) (flow : Expr) (escaped : Word) (fallback : Expr) (ξ : Renaming) :
    (code type flow escaped fallback).rename ξ =
      code type (flow.rename ξ) escaped (fallback.rename ξ) := by
  simp [code, LocalControl.finish, LocalLoop.toControl, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.rename, Renaming.lift]

/-- The function footer keeps the exact expression value or nested failure. -/
theorem terminal_evaluates {catalog : SourceCoreDataCatalog.Catalog}
    {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {type : Ty} {faults : RecursiveStageMeaning.FaultRep}
    {actual : Environment} {before after : Store} {flow fallback : Expr}
    {outcome : Staging.Recursive.Outcome} {value : Value}
    (represented : CallableIndexedOwnedAdmittedStagedTerminalStatements.ResultRepresents
      model mapping world sourceType type faults outcome value)
    (evaluated : Evaluates actual before flow value after) (escaped : Word) :
    ∃ result, Evaluates actual before (code type flow escaped fallback) result after ∧
      RecursiveStageMeaning.ResultRepresentsFor model mapping world sourceType type faults outcome result := by
  cases represented with
  | returned payload =>
    exact ⟨_, LocalControl.finish_returned type (LocalLoop.toControl_normal type escaped evaluated), .value payload⟩
  | fault matched =>
    exact ⟨_, LocalControl.finish_failure type (LocalLoop.toControl_failure type escaped evaluated), .fault matched⟩

/-- Both original sum binds have their own strict finite children. The footer
may be generic here; the terminal representation later fixes its outcome. -/
theorem flow_prefix {budget size : Nat} {actual : Environment} {before after : Store}
    {type : Ty} {flow fallback : Expr} {escaped : Word} {value : Value}
    (completed : EvaluationSize size actual before (code type flow escaped fallback) value after)
    (within : size ≤ budget) :
    ∃ flowSize flowValue flowStore,
      EvaluationSize flowSize actual before flow flowValue flowStore ∧ flowSize < budget := by
  change EvaluationSize size actual before (LanguageResult.bind type
    (LocalLoop.toControl type flow escaped)
    (.caseE (.var 0) ((fallback.weakenAt 0).weakenAt 0) (LanguageResult.success (.var 0)))) value after at completed
  cases CallableIndirectCallBounds.bind_completed completed within with
  | failed controlTrace strict =>
    change EvaluationSize _ actual before (LanguageResult.bind (LocalControl.controlType type) flow
      (.caseE (.var 0) (LanguageResult.success (.var 0))
        (LanguageResult.failure (LocalControl.controlType type) (.word escaped)))) _ _ at controlTrace
    cases CallableIndirectCallBounds.bind_completed controlTrace (Nat.le_of_lt strict) with
    | failed child childStrict => exact ⟨_, _, _, child, childStrict⟩
    | continued child _remaining childStrict _remainingStrict => exact ⟨_, _, _, child, childStrict⟩
  | continued controlTrace _remaining strict _remainingStrict =>
    change EvaluationSize _ actual before (LanguageResult.bind (LocalControl.controlType type) flow
      (.caseE (.var 0) (LanguageResult.success (.var 0))
        (LanguageResult.failure (LocalControl.controlType type) (.word escaped)))) _ _ at controlTrace
    cases CallableIndirectCallBounds.bind_completed controlTrace (Nat.le_of_lt strict) with
    | continued child _remaining childStrict _remainingStrict => exact ⟨_, _, _, child, childStrict⟩

theorem body_result (type : TypeSystem.Ty) (outcome : Staging.Recursive.Outcome) :
    Staging.Recursive.BodyResult type (control outcome) outcome := by
  cases outcome with
  | value value => exact .returned
  | fault failure => exact .fault

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId}
  {statements : List StatementId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  (head : Head invocation expression statements)
  (certified : certificate scope expression lowered)
  (found : invocation.source.lookupExpression? expression = some node)
  (sourceTyped : ExpressionHasType invocation.source context expression node.type)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
  (heaps : GenericHeap.HeapRepresents model mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

include head certified found sourceTyped environments heaps locals agrees typed admitted in
/-- Actual terminal expression preservation constructs both the sized body
trace and its original BodyResult, then removes the Core control envelope. -/
theorem preserves (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    (escaped : Word) (fallback : Expr)
    {childSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment
      before expression outcome after)
    (within : Staging.Recursive.Size.stepSize [childSize] ≤ budget) :
    Staging.Recursive.Size.Statements program registry (Staging.Recursive.Size.stepSize [childSize])
      invocation context environment before statements context (control outcome) after ∧
    Staging.Recursive.BodyResult node.type (control outcome) outcome ∧
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code lowered.type ((LocalLoop.returnValue lowered.type lowered.expression).rename ξ)
        escaped fallback) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  obtain ⟨trace, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalStatements.preserves bridge head certified found sourceTyped
      environments heaps locals agrees typed initial admitted budget children child within
  obtain ⟨result, whole, resultRep⟩ := terminal_evaluates represented evaluated escaped
  exact ⟨trace, body_result _ _, result, finalStore, finalMap, finalWorld, whole, resultRep,
    finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩

include head certified found sourceTyped environments heaps locals agrees typed admitted in
/-- Original footer inversion supplies the strict terminal helper child.
The genuine expression IH constructs its Source body, and determinism retains
the same completed body result and actual endpoint. -/
theorem reflects (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model registry invocation certificate faults budget)
    (escaped : Word) (fallback : Expr)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      (code lowered.type ((LocalLoop.returnValue lowered.type lowered.expression).rename ξ) escaped fallback)
      value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements program registry sourceSize invocation context environment
        before statements context (control outcome) after ∧
      Staging.Recursive.BodyResult node.type (control outcome) outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  obtain ⟨flowSize, flowValue, flowStore, flow, strict⟩ := flow_prefix completed within
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalStatements.reflects bridge head certified found sourceTyped
      environments heaps locals agrees typed initial admitted budget children flow (Nat.le_of_lt strict)
  obtain ⟨result, whole, resultRep⟩ := terminal_evaluates represented flow.sound escaped
  obtain ⟨same, stores⟩ := evaluation_deterministic completed.sound whole
  cases same
  subst stores
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, body_result _ _, resultRep,
    finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTerminalBody
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedTerminalStatements
/-! Staged return and tail-expression composition uses the original lexical
return helper and strict expression hypotheses. Each result keeps its actual
reached caller state. Native reflection reconstructs an independent staged
Source grade and never projects a nested stage failure to a semantic failure. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedTerminalStatements
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

/-- These are the actual two terminal statement forms compiled by the lexical
statement algebra. The receipt contains only source occurrences and form. -/
inductive Head (invocation : Staging.Recursive.Scope) (expression : ExpressionId) : Bool → List StatementId → Prop where
  | returning {mode id node} (rest : List StatementId)
      (contains : ContainsStatement invocation.source id node)
      (form : node.form = .returnStmt (some expression)) : Head invocation expression mode (id :: rest)
  | tail {id node} (contains : ContainsStatement invocation.source id node)
      (form : node.form = .expression expression false) : Head invocation expression true [id]

def control (outcome : Staging.Recursive.Outcome) : Staging.Recursive.BodyOutcome :=
  match outcome with
  | .value value => .returned value
  | .fault failure => .fault failure

/-- Both terminal forms propagate the same nested failure. A successful
expression becomes the real returned control outcome. -/
theorem Head.trace {mode : Bool} {expression : ExpressionId} {statements : List StatementId}
    (head : Head invocation expression mode statements)
    {size : Nat} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Staging.Recursive.Outcome}
    (child : Staging.Recursive.Size.Expression program registry size invocation context environment
      before expression outcome after) :
    Staging.Recursive.Size.StatementsIn program registry mode (Staging.Recursive.Size.stepSize [size])
      invocation context environment before statements context (control outcome) after := by
  cases head with
  | returning rest contains form =>
    cases outcome with
    | value value => exact .returnValue contains form child
    | fault failure => exact .returnFault contains form child
  | tail contains form =>
    cases outcome with
    | value value => exact .tail contains form child
    | fault failure => exact .expressionFault contains form child

/-- The original control envelope retains the expression payload or exact
fault token. It introduces no fallthrough or additional execution. -/
inductive ResultRepresents (model : GenericHeap.PayloadModel catalog projects definitions)
    (mapping : LocationMap) (world : StoreTyping) (sourceType : TypeSystem.Ty)
    (type : Ty) (faults : RecursiveStageMeaning.FaultRep) :
    Staging.Recursive.Outcome → Value → Prop where
  | returned {source value} (payload : model.Represents mapping world sourceType source value type) :
      ResultRepresents model mapping world sourceType type faults (.value source) (LocalLoop.returnedValue value)
  | fault {failure token} (matched : faults failure token) :
      ResultRepresents model mapping world sourceType type faults (.fault failure)
        (.inLeft (LocalLoop.controlType type) (.word token))

section Terminal
variable {mode : Bool} {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId}
  {statements : List StatementId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  (head : Head invocation expression mode statements)
  (certified : certificate scope expression lowered)
  (found : invocation.source.lookupExpression? expression = some node)
  (sourceTyped : ExpressionHasType invocation.source context expression node.type)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
  (heaps : GenericHeap.HeapRepresents model mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

include head certified found sourceTyped environments heaps locals agrees typed admitted in
/-- The real parent step gives a strict expression grade. The expression IH
runs once and the existing return helper preserves its exact endpoint. -/
theorem preserves (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    {childSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment
      before expression outcome after)
    (within : Staging.Recursive.Size.stepSize [childSize] ≤ budget) :
    Staging.Recursive.Size.StatementsIn program registry mode (Staging.Recursive.Size.stepSize [childSize])
      invocation context environment before statements context (control outcome) after ∧
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.returnValue lowered.type lowered.expression).rename ξ) value finalStore ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  have strict : childSize < budget :=
    Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (child := childSize)
      (children := [childSize]) (by simp)) within
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    children childSize strict certified found sourceTyped environments heaps locals agrees typed initial admitted child
  refine ⟨head.trace child, ?_⟩
  cases represented with
  | value payload =>
    exact ⟨_, finalStore, finalMap, finalWorld,
      by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_success _ evaluated,
      .returned payload, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩
  | fault matched =>
    exact ⟨_, finalStore, finalMap, finalWorld,
      by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_failure _ evaluated,
      .fault matched, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩

include head certified found sourceTyped environments heaps locals agrees typed admitted in
/-- Native inversion uses the original sum bind and its strict child grade.
The Source result and parent grade are reconstructed from that one child IH. -/
theorem reflects (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model registry invocation certificate faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      ((LocalLoop.returnValue lowered.type lowered.expression).rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program registry mode sourceSize invocation context environment
        before statements context (control outcome) after ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  have original := completed
  rw [LoopRenaming.returnValue] at original
  change EvaluationSize size actual store
    (LanguageResult.bind (LocalLoop.controlType lowered.type) (lowered.expression.rename ξ)
      (LocalLoop.returned (.var 0))) value finalStore at original
  cases CallableIndirectCallBounds.bind_completed original within with
  | failed child strict =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related, post⟩ :=
      children _ strict certified found sourceTyped environments heaps locals agrees typed initial admitted child
    cases represented with
    | fault matched =>
      exact ⟨_, _, after, finalMap, finalWorld, head.trace trace, .fault matched,
        finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩
  | continued child remaining strict _remainingStrict =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related, post⟩ :=
      children _ strict certified found sourceTyped environments heaps locals agrees typed initial admitted child
    cases represented with
    | value payload =>
      have expected := LocalLoop.returnValue_success lowered.type child.sound
      obtain ⟨same, stores⟩ := evaluation_deterministic original.sound expected
      cases same
      subst stores
      exact ⟨_, _, after, finalMap, finalWorld, head.trace trace, .returned payload,
        finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩
end Terminal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedTerminalStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBuiltinFaultBounds
/-! The existing builtin producer retains its primitive path at one actual
reached caller. The state post keeps the same native fault evaluation, since
the generic Calls head post does not contain the returned native value. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBuiltinFaultBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open ExpressionFailurePostContracts
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)

/-- This packet names the actual parent evaluation and the same reached heap,
map, world and store. The original Source fault reason remains unchanged. -/
def NativeFaultAt (post : ExpressionFaultPost)
    {initialIndex : ProtectedStateTransition.Index} (_initial : callerProtocol.State initialIndex)
    (environment : Dynamic.Environment) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    (actual : Environment) (ξ : Renaming) (outcome : Dynamic.ExpressionOutcome)
    {index : ProtectedStateTransition.Index} (_reached : callerProtocol.State index) : Prop :=
  match outcome with
  | .value _ => True
  | .fault reason => ∃ token,
      Evaluates actual initialIndex.store (lowered.expression.rename ξ)
        (.inLeft lowered.type (.word token)) index.store ∧
      post program context evidence source environment initialIndex.heap id reason
        index.heap token index.mapping index.world index.store

/-- Admission and the actual fault packet observe the identical returned state. -/
def StatePost (post : ExpressionFaultPost)
    {initialIndex : ProtectedStateTransition.Index} (initial : callerProtocol.State initialIndex)
    (environment : Dynamic.Environment) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    (actual : Environment) (ξ : Renaming) (node : ExpressionNode) (outcome : Dynamic.ExpressionOutcome)
    {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index) : Prop :=
  PostAdmission bridge context node.type outcome reached ∧
  NativeFaultAt (program := program) (source := source) (context := context) evidence post initial environment id lowered actual ξ outcome reached

variable {bridge functions evidence}

/-- Determinism aligns the packet's token with a separately retained actual
parent completion. It does not infer a path from the category FaultRep. -/
theorem NativeFaultAt.at_fault {post : ExpressionFaultPost}
    {initialIndex : ProtectedStateTransition.Index} {initial : callerProtocol.State initialIndex}
    {environment : Dynamic.Environment} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {actual : Environment} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index} {value : Value}
    (packet : NativeFaultAt (program := program) (source := source) (context := context) evidence post
      initial environment id lowered actual ξ (.fault reason) reached)
    (evaluated : Evaluates actual initialIndex.store (lowered.expression.rename ξ) value index.store) :
    ∃ token, value = .inLeft lowered.type (.word token) ∧
      post program context evidence source environment initialIndex.heap id reason
        index.heap token index.mapping index.world index.store := by
  obtain ⟨token, faultEvaluation, retained⟩ := packet
  exact ⟨token, (evaluation_deterministic evaluated faultEvaluation).1, retained⟩

variable (bridge functions evidence)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel (.initial compiled.compatible.checked) source context reasonAt faults)
  (missing : IndexFaultPostContracts.MissingPolicies (.initial compiled.compatible.checked) source functions registry
    program context evidence reasonAt faults)
  (unique : NodeOccurrencesUnique source)
  (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context)

include extension faithful observations functionTypes valid reads missing unique wellFormed runtime covers transport in
/-- One builtin producer returns its complete semantic tuple and primitive path.
The actual Source trace supplies admission at the same protected transition. -/
theorem preserves
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (tree : CompatibleExpressionBuiltins.Tree fuel (.initial compiled.compatible.checked) source context solved reasonAt scope id lowered)
    (found : source.lookupExpression? id = some node) (sourceTyped : ExpressionHasType source context id node.type)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after) :
    ProtectedStateExpressionCallsHeads.WithFacts.PreservesResult (registry := registry) (faults := faults)
      functions callerProtocol
      (StatePost (program := program) (source := source) (context := context) bridge evidence
        (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry)
        initial environment id lowered actual ξ)
      initial node lowered actual ξ outcome after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, retained⟩ :=
    ReachedBuiltinFragmentOutcomePorts.builtin_preserves
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) functions extension program evidence faithful observations functionTypes
      valid reads unique missing tree found environments heaps locals agrees typed trace.sound
  obtain ⟨reached, related⟩ :=
    ProtectedStateTransition.AdministrativeTransport.transition callerProtocol transport initial maps worlds frame metadata
  refine ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped trace frame, ?_⟩
  cases outcome with
  | value sourceValue => trivial
  | fault reason =>
    obtain ⟨token, sameValue, origin⟩ := retained
    exact ⟨token, sameValue ▸ evaluated, origin⟩

include extension faithful observations functionTypes valid reads missing unique wellFormed runtime covers transport in
/-- Native completion retains the same fault packet and reached state. Its
Source grade is reconstructed from the genuine returned Source trace. -/
theorem reflects
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (tree : CompatibleExpressionBuiltins.Tree fuel (.initial compiled.compatible.checked) source context solved reasonAt scope id lowered)
    (found : source.lookupExpression? id = some node) (sourceTyped : ExpressionHasType source context id node.type)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {size : Nat} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore) :
    ProtectedStateExpressionCallsHeads.WithFacts.ReflectsResult (registry := registry) (faults := faults)
      (program := program) (source := source) (context := context) functions evidence callerProtocol
      (StatePost (program := program) (source := source) (context := context) bridge evidence
        (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry)
        initial environment id lowered actual ξ)
      initial node id lowered environment value finalStore := by
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, retained⟩ :=
    ReachedBuiltinFragmentOutcomePorts.builtin_reflects
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) functions extension program evidence faithful observations functionTypes
      valid reads unique missing tree found environments heaps locals agrees typed completed.sound
  obtain ⟨sourceSize, sourceTrace⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size trace
  obtain ⟨reached, related⟩ :=
    ProtectedStateTransition.AdministrativeTransport.transition callerProtocol transport initial maps worlds frame metadata
  refine ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped sourceTrace frame, ?_⟩
  cases outcome with
  | value sourceValue => trivial
  | fault reason =>
    obtain ⟨token, sameValue, origin⟩ := retained
    exact ⟨token, sameValue ▸ completed.sound, origin⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBuiltinFaultBounds
end
