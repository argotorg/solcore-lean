import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectExpressionHeads
import Solcore.SourceSemantics.Dynamic.WholeLanguagePreservation

/-! Source admission is a pointwise receipt at an actual caller state. Deep
Source heap typing follows real successful Source execution; administrative
preservation separately retains every reached row's own stable history.
Faults retain the actual post and stable rows. They carry no claim of deep heap
typing. These adapters supply no administrative transport or execution law. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (context : SourceSemantics.Context)

/-- Both facets describe this actual input. A single selected-row packet does
not supply the all-row receipt or the deep Source heap receipt. -/
structure Admission {index : ProtectedStateTransition.Index}
    (initial : callerProtocol.State index) : Prop where
  heap : Dynamic.HeapWellTyped context index.heap
  rows : StableRows (bridge.pool initial)

/-- Only a successful Source outcome supplies value and deep heap typing.
The reached pool and every row's own stable history are retained for faults. -/
structure PostAdmission (type : TypeSystem.Ty) (outcome : Dynamic.ExpressionOutcome)
    {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index) : Prop where
  rows : StableRows (bridge.pool reached)
  successful : ∀ value, outcome = .value value →
    Dynamic.ValueHasType context index.heap value type ∧ Dynamic.HeapWellTyped context index.heap

variable {bridge context}

/-- Successful posts become genuine input admission at the same actual state. -/
theorem PostAdmission.at_value {type : TypeSystem.Ty} {value : Dynamic.Value}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : PostAdmission bridge context type (.value value) reached) :
    Dynamic.ValueHasType context index.heap value type ∧ Admission bridge context reached := by
  have typed := post.successful value rfl
  exact ⟨typed.1, typed.2, post.rows⟩

/-- Pair the real Source derivation with the actual reached caller witness.
No old state is substituted for that witness, and its own ghosts authenticate
all reached stable histories. -/
theorem after_expression {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    (admitted : Admission bridge context first)
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {id : ExpressionId} {type : TypeSystem.Ty}
    {outcome : Dynamic.ExpressionOutcome}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (typed : ExpressionHasType source context id type)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment
      initial.heap id outcome reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    PostAdmission bridge context type outcome last := by
  refine ⟨StableRows.after_administrative (bridge.pool first) (bridge.pool last) admitted.rows frame, ?_⟩
  intro value same
  cases trace with
  | value evaluated =>
    cases same
    have preserved := wellFormed.wholeLanguagePreservation.expression context evidence source environment
      initial.heap reached.heap id _ type runtime covers locals admitted.heap typed evaluated
    exact ⟨preserved.value_typed, preserved.heap_typed⟩
  | fault _ => cases same

/-- Source and Core grades remain independent. The exact original sized
Source derivation supplies the admission; its grade is not changed. -/
theorem after_expression_sized {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    (admitted : Admission bridge context first)
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {id : ExpressionId} {type : TypeSystem.Ty}
    {outcome : Dynamic.ExpressionOutcome} {size : Nat}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (typed : ExpressionHasType source context id type)
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment
      initial.heap id outcome reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    PostAdmission bridge context type outcome last :=
  after_expression first last admitted wellFormed runtime covers locals typed trace.sound frame

/-- Sequential use consumes the actual first successful post together with
its Source admission. The callback never receives an administrative surrogate. -/
theorem then_value {initial middle final : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (admitted : Admission bridge context first)
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {id : ExpressionId} {type : TypeSystem.Ty}
    {value : Dynamic.Value} {size : Nat}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (typed : ExpressionHasType source context id type)
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment
      initial.heap id (.value value) middle.heap)
    (frame : AdministrativePreserved initial.mapping initial.store middle.mapping middle.store)
    (transition : ProtectedStateTransition.Transition callerProtocol first middle)
    (next : ∀ reached : callerProtocol.State middle, callerProtocol.Relates first reached →
      Admission bridge context reached → Dynamic.ValueHasType context middle.heap value type →
      ProtectedStateTransition.Transition callerProtocol reached final) :
    ProtectedStateTransition.Transition callerProtocol first final := by
  apply transition.then
  intro reached related
  have post := after_expression_sized first reached admitted wellFormed runtime covers locals typed trace frame
  have actualAdmission := post.at_value
  exact next reached related actualAdmission.2 actualAdmission.1

section ExpressionConsumer
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {certificate : GenericExpressionMeaning.Certificate} {faults : GenericExpressionMeaning.FaultRep}
  {size : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {node : ExpressionNode}
  {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {actualContext : Core.Context}
  {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (wellFormed : ProgramWellFormed program)
  (runtime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context)
  (certified : certificate scope id lowered)
  (found : source.lookupExpression? id = some node)
  (sourceTyped : ExpressionHasType source context id node.type)
  (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
  (heaps : GenericHeap.HeapRepresents model mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)

include admitted wellFormed runtime covers certified found sourceTyped environments heaps locals agrees typed

/-- Consume an existing actual-state producer pointwise and retain its full
semantic result, exact reached witness, relation and authentic Source admission. -/
theorem preserves_at
    (meaning : ProtectedStateTransition.PreservesAt callerProtocol model program context evidence source certificate faults size)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.type outcome reached := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
      frame, metadata, reached, related⟩ :=
    meaning certified found environments heaps locals agrees typed initial trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped trace frame⟩

/-- Native reflection first obtains its independently graded real Source
trace. That trace authenticates successful admission at the same returned post. -/
theorem reflects_at
    (meaning : ProtectedStateTransition.ReflectsAt callerProtocol model program context evidence source certificate faults size)
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.type outcome reached := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
      frame, metadata, reached, related⟩ :=
    meaning certified found environments heaps locals agrees typed initial completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped trace frame⟩
end ExpressionConsumer

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission
