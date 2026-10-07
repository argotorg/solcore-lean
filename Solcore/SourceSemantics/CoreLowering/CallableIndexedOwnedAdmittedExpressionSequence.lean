import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionBounds
import Solcore.SourceSemantics.CoreLowering.ProtectedStateSequenceBridge

/-! Ordered admitted children use the same readiness sequence proof. Authentic
Source typing applies only to actual list members. Successful children pass
their exact reached state and deep heap admission to the next child; faults
retain that state and every row's own stable history. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionSequence
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open DataPatternValues DataExpressionSequence CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

/-- Extract the actual stored type from the genuine Source typing row.
Duplicates retain their own list membership; no off-list expression is typed. -/
theorem member_expression_typed {source : TypedSource} {context : SourceSemantics.Context}
    {ids : List ExpressionId} {types : List TypeSystem.Ty} {id : ExpressionId} {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (typing : ExpressionsHaveTypes source context ids types)
    (member : id ∈ ids) (found : source.lookupExpression? id = some node) :
    ExpressionHasType source context id node.type := by
  cases typing with
  | nil => simp at member
  | @cons _ expression expressions type types head tail =>
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨stored, contains, sourceType⟩ := head.stored_type
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      exact sourceType ▸ head
    · exact member_expression_typed unique tail member found
termination_by ids.length

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {certificate : GenericExpressionMeaning.Certificate} {faults : GenericExpressionMeaning.FaultRep}
  {ids : List ExpressionId} {sourceTypes originalSourceTypes : List TypeSystem.Ty}

/-- A reflected or preserved sequence supplies deep admission only on success.
Every outcome keeps the genuine reached pool and all-row stable histories. -/
structure PostSequenceAdmission (outcome : Outcome) {index : ProtectedStateTransition.Index}
    (reached : callerProtocol.State index) : Prop where
  rows : StableRows (bridge.pool reached)
  successful : ∀ values, outcome = .ok values → Admission bridge context reached

/-- The next real child receives this same successful post. -/
theorem PostSequenceAdmission.at_values {values : List Dynamic.Value}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : PostSequenceAdmission bridge (context := context) (.ok values) reached) : Admission bridge context reached :=
  post.successful values rfl

/-- An admitted Source producer supplies readiness for this actual child. -/
theorem preserves_child_at {id : ExpressionId} {size : Nat}
    (unique : NodeOccurrencesUnique source) (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
    (member : id ∈ ids)
    (meaning : CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context evidence source certificate faults size) :
    ProtectedDataExpressionSequence.Stateful.WithReady.ExpressionPreservesAt callerProtocol
      (Admission bridge context) size model program context evidence source
      (fun current expression code => expression = id ∧ certificate current expression code) faults := by
  intro scope expression lowered certified node found mapping world admin environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  have sourceTyped := member_expression_typed unique typing (certified.1.symm ▸ member) found
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    meaning certified.2 found sourceTyped environments heaps locals agrees typed initial admitted
      (ProtectedStateTransition.SequenceBridge.call_trace trace)
  refine ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, ?_⟩
  intro value same
  cases same
  exact post.at_value.2

/-- Native reflection keeps its independent Source grade and actual post. -/
theorem reflects_child_at {id : ExpressionId} {size : Nat}
    (unique : NodeOccurrencesUnique source) (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
    (member : id ∈ ids)
    (meaning : CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge model context evidence source certificate faults size) :
    ProtectedDataExpressionSequence.Stateful.WithReady.ExpressionReflectsAt callerProtocol
      (Admission bridge context) size model program context evidence source
      (fun current expression code => expression = id ∧ certificate current expression code) faults := by
  intro scope expression lowered certified node found mapping world admin environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  have sourceTyped := member_expression_typed unique typing (certified.1.symm ▸ member) found
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    meaning certified.2 found sourceTyped environments heaps locals agrees typed initial admitted completed
  refine ⟨sourceSize, outcome, after, finalMap, finalWorld,
    ProtectedStateTransition.SequenceBridge.source_trace trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, ?_⟩
  intro value same
  cases same
  exact post.at_value.2

variable {scope : SourceCoreLocalCell.Scope} {codes : List SourceCoreBasic.LoweredExpr}

theorem preserves_values_bounded (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (unique : NodeOccurrencesUnique source)
    (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
    (meaning : ∀ size, size < budget →
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context evidence source certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (initialReady : Admission bridge context initial)
    {size : Nat}
    (execution : SourceExecutionSize.ExpressionsEvaluate program size context evidence source environment before ids sources after) (bounded : size ≤ budget) :
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached := by
  exact
    ProtectedDataExpressionSequence.Stateful.WithReady.preserves_values_bounded callerProtocol
      (Admission bridge context) budget tree
      (fun id member size smaller => preserves_child_at bridge unique typing member (meaning size smaller))
      environments heaps locals layout actualTyped initial initialReady execution bounded

theorem preserves_fault_bounded (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (unique : NodeOccurrencesUnique source)
    (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
    (meaning : ∀ size, size < budget →
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context evidence source certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (initialReady : Admission bridge context initial)
    {size : Nat}
    (execution : SourceExecutionSize.ExpressionsFault program size context evidence source environment before ids reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    ProtectedDataExpressionSequence.Stateful.WithReady.preserves_fault_bounded callerProtocol
      (Admission bridge context) budget tree
      (fun id member size smaller => preserves_child_at bridge unique typing member (meaning size smaller))
      environments heaps locals layout actualTyped initial initialReady execution bounded
  exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) initialReady.rows frame⟩

theorem reflects_bounded (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (unique : NodeOccurrencesUnique source)
    (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
    (meaning : ∀ size, size < budget →
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge model context evidence source certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (initialReady : Admission bridge context initial)
    {size : Nat}
    (evaluated : EvaluationSize size actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) (bounded : size < budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      ProtectedDataExpressionSequence.TraceAt program sourceSize context evidence source environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostSequenceAdmission bridge (context := context) outcome reached := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, successful⟩ :=
    ProtectedDataExpressionSequence.Stateful.WithReady.reflects_bounded callerProtocol
      (Admission bridge context) budget tree
      (fun id member size smaller => reflects_child_at bridge unique typing member (meaning size smaller))
      environments heaps locals layout actualTyped initial initialReady evaluated bounded
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) initialReady.rows frame, successful⟩

theorem preserves_bounded (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (unique : NodeOccurrencesUnique source)
    (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
    (meaning : ∀ size, size < budget →
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context evidence source certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Outcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (initialReady : Admission bridge context initial)
    {size : Nat}
    (execution : ProtectedDataExpressionSequence.TraceAt program size context evidence source environment before ids outcome after) (bounded : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostSequenceAdmission bridge (context := context) outcome reached := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, successful⟩ :=
    ProtectedDataExpressionSequence.Stateful.WithReady.preserves_bounded callerProtocol
      (Admission bridge context) budget tree
      (fun id member size smaller => preserves_child_at bridge unique typing member (meaning size smaller))
      environments heaps locals layout actualTyped initial initialReady execution bounded
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) initialReady.rows frame, successful⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionSequence
