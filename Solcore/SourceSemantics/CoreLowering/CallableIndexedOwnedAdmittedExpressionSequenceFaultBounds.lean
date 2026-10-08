import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionSequence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBuiltinFaultBounds

/-! The original ready sequence consumes actual admitted child fault packets.
Finite Source joins retain the exact reason, token and reached tuple. No
primitive is selected from a category relation or an unrelated receiving heap. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionSequenceFaultBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open DataPatternValues DataExpressionSequence CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open ExpressionFailurePostContracts
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
  (certificate : GenericExpressionMeaning.Certificate) (faults : GenericExpressionMeaning.FaultRep)

def PreservesAt (post : ExpressionFailurePostContracts.ExpressionFaultPost) (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.type outcome reached ∧
        CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt (program := program) (source := source)
          (context := context) evidence post initial environment id lowered actual ξ outcome reached

def ReflectsAt (post : ExpressionFailurePostContracts.ExpressionFaultPost) (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.type outcome reached ∧
        CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt (program := program) (source := source)
          (context := context) evidence post initial environment id lowered actual ξ outcome reached

variable {bridge model context evidence source certificate faults}

theorem PreservesAt.forget {post : ExpressionFaultPost} {size : Nat}
    (meaning : PreservesAt bridge model context evidence source certificate faults post size) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context evidence source certificate faults size := by
  intro scope id lowered certified node found sourceTyped mapping world admin environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, admission, _post⟩ :=
    meaning certified found sourceTyped environments heaps locals agrees typed initial admitted trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, admission⟩

theorem ReflectsAt.forget {post : ExpressionFaultPost} {size : Nat}
    (meaning : ReflectsAt bridge model context evidence source certificate faults post size) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge model context evidence source certificate faults size := by
  intro scope id lowered certified node found sourceTyped mapping world admin environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted trace
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, admission, _post⟩ :=
    meaning certified found sourceTyped environments heaps locals agrees typed initial admitted trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, admission⟩

variable (bridge model context evidence source certificate faults)
variable {ids : List ExpressionId} {sourceTypes originalSourceTypes : List TypeSystem.Ty}

theorem preserves_child_at (post : ExpressionFaultPost) {id : ExpressionId} {size : Nat}
    (unique : NodeOccurrencesUnique source) (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
    (member : id ∈ ids)
    (meaning : PreservesAt bridge model context evidence source certificate faults post size) :
    ProtectedReadyExpressionFaultPostContracts.ExpressionPreservesAt ProtectedDataExpressionSequence.ExpressionTraceAt callerProtocol
      (Admission bridge context) post size model program context evidence source
      (fun current expression code => expression = id ∧ certificate current expression code) faults := by
  intro scope expression lowered certified node found mapping world admin environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  have sourceTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typing (certified.1.symm ▸ member) found
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, admission, retained⟩ :=
    meaning certified.2 found sourceTyped environments heaps locals agrees typed initial admitted
      (ProtectedStateTransition.SequenceBridge.call_trace trace)
  refine ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, ⟨reached, related, ?_⟩, ?_⟩
  · intro value same
    cases same
    exact admission.at_value.2
  · cases outcome with
    | value => trivial
    | fault reason =>
      exact CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault retained evaluated

/-- Native reflection keeps its independent Source grade and actual post. -/
theorem reflects_child_at (post : ExpressionFaultPost) {id : ExpressionId} {size : Nat}
    (unique : NodeOccurrencesUnique source) (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
    (member : id ∈ ids)
    (meaning : ReflectsAt bridge model context evidence source certificate faults post size) :
    ProtectedReadyExpressionFaultPostContracts.ExpressionReflectsAt ProtectedDataExpressionSequence.ExpressionTraceAt callerProtocol
      (Admission bridge context) post size model program context evidence source
      (fun current expression code => expression = id ∧ certificate current expression code) faults := by
  intro scope expression lowered certified node found mapping world admin environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  have sourceTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typing (certified.1.symm ▸ member) found
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, admission, retained⟩ :=
    meaning certified.2 found sourceTyped environments heaps locals agrees typed initial admitted completed
  refine ⟨sourceSize, outcome, after, finalMap, finalWorld,
    ProtectedStateTransition.SequenceBridge.source_trace trace, represented, finalHeaps,
    maps, worlds, frame, metadata, ⟨reached, related, ?_⟩, ?_⟩
  · intro value same
    cases same
    exact admission.at_value.2
  · cases outcome with
    | value => trivial
    | fault reason =>
      exact CallableIndexedOwnedAdmittedBuiltinFaultBounds.NativeFaultAt.at_fault retained completed.sound

variable {scope : SourceCoreLocalCell.Scope} {codes : List SourceCoreBasic.LoweredExpr}

theorem preserves_fault_bounded (expressionPost : ExpressionFaultPost) (listPost : ExpressionsFaultPost)
    (joins : SequenceJoins expressionPost listPost program context evidence source) (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (unique : NodeOccurrencesUnique source)
    (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
    (meaning : ∀ size, size < budget →
      PreservesAt bridge model context evidence source certificate faults expressionPost size)
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
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) ∧
        listPost program context evidence source environment before ids reason after token finalMap finalWorld finalStore := by
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
    maps, worlds, frame, metadata, ⟨reached, related⟩, retained⟩ :=
    ProtectedDataExpressionSequence.Stateful.WithReady.preserves_fault_bounded_with_post callerProtocol
      (Admission bridge context) expressionPost listPost joins budget tree
      (fun id member size smaller => preserves_child_at bridge model context evidence source certificate faults
        expressionPost unique typing member (meaning size smaller))
      environments heaps locals layout actualTyped initial initialReady execution bounded
  exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) initialReady.rows frame, retained⟩

theorem reflects_bounded (expressionPost : ExpressionFaultPost) (listPost : ExpressionsFaultPost)
    (joins : SequenceJoins expressionPost listPost program context evidence source) (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (unique : NodeOccurrencesUnique source)
    (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
    (meaning : ∀ size, size < budget →
      ReflectsAt bridge model context evidence source certificate faults expressionPost size)
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
        callerProtocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedExpressionSequence.PostSequenceAdmission bridge (context := context) outcome reached ∧
        ListOutcomePost listPost program context evidence source environment before ids
          (SourceCoreCalls.packArguments codes).type outcome after value finalMap finalWorld finalStore := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, ⟨reached, related, successful⟩, retained⟩ :=
    ProtectedDataExpressionSequence.Stateful.WithReady.reflects_bounded_with_post callerProtocol
      (Admission bridge context) expressionPost listPost joins budget tree
      (fun id member size smaller => reflects_child_at bridge model context evidence source certificate faults
        expressionPost unique typing member (meaning size smaller))
      environments heaps locals layout actualTyped initial initialReady evaluated bounded
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    ⟨StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) initialReady.rows frame, successful⟩, retained⟩

theorem preserves_bounded (expressionPost : ExpressionFaultPost) (listPost : ExpressionsFaultPost)
    (joins : SequenceJoins expressionPost listPost program context evidence source) (budget : Nat) (tree : Tree source certificate scope ids sourceTypes codes)
    (unique : NodeOccurrencesUnique source)
    (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
    (meaning : ∀ size, size < budget →
      PreservesAt bridge model context evidence source certificate faults expressionPost size)
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
        callerProtocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedExpressionSequence.PostSequenceAdmission bridge (context := context) outcome reached ∧
        ListOutcomePost listPost program context evidence source environment before ids
          (SourceCoreCalls.packArguments codes).type outcome after value finalMap finalWorld finalStore := by
  cases execution with
  | values trace =>
    obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, admitted⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.preserves_values_bounded bridge budget tree unique typing
        (fun size smaller => PreservesAt.forget (meaning size smaller)) environments heaps locals layout actualTyped initial initialReady trace bounded
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .values represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, ⟨admitted.rows, fun _ _ => admitted⟩, True.intro⟩
  | fault trace =>
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
      maps, worlds, frame, metadata, reached, related, rows, retained⟩ :=
      preserves_fault_bounded bridge model context evidence source certificate faults expressionPost listPost joins
        budget tree unique typing meaning environments heaps locals layout actualTyped initial initialReady trace bounded
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps,
      maps, worlds, frame, metadata, reached, related, ⟨rows, fun _ impossible => nomatch impossible⟩,
      ⟨token, rfl, retained⟩⟩

section Builtin
variable (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel (.initial compiled.compatible.checked) source context reasonAt faults)
  (missing : IndexFaultPostContracts.MissingPolicies (.initial compiled.compatible.checked) source functions registry
    program context evidence reasonAt faults)
  (unique : NodeOccurrencesUnique source)
  (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context)

include transport extension faithful observations functionTypes valid reads missing unique wellFormed runtime covers in
/-- The genuine builtin producer supplies the closed child packet at every
actual admitted entry. The finite conversion supplies no separate origin law. -/
theorem preserves_builtin (size : Nat) :
    PreservesAt bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source (CompatibleExpressionBuiltins.Tree fuel (.initial compiled.compatible.checked)
        source context solved reasonAt) faults
      (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry) size := by
  intro scope id lowered tree node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  exact CallableIndexedOwnedAdmittedBuiltinFaultBounds.preserves bridge functions evidence transport extension
    faithful observations functionTypes valid reads missing unique wellFormed runtime covers
    tree found sourceTyped environments heaps locals agrees typed initial admitted trace

include transport extension faithful observations functionTypes valid reads missing unique wellFormed runtime covers in
/-- The actual measured builtin child retains its independent Source grade
and the same token/path used by the ordered sequence join. -/
theorem reflects_builtin (size : Nat) :
    ReflectsAt bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source (CompatibleExpressionBuiltins.Tree fuel (.initial compiled.compatible.checked)
        source context solved reasonAt) faults
      (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry) size := by
  intro scope id lowered tree node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  exact CallableIndexedOwnedAdmittedBuiltinFaultBounds.reflects bridge functions evidence transport extension
    faithful observations functionTypes valid reads missing unique wellFormed runtime covers
    tree found sourceTyped environments heaps locals agrees typed initial admitted completed

/-- The concrete builtin list post uses the original head/tail path constructors
at the same primitive, without a generic category-wide origin supplier. -/
theorem builtin_sequence_joins :
    SequenceJoins
      (ReachedBuiltinExpressionFaultPaths.model_expressionPost compiled.compatible.checked functions registry)
      (ReachedBuiltinExpressionFaultPaths.model_expressionsPost compiled.compatible.checked functions registry)
      program context evidence source :=
  ReachedBuiltinExpressionFaultPaths.sequence_joins compiled.compatible.checked functions registry program context evidence source

end Builtin

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionSequenceFaultBounds
