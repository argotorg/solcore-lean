import Solcore.SourceSemantics.CoreLowering.DataPlaceMappingPreparation
import Solcore.SourceSemantics.CoreLowering.DataExpressionSequence
import Solcore.SourceSemantics.CoreLowering.DataPlaceCertificates

/-! Ordered index expressions from actual place preparation. The independent
source projection trace is equivalent to evaluating exactly this expression
vector: member projections contribute no expression execution. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceKeyOrder
open Core Frontend Frontend.SourceInference SourceCoreDataPlaces DataPatternValues

def sourceKeys : List PlaceProjection → List ExpressionId
  | [] => []
  | .member _ _ :: rest => sourceKeys rest
  | .index key :: rest => key :: sourceKeys rest

def stepKeys : List Step → List ExpressionId
  | [] => []
  | .member _ _ _ _ :: rest => stepKeys rest
  | .index _ key _ :: rest => key :: stepKeys rest

/-- A projection vector retains member names and positions while pairing
index positions with their ordered source values. -/
inductive Values : List PlaceProjection → List Dynamic.Value → List Dynamic.EvaluatedProjection → Prop where
  | nil : Values [] [] []
  | member {name index rest values projections} (tail : Values rest values projections) :
      Values (.member name index :: rest) values (.member name index :: projections)
  | index {key rest value values projections} (tail : Values rest values projections) :
      Values (.index key :: rest) (value :: values) (.index value :: projections)

theorem projections_values {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {projections : List PlaceProjection} {evaluated : List Dynamic.EvaluatedProjection}
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before projections evaluated after) :
    ∃ values, Values projections values evaluated ∧
      Dynamic.ExpressionsEvaluate program context evidence source environment before (sourceKeys projections) values after := by
  induction projections generalizing before evaluated with
  | nil => cases trace; exact ⟨[], .nil, .nil⟩
  | cons projection rest ih =>
    cases projection with
    | member name index =>
      cases trace with
      | member tail => obtain ⟨values, related, evaluated⟩ := ih tail; exact ⟨values, .member related, evaluated⟩
    | index key =>
      cases trace with
      | index head tail => obtain ⟨values, related, evaluated⟩ := ih tail; exact ⟨_ :: values, .index related, .cons head evaluated⟩

theorem values_projections {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {projections : List PlaceProjection} {values : List Dynamic.Value}
    (trace : Dynamic.ExpressionsEvaluate program context evidence source environment before (sourceKeys projections) values after) :
    ∃ evaluated, Values projections values evaluated ∧
      Dynamic.SourceProjectionsEvaluate program context evidence source environment before projections evaluated after := by
  induction projections generalizing before values with
  | nil => cases trace; exact ⟨[], .nil, .nil⟩
  | cons projection rest ih =>
    cases projection with
    | member name index => obtain ⟨evaluated, related, executed⟩ := ih trace; exact ⟨_, .member related, .member executed⟩
    | index key =>
      cases trace with
      | cons head tail => obtain ⟨evaluated, related, executed⟩ := ih tail; exact ⟨_, .index related, .index head executed⟩

theorem projections_fault {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {projections : List PlaceProjection} {reason : Dynamic.SemanticFault}
    (trace : Dynamic.SourceProjectionsFault program context evidence source environment before projections reason after) :
    Dynamic.ExpressionsFault program context evidence source environment before (sourceKeys projections) reason after := by
  induction projections generalizing before with
  | nil => cases trace
  | cons projection rest ih =>
    cases projection with
    | member name index => cases trace with
      | memberTail tail => exact ih tail
    | index key => cases trace with
      | indexHead fault => exact .head fault
      | indexTail head tail => exact .tail head (ih tail)

theorem fault_projections {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {projections : List PlaceProjection} {reason : Dynamic.SemanticFault}
    (trace : Dynamic.ExpressionsFault program context evidence source environment before (sourceKeys projections) reason after) :
    Dynamic.SourceProjectionsFault program context evidence source environment before projections reason after := by
  induction projections generalizing before with
  | nil => cases trace
  | cons projection rest ih =>
    cases projection with
    | member name index => exact .memberTail (ih trace)
    | index key => cases trace with
      | head fault => exact .indexHead fault
      | tail head rest => exact .indexTail head (ih rest)

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : first >>= next = .ok value) : ∃ input, first = .ok input ∧ next input = .ok value := by
  cases first <;> simp_all [bind, Except.bind]

private theorem member_shape {checked : Checked} {signatures : ProgramSignatures}
    {site : SourceCoreElaboration.ErrorSite} {binder : Resolved.LocalId} {type field : TypeSystem.Ty}
    {index : Nat} {step : Step}
    (accepted : memberStep checked signatures site binder type index = .ok (step, field)) :
    ∃ identity branches coreType, step = .member identity index branches coreType := by
  unfold memberStep at accepted
  dsimp only at accepted
  split at accepted <;> (try simp only [pure, Except.pure, bind, Except.bind, throw] at accepted) <;> try cases accepted
  split at accepted <;> (try simp only [pure, Except.pure, bind, Except.bind, throw] at accepted) <;> try cases accepted
  split at accepted <;> (try simp only [pure, Except.pure, bind, Except.bind, throw] at accepted) <;> try cases accepted
  split at accepted <;> (try simp only [pure, Except.pure, bind, Except.bind, throw] at accepted) <;> try cases accepted
  obtain ⟨state, _, accepted⟩ := bind_ok accepted
  split at accepted <;> (try simp only [pure, Except.pure, bind, Except.bind, throw] at accepted) <;> try cases accepted
  obtain ⟨coreType, _, accepted⟩ := bind_ok accepted
  cases accepted
  exact ⟨_, _, coreType, rfl⟩

/-- The successful route traversal keeps exactly the source index occurrences,
including repeated occurrences and indices separated by nominal members. -/
theorem routeSteps_keys {checked : Checked} {signatures : ProgramSignatures}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {binder : Resolved.LocalId}
    {type field : TypeSystem.Ty} {projections : List PlaceProjection} {steps : List Step}
    (accepted : routeSteps checked signatures source site binder type projections = .ok (steps, field)) :
    stepKeys steps = sourceKeys projections := by
  induction projections generalizing type steps field with
  | nil =>
    simp only [routeSteps, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    rfl
  | cons projection rest ih =>
    cases projection with
    | member name index =>
      rw [routeSteps.eq_def] at accepted
      dsimp only at accepted
      obtain ⟨selected, first, accepted⟩ := bind_ok accepted
      obtain ⟨step, selectedType⟩ := selected
      obtain ⟨remaining, tail, accepted⟩ := bind_ok accepted
      obtain ⟨remainingSteps, finalType⟩ := remaining
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      obtain ⟨identity, branches, coreType, rfl⟩ := member_shape first
      simpa only [stepKeys, sourceKeys] using (ih (steps := remainingSteps) tail)
    | index key =>
      rw [routeSteps.eq_def] at accepted
      dsimp only at accepted
      split at accepted <;> (try simp only [pure, Except.pure, bind, Except.bind, throw] at accepted) <;> try cases accepted
      split at accepted <;> (try simp only [pure, Except.pure, bind, Except.bind, throw] at accepted) <;> try cases accepted
      split at accepted <;> (try simp only [pure, Except.pure, bind, Except.bind, throw] at accepted) <;> try cases accepted
      obtain ⟨keyType, _, accepted⟩ := bind_ok accepted
      obtain ⟨projectedKey, _, accepted⟩ := bind_ok accepted
      obtain ⟨checkedUnit, _, accepted⟩ := bind_ok accepted
      cases checkedUnit
      obtain ⟨valueType, _, accepted⟩ := bind_ok accepted
      split at accepted <;> (try simp only [pure, Except.pure, bind, Except.bind, throw] at accepted) <;> try cases accepted
      split at accepted <;> (try simp only [pure, Except.pure, bind, Except.bind, throw] at accepted) <;> try cases accepted
      obtain ⟨remaining, tail, accepted⟩ := bind_ok accepted
      obtain ⟨remainingSteps, finalType⟩ := remaining
      cases accepted
      exact congrArg (key :: ·) (ih tail)

/-- The preparation loop's real key table keeps route order. Comparator and
default preparation introduce no additional source expression occurrences. -/
theorem prepared_keys {checked : Checked} {fuel : Nat} {route : Route}
    {invalid : Word} {missing : TypeSystem.Ty → Word} {prepared : Prepared}
    (accepted : prepare checked fuel route invalid missing = .ok prepared) :
    prepared.keys.map Prod.fst = stepKeys route.steps := by
  obtain ⟨_, _, generated⟩ := DataPlaceMappingPreparation.steps_of_prepare accepted
  have ordered : ∀ {count steps targets keys},
      DataPlaceMappingPreparation.Steps checked fuel missing count steps targets keys →
        keys.map Prod.fst = stepKeys steps := by
    intro count steps targets keys generated
    induction generated with
    | nil => rfl
    | member _ ih => exact ih
    | index _ _ _ _ _ ih => exact congrArg (_ :: ·) ih
  exact ordered generated

theorem described_keys {checked : Checked} {signatures : ProgramSignatures}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {route : Route}
    (accepted : describe checked signatures source site assignment = .ok route) :
    stepKeys route.steps = sourceKeys assignment.target.projections := by
  unfold describe at accepted
  dsimp only at accepted
  split at accepted <;> (try simp only [pure, Except.pure, bind, Except.bind, throw] at accepted) <;> try cases accepted
  obtain ⟨binder, _, accepted⟩ := bind_ok accepted
  obtain ⟨rootType, _, accepted⟩ := bind_ok accepted
  obtain ⟨routed, routedBy, accepted⟩ := bind_ok accepted
  obtain ⟨steps, field⟩ := routed
  split at accepted <;> try cases accepted
  dsimp only [bind, Except.bind, pure, Except.pure] at accepted
  repeat' first | split at accepted | cases accepted
  all_goals exact routeSteps_keys routedBy

theorem prepared_source_keys {checked : Checked} {signatures : ProgramSignatures}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
    {fuel : Nat} {route : Route} {invalid : Word} {missing : TypeSystem.Ty → Word} {prepared : Prepared}
    (described : describe checked signatures source site assignment = .ok route)
    (preparedBy : prepare checked fuel route invalid missing = .ok prepared) :
    prepared.keys.map Prod.fst = sourceKeys assignment.target.projections :=
  (prepared_keys preparedBy).trans (described_keys described)

/-- Actual accepted child compilations and exact key-type checks automatically
produce the vector certificate used by the semantic sequence theorems. -/
theorem tree_of_generated_keys {checked : Checked} {signatures : ProgramSignatures}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
    {fuel : Nat} {route : Route} {invalid : Word} {missing : TypeSystem.Ty → Word} {prepared : Prepared}
    {expression : ExpressionLowerer} {scope : Scope} {reasonAt : ExpressionId → Word}
    {codes : List SourceCoreBasic.LoweredExpr} {certificate : GenericExpressionMeaning.Certificate}
    (described : describe checked signatures source site assignment = .ok route)
    (preparedBy : prepare checked fuel route invalid missing = .ok prepared)
    (generated : ListRel (DataPlaceCertificates.KeyGenerated expression fuel source scope reasonAt) prepared.keys codes)
    (extract : ∀ id code, expression fuel source scope id reasonAt = .ok code → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id code) :
    ∃ types, DataExpressionSequence.Tree source certificate scope (sourceKeys assignment.target.projections) types codes ∧
      prepared.keyTypes = codes.map (·.type) := by
  have collect : ∀ {keys codes},
      ListRel (DataPlaceCertificates.KeyGenerated expression fuel source scope reasonAt) keys codes →
      ListRel (fun id code => ∃ node, source.lookupExpression? id = some node ∧ certificate scope id code)
        (keys.map Prod.fst) codes ∧ keys.map Prod.snd = codes.map (·.type) := by
    intro keys codes generated
    induction generated with
    | nil => exact ⟨.nil, rfl⟩
    | cons head tail ih => exact ⟨.cons (extract _ _ head.1) ih.1, by simp only [List.map_cons, head.2, ih.2]⟩
  have receipts := collect generated
  obtain ⟨types, tree⟩ := DataExpressionSequence.Tree.of_children receipts.1
  rw [prepared_source_keys described preparedBy] at tree
  exact ⟨types, tree, receipts.2⟩

open GeneralHeap GenericExpressionMeaning

/-- Index effects are evaluated exactly once in source projection order. The
generated values remain fully represented after later index effects. -/
theorem preserves {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {certificate : GenericExpressionMeaning.Certificate} {faults : FaultRep}
    {projections : List PlaceProjection} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source certificate scope (sourceKeys projections) types codes)
    (meaning : Preserves model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {evaluated : List Dynamic.EvaluatedProjection}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before projections evaluated after) :
    ∃ sources values finalStore finalMap finalWorld,
      Values projections sources evaluated ∧
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      DataExpressionSequence.Values model finalMap finalWorld types (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨sources, shaped, executed⟩ := projections_values trace
  obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata⟩ := tree.preserves_values meaning environments heaps locals layout executed
  exact ⟨sources, values, finalStore, finalMap, finalWorld, shaped, evaluated, represented,
    finalHeaps, maps, worlds, frame, metadata⟩

theorem preserves_fault {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {certificate : GenericExpressionMeaning.Certificate} {faults : FaultRep}
    {projections : List PlaceProjection} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source certificate scope (sourceKeys projections) types codes)
    (meaning : Preserves model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (trace : Dynamic.SourceProjectionsFault program context evidence source environment before projections reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  tree.preserves_fault meaning environments heaps locals layout (projections_fault trace)

inductive OutcomeTrace (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (projections : List PlaceProjection) : DataExpressionSequence.Outcome → Dynamic.Heap → Prop where
  | values {values evaluated after} (shaped : Values projections values evaluated)
      (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before projections evaluated after) :
      OutcomeTrace program context evidence source environment before projections (.ok values) after
  | fault {reason after}
      (trace : Dynamic.SourceProjectionsFault program context evidence source environment before projections reason after) :
      OutcomeTrace program context evidence source environment before projections (.error reason) after

theorem reflects {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {certificate : GenericExpressionMeaning.Certificate} {faults : FaultRep}
    {projections : List PlaceProjection} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source certificate scope (sourceKeys projections) types codes)
    (meaning : Reflects model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      OutcomeTrace program context evidence source environment before projections outcome after ∧
      DataExpressionSequence.Result model finalMap finalWorld types codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps,
    maps, worlds, frame, metadata⟩ := tree.reflects meaning environments heaps locals layout evaluated
  refine ⟨outcome, after, finalMap, finalWorld, ?_, represented, finalHeaps, maps, worlds, frame, metadata⟩
  cases sourceTrace with
  | values trace => obtain ⟨evaluated, shaped, sourceTrace⟩ := values_projections trace; exact .values shaped sourceTrace
  | fault trace => exact .fault (fault_projections trace)

end Solcore.SourceSemantics.CoreLowering.DataPlaceKeyOrder
