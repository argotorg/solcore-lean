import Solcore.SourceSemantics.Staging.Internal.SelectedContracts
import Solcore.SourceSemantics.Staging.Internal.FaultCalls

/-!
# Cases of selected preservation

One step of the staged preservation induction for each expression and statement form.
-/

section
-- leanmerge: from Solcore.SourceSemantics.Staging.SelectedPreservationComposition
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

theorem OutcomePreserved.success {context : Context} {before after : Heap}
    {type : Ty} {value : Value} (post : OutcomePreserved context before after type (.value value)) :
    ExpressionEvaluationPreserved context before after value type :=
  ⟨post.value_typed value rfl, post.heap_typed, post.heap_extends⟩

theorem StatementsAt.bodySuccess {size : Nat} (sound : StatementsAt program registry size) :
    BodySuccessAt program registry size := by
  intro scope context staticFinal runtimeFinal environment before after roots facts type outcome value
    runtime covers locals heap typed completes trace result
  have preserved := sound runtime covers locals heap typed trace
  cases result with
  | returned => exact ⟨preserved.returned (fun _ => completes) _ rfl, preserved.heap_typed, preserved.heap_extends⟩
  | unit => exact ⟨.unit, preserved.heap_typed, preserved.heap_extends⟩

theorem StatementsAt.fault {size : Nat} (sound : StatementsAt program registry size) :
    FaultPreservation.StatementsAt program registry size := by
  intro mode scope context staticFinal runtimeFinal environment before after statements failure control facts
    runtime covers locals heap typed trace
  have preserved := sound runtime covers locals heap typed trace
  exact ⟨preserved.heap_typed, preserved.heap_extends⟩

theorem applies_all_step (selectedBodies : GlobalBodiesTyped program registry) (size : Nat)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller) :
    AppliesAt program registry size := by
  intro scope context source before after callable arguments packed outcome parameter result
    runtime heap typed packing packedTyped trace
  cases outcome with
  | value value =>
    have preserved := applies_step selectedBodies size
      (fun smaller below => StatementsAt.bodySuccess (statementsIH smaller below))
      runtime heap typed packing packedTyped trace
    exact ⟨preserved.heap_typed, preserved.heap_extends, by
      intro actual equal; cases equal; exact preserved.value_typed⟩
  | fault failure =>
    have preserved := SelectedFaultPreservation.applies_step selectedBodies size
      (fun smaller below => StatementsAt.fault (statementsIH smaller below))
      runtime heap typed packing packedTyped trace
    exact ⟨preserved.1, preserved.2, by intro value equal; cases equal⟩

theorem expressions_step (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (expressionsIH : ∀ smaller, smaller < size → ExpressionsAt program registry smaller) :
    ExpressionsAt program registry size := by
  intro scope context environment before after ids outcome types runtime covers locals heap typed trace
  cases trace with
  | nil =>
    cases typed
    exact ⟨heap, .refl _, by intro values equal; cases equal; exact .nil⟩
  | @cons headSize tailSize scope context environment before middle after id ids value values head tail =>
    cases typed with
    | cons headTyped tailTyped =>
      have first := expressionIH headSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap headTyped head
      have next := expressionsIH tailSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed tailTyped tail
      exact ⟨next.heap_typed, first.heap_extends.trans next.heap_extends, by
        intro actual equal; cases equal
        exact .cons ((first.value_typed _ rfl).mono next.heap_extends) (next.values_typed _ rfl)⟩
  | @headFault headSize scope context environment before after id ids failure head =>
    cases typed with
    | cons headTyped tailTyped =>
      have first := expressionIH headSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap headTyped head
      exact ⟨first.heap_typed, first.heap_extends, by intro values equal; cases equal⟩
  | @tailFault headSize tailSize scope context environment before middle after id ids value failure head tail =>
    cases typed with
    | cons headTyped tailTyped =>
      have first := expressionIH headSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap headTyped head
      have next := expressionsIH tailSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed tailTyped tail
      exact ⟨next.heap_typed, first.heap_extends.trans next.heap_extends, by intro values equal; cases equal⟩

theorem coercion_path_step (size : Nat)
    (stepIH : ∀ smaller, smaller < size → CoercionStepAt program registry smaller)
    (pathIH : ∀ smaller, smaller < size → CoercionPathAt program registry smaller) :
    CoercionPathAt program registry size := by
  intro scope context before after steps input outcome sourceType targetType runtime heap typed valid trace
  cases trace with
  | coercionsNil =>
    cases valid
    exact ⟨heap, .refl _, by intro value equal; cases equal; exact typed⟩
  | @coercionsCons headSize tailSize scope context before middle after step steps input converted outcome head tail =>
    cases valid with
    | cons headValid tailValid =>
      have first := stepIH headSize (Size.child_lt_stepSize (by simp)) runtime heap typed headValid head
      have next := pathIH tailSize (Size.child_lt_stepSize (by simp)) runtime
        first.heap_typed (first.value_typed _ rfl) tailValid tail
      exact ⟨next.heap_typed, first.heap_extends.trans next.heap_extends, next.value_typed⟩
  | @coercionsFault headSize scope context before after step steps input failure head =>
    cases valid with
    | cons headValid tailValid =>
      have first := stepIH headSize (Size.child_lt_stepSize (by simp)) runtime heap typed headValid head
      exact ⟨first.heap_typed, first.heap_extends, by intro value equal; cases equal⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.SelectedPreservationProjections
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

theorem ExpressionAt.fault {size : Nat} (sound : ExpressionAt program registry size) :
    FaultPreservation.ExpressionAt program registry size := by
  intro scope context environment before after id failure type runtime covers locals heap typed trace
  have post := sound runtime covers locals heap typed trace
  exact ⟨post.heap_typed, post.heap_extends⟩

theorem ExpressionsAt.fault {size : Nat} (sound : ExpressionsAt program registry size) :
    FaultPreservation.ExpressionsAt program registry size := by
  intro scope context environment before after ids failure types runtime covers locals heap typed trace
  have post := sound runtime covers locals heap typed trace
  exact ⟨post.heap_typed, post.heap_extends⟩

theorem AppliesAt.fault {size : Nat} (sound : AppliesAt program registry size) :
    FaultPreservation.AppliesAt program registry size := by
  intro scope context source before after callable arguments packed failure parameter result runtime heap typed packing argumentTyped trace
  have post := sound runtime heap typed packing argumentTyped trace
  exact ⟨post.heap_typed, post.heap_extends⟩

theorem RawFormAt.fault {size : Nat} (sound : RawFormAt program registry size) :
    FaultPreservation.RawFormAt program registry size := by
  intro scope context environment before after form requirements coercions failure rawType finalType plan runtime covers locals heap occurrence typed valid trace
  have post := sound runtime covers locals heap occurrence typed valid trace
  exact ⟨post.heap_typed, post.heap_extends⟩

theorem CoercionPathAt.fault {size : Nat} (sound : CoercionPathAt program registry size) :
    FaultPreservation.CoercionPathAt program registry size := by
  intro scope context before after steps input failure sourceType targetType runtime heap typed valid trace
  have post := sound runtime heap typed valid trace
  exact ⟨post.heap_typed, post.heap_extends⟩

theorem expression_value {size : Nat} (sound : ExpressionAt program registry size) {scope : Scope} {context : Context} {environment : Dynamic.Environment}
    {before after : Heap} {id : ExpressionId} {value : Value} {type : TypeSystem.Ty}
    (runtime : SourceRuntimeValid program context scope.source) (covers : scope.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment) (heap : HeapWellTyped context before)
    (typed : ExpressionHasType scope.source context id type)
    (trace : Size.Expression program registry size scope context environment before id (.value value) after) :
    ExpressionEvaluationPreserved context before after value type := by
  have post := sound runtime covers locals heap typed trace
  exact ⟨post.value_typed _ rfl, post.heap_typed, post.heap_extends⟩

theorem expressions_values {size : Nat} (sound : ExpressionsAt program registry size) {scope : Scope} {context : Context} {environment : Dynamic.Environment}
    {before after : Heap} {ids : List ExpressionId} {values : List Value} {types : List TypeSystem.Ty}
    (runtime : SourceRuntimeValid program context scope.source) (covers : scope.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment) (heap : HeapWellTyped context before)
    (typed : ExpressionsHaveTypes scope.source context ids types)
    (trace : Size.Expressions program registry size scope context environment before ids (.values values) after) :
    ValuesHaveTypes context after values types ∧ HeapWellTyped context after ∧ HeapTypesExtend before after := by
  have post := sound runtime covers locals heap typed trace
  exact ⟨post.values_typed _ rfl, post.heap_typed, post.heap_extends⟩

theorem raw_form_value {size : Nat} (sound : RawFormAt program registry size) {scope : Scope} {context : Context} {environment : Dynamic.Environment}
    {before after : Heap} {form : ExpressionForm} {requirements : List RequirementId}
    {coercions : List SourceInference.CoercionStep} {value : Value}
    {rawType finalType : TypeSystem.Ty} {plan : ExpressionRequirementPlan}
    (runtime : SourceRuntimeValid program context scope.source) (covers : scope.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment) (heap : HeapWellTyped context before)
    (occurrence : ∃ id node, ContainsExpression scope.source id node ∧ node.form = form ∧ node.rawType = rawType)
    (typed : ExpressionFormHasRawType scope.source context form rawType plan)
    (valid : ExpressionRequirementPlan.Valid context rawType finalType plan requirements coercions)
    (trace : Size.RawForm program registry size scope context environment before form requirements coercions (.value value) after) :
    ValueHasType context after value rawType ∧ HeapWellTyped context after ∧ HeapTypesExtend before after := by
  have post := sound runtime covers locals heap occurrence typed valid trace
  exact ⟨post.value_typed _ rfl, post.heap_typed, post.heap_extends⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.SelectedControlPreservationContracts
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic

structure ControlPreserved (context : Context) (before after : Heap)
    (type : Ty) (outcome : BodyOutcome) : Prop where
  heap_typed : HeapWellTyped context after
  heap_extends : HeapTypesExtend before after
  returned : ∀ value, outcome = .returned value → ValueHasType context after value type

variable (program : Program) (registry : Registry)

def WhileAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context bodyFinal : Context} {environment : Dynamic.Environment}
    {before after : Heap} {condition : ExpressionId} {statements : List StatementId}
    {outcome : BodyOutcome} {control : ControlContext} {facts : BodyFacts},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    ExpressionHasType scope.source context condition .bool →
    StatementsHaveType scope.source control.enterLoop context statements bodyFinal facts →
    Size.While program registry size scope context environment before condition statements outcome after →
    ControlPreserved context before after control.returnType outcome

def MatchAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context : Context} {environment : Dynamic.Environment}
    {before after : Heap} {resolution : MatchResolution} {outcome : BodyOutcome}
    {control : ControlContext} {type : Ty} {caseFacts : List BodyFacts},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    ExpressionHasType scope.source context resolution.scrutinee type →
    MatchCasesHaveType scope.source control context type resolution.cases caseFacts →
    (∀ statements, resolution.defaultBody = some statements →
      ∃ final facts, StatementsHaveType scope.source control context statements final facts) →
    Size.Match program registry size scope context environment before resolution outcome after →
    ControlPreserved context before after control.returnType outcome

def ForItemsAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context staticFinal runtimeFinal : Context} {environment : Dynamic.Environment}
    {before after : Heap} {items : List ForItemForm} {outcome : ForItemsOutcome} {control : ControlContext},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    ForItemsHaveType scope.source control context items staticFinal →
    Size.ForItems program registry size scope context environment before items runtimeFinal outcome after →
    ItemsPreserved context staticFinal runtimeFinal before after outcome

def ForLoopAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context bodyFinal postFinal : Context} {environment : Dynamic.Environment}
    {before after : Heap} {condition : ExpressionId} {post : List ForItemForm} {body : List StatementId}
    {outcome : BodyOutcome} {control : ControlContext} {facts : BodyFacts},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    ExpressionHasType scope.source context condition .bool →
    StatementsHaveType scope.source control.enterLoop context body bodyFinal facts →
    ForItemsHaveType scope.source control.enterLoop context post postFinal →
    Size.ForLoop program registry size scope context environment before condition post body outcome after →
    ControlPreserved context before after control.returnType outcome

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.SelectedBareWritePreservation
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic

theorem bare_target_typed
    {source : TypedSource} {context : Context} {environment : Dynamic.Environment}
    {before : Heap} {place : PlaceResolution} {target : ResolvedPlace} {type : Ty}
    (locals : EnvironmentAgrees before context.locals environment)
    (heap : HeapWellTyped context before)
    (typed : SourcePlaceHasType source context place type)
    (snapshot : BareTarget environment before place target) :
    ∃ rootType, ResolvedPlaceHasType context before target rootType type := by
  cases typed with
  | @intro _ _ rootType finalType writable projections stored =>
      cases snapshot with
      | @intro location cell initial bare lookup read value =>
          rw [bare] at projections
          cases projections
          obtain ⟨scheme, staticLookup, _wellFormed, _monomorphic, bodyEq⟩ := writable.scheme
          obtain ⟨staticLocation, staticCell, actualLookup, actualRead, typeEq, _storage⟩ := locals.lookup staticLookup
          have locationEq := lookup.functional actualLookup
          subst staticLocation
          have cellEq := read.functional actualRead
          subst staticCell
          have rootEq : cell.type = type := typeEq.trans bodyEq
          refine ⟨type, ⟨rootEq, stored, .nil _,  ?_⟩⟩
          exact rootEq ▸ value.preserves (heap cell read.member)

theorem bare_write
    {source : TypedSource} {context : Context} {environment : Dynamic.Environment}
    {before middle after : Heap} {place : PlaceResolution} {target : ResolvedPlace}
    {value updated : Value} {type : Ty}
    (locals : EnvironmentAgrees before context.locals environment)
    (heap : HeapWellTyped context before)
    (targetTyped : SourcePlaceHasType source context place type)
    (snapshot : BareTarget environment before place target)
    (rhs : ExpressionEvaluationPreserved context before middle value type)
    (write : ResolvedPlaceWrites (fun _ replacement => AssignmentValueApplies .equal target.selected value replacement)
      middle target updated after) :
    HeapWellTyped context after ∧ HeapTypesExtend before after := by
  obtain ⟨rootType, targetBefore⟩ := bare_target_typed locals heap targetTyped snapshot
  have targetMiddle := targetBefore.mono rhs.heap_extends
  cases write with
  | intro currentRead rootEq initialValue update heapWrite =>
      rename_i currentCell initial
      have initialTyped := initialValue.preserves (rhs.heap_typed _ currentRead.member)
      have initialRoot : OptionalValueHasType context middle initial rootType := by
        rw [← targetMiddle.root_type, ← rootEq]
        exact initialTyped
      have modification : LeafModificationPreservesType context middle
          (fun _ replacement => AssignmentValueApplies .equal target.selected value replacement) type := by
        intro current replacement _currentTyped applies
        exact applies.equalPreserves rhs.value_typed
      have updatedTyped := update.preserves targetMiddle.projections initialRoot modification
      have updatedCell : ValueHasType context middle updated currentCell.type := by
        rw [rootEq, targetMiddle.root_type]
        exact updatedTyped
      exact ⟨rhs.heap_typed.write currentRead (.some updatedCell) heapWrite,
        rhs.heap_extends.trans (HeapTypesExtend.of_write heapWrite)⟩

theorem bare_write_compound
    {source : TypedSource} {context : Context} {environment : Dynamic.Environment}
    {before middle after : Heap} {place : PlaceResolution} {target : ResolvedPlace}
    {value updated : Value} {operator : Syntax.ValueAssignOp}
    (kind : WordCompoundAssignmentOperator operator)
    (locals : EnvironmentAgrees before context.locals environment)
    (heap : HeapWellTyped context before)
    (targetTyped : SourcePlaceHasType source context place .word)
    (snapshot : BareTarget environment before place target)
    (rhs : ExpressionEvaluationPreserved context before middle value .word)
    (write : ResolvedPlaceWrites (fun _ replacement => AssignmentValueApplies operator target.selected value replacement)
      middle target updated after) :
    HeapWellTyped context after ∧ HeapTypesExtend before after := by
  obtain ⟨rootType, targetBefore⟩ := bare_target_typed locals heap targetTyped snapshot
  have targetMiddle := targetBefore.mono rhs.heap_extends
  cases write with
  | intro currentRead rootEq initialValue update heapWrite =>
      rename_i currentCell initial
      have initialTyped := initialValue.preserves (rhs.heap_typed _ currentRead.member)
      have initialRoot : OptionalValueHasType context middle initial rootType := by
        rw [← targetMiddle.root_type, ← rootEq]
        exact initialTyped
      have modification : LeafModificationPreservesType context middle
          (fun _ replacement => AssignmentValueApplies operator target.selected value replacement) .word := by
        intro current replacement _currentTyped applies
        exact applies.wordCompoundPreserves kind targetMiddle.selected rhs.value_typed
      have updatedTyped := update.preserves targetMiddle.projections initialRoot modification
      have updatedCell : ValueHasType context middle updated currentCell.type := by
        rw [rootEq, targetMiddle.root_type]
        exact updatedTyped
      exact ⟨rhs.heap_typed.write currentRead (.some updatedCell) heapWrite,
        rhs.heap_extends.trans (HeapTypesExtend.of_write heapWrite)⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.SelectedBitNotWritePreservation
/-! A bare unary write preserves the actual raw Word cell type. No expression
preservation hypothesis is needed for the absent right-hand side. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic

theorem bare_write_bitNot
    {source : TypedSource} {context : Context} {environment : Dynamic.Environment}
    {before after : Heap} {assignment : AssignmentResolution} {target : ResolvedPlace}
    {updated : Value}
    (locals : EnvironmentAgrees before context.locals environment)
    (heap : HeapWellTyped context before)
    (typed : SourceBitNotAssignmentValid source context assignment)
    (snapshot : BareTarget environment before assignment.target target)
    (write : ResolvedPlaceWrites (fun _ replacement => BitNotSnapshot target.selected replacement)
      before target updated after) :
    HeapWellTyped context after ∧ HeapTypesExtend before after := by
  cases typed with
  | intro targetTyped _ =>
    obtain ⟨rootType, targetTyped⟩ := bare_target_typed locals heap targetTyped snapshot
    cases write with
    | intro currentRead rootEq initialValue update heapWrite =>
      rename_i currentCell initial
      have initialTyped := initialValue.preserves (heap _ currentRead.member)
      have initialRoot : OptionalValueHasType context before initial rootType := by
        rw [← targetTyped.root_type, ← rootEq]
        exact initialTyped
      have modification : LeafModificationPreservesType context before
          (fun _ replacement => BitNotSnapshot target.selected replacement) .word := by
        intro current replacement _ applies
        exact applies.preserves targetTyped.selected
      have updatedTyped := update.preserves targetTyped.projections initialRoot modification
      have updatedCell : ValueHasType context before updated currentCell.type := by
        rw [rootEq, targetTyped.root_type]
        exact updatedTyped
      exact ⟨heap.write currentRead (.some updatedCell) heapWrite,
        HeapTypesExtend.of_write heapWrite⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.SelectedStatementPreservationSupport
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

theorem statement_head_tail
    {source : TypedSource} {control : ControlContext} {context final : Context}
    {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts,
      StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts ∧
      (∀ expected, rest ≠ [] → headFacts.control.canFallthrough = true →
        BodyCompletes expected facts → BodyCompletes expected tailFacts) ∧
      (headFacts.control.canFallthrough = true → tailFacts.control.canFallthrough = true → facts.control.canFallthrough = true) := by
  cases typed with
  | singleton head =>
      exact ⟨_, _, _, head, .nil _ _, by intro expected nonempty; exact (nonempty rfl).elim, by intro falls _; exact falls⟩
  | cons head tail =>
      exact ⟨_, _, _, head, tail,
        fun _ _ falls complete => BodyCompletes.tail_of_cons_of_hasOutcome falls tail.controlHasOutcome complete,
        ControlSummary.sequence_canFallthrough⟩

theorem statement_form
    {source : TypedSource} {control : ControlContext} {context final : Context}
    {id : StatementId} {node : StatementNode} {shape : StatementForm} {facts : StatementFacts}
    (unique : NodeOccurrencesUnique source)
    (typed : StatementHasType source control context id final facts)
    (contains : ContainsStatement source id node) (form : node.form = shape) :
    Solcore.SourceSemantics.Dynamic.StatementHasType.FormTyping source control context shape final := by
  obtain ⟨actual, found, formTyped⟩ := Solcore.SourceSemantics.Dynamic.StatementHasType.formTyping typed
  have same := Option.some.inj ((lookupStatement?_complete unique found).symm.trans
    (lookupStatement?_complete unique contains))
  cases same
  exact form ▸ formTyped

theorem statement_control_form
    {source : TypedSource} {control : ControlContext} {context final : Context}
    {id : StatementId} {node : StatementNode} {shape : StatementForm} {facts : StatementFacts}
    (unique : NodeOccurrencesUnique source)
    (typed : StatementHasType source control context id final facts)
    (contains : ContainsStatement source id node) (form : node.form = shape) :
    StatementControlFormTyping source control context shape facts := by
  obtain ⟨actual, found, formTyped⟩ := Solcore.SourceSemantics.Dynamic.StatementHasType.controlFormTyping typed
  have same := Option.some.inj ((lookupStatement?_complete unique found).symm.trans
    (lookupStatement?_complete unique contains))
  cases same
  exact form ▸ formTyped

theorem continue_tail
    {size : Nat} {mode : Bool} {scope : Scope} {context staticFinal runtimeFinal : Context}
    {environment : Dynamic.Environment} {before after : Heap} {rest : List StatementId}
    {facts tailFacts : BodyFacts} {headFacts : StatementFacts} {type : Ty} {outcome : BodyOutcome}
    (headFalls : headFacts.control.canFallthrough = true)
    (completeTail : ∀ expected, rest ≠ [] → headFacts.control.canFallthrough = true →
      BodyCompletes expected facts → BodyCompletes expected tailFacts)
    (fallthroughWhole : headFacts.control.canFallthrough = true → tailFacts.control.canFallthrough = true → facts.control.canFallthrough = true)
    (trace : Size.StatementsIn program registry mode size scope context environment before rest runtimeFinal outcome after)
    (post : StatementsPreserved context staticFinal runtimeFinal before after type outcome
      (mode = true → BodyCompletes type tailFacts) (tailFacts.control.canFallthrough = true)) :
    StatementsPreserved context staticFinal runtimeFinal before after type outcome
      (mode = true → BodyCompletes type facts) (facts.control.canFallthrough = true) := by
  refine ⟨post.heap_typed, post.heap_extends, ?_, ?_⟩
  · intro complete value returned
    by_cases empty : rest = []
    · subst rest
      cases trace
      cases returned
    · exact post.returned (fun same => completeTail type empty headFalls (complete same)) value returned
  · intro result equal
    obtain ⟨same, locals, allowed⟩ := post.fallthrough result equal
    exact ⟨same, locals, fallthroughWhole headFalls allowed⟩

theorem StatementsPreserved.prepend
    {context staticFinal runtimeFinal : Context} {before middle after : Heap}
    {type : Ty} {outcome : BodyOutcome} {complete allowed : Prop}
    (extended : HeapTypesExtend before middle)
    (post : StatementsPreserved context staticFinal runtimeFinal middle after type outcome complete allowed) :
    StatementsPreserved context staticFinal runtimeFinal before after type outcome complete allowed :=
  ⟨post.heap_typed, extended.trans post.heap_extends, post.returned, post.fallthrough⟩

theorem StatementsPreserved.transportEntry
    {program : Program} {source : TypedSource} {context middle staticFinal runtimeFinal : Context}
    {before after : Heap} {type : Ty} {outcome : BodyOutcome} {complete allowed : Prop}
    (runtime : SourceRuntimeValid program context source)
    (fields : RuntimeContextFields context middle)
    (post : StatementsPreserved middle staticFinal runtimeFinal before after type outcome complete allowed) :
    StatementsPreserved context staticFinal runtimeFinal before after type outcome complete allowed := by
  have closed := fields.targetClosed runtime.closed
  exact ⟨post.heap_typed.transportClosed fields.signatures.symm closed runtime.closed
      (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
    post.heap_extends,
    fun completion value equal => (post.returned completion value equal).transportClosed
      fields.signatures.symm closed runtime.closed
      (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
    post.fallthrough⟩

theorem fault_statements
    {context staticFinal runtimeFinal : Context} {before after : Heap}
    {type : Ty} {failure : Failure} {complete allowed : Prop}
    (heap : HeapWellTyped context after) (extended : HeapTypesExtend before after) :
    StatementsPreserved context staticFinal runtimeFinal before after type (.fault failure) complete allowed :=
  ⟨heap, extended, (by intro _ value equal; cases equal), (by intro environment equal; cases equal)⟩

theorem terminal_statements
    {context staticFinal runtimeFinal : Context} {before after : Heap}
    {type : Ty} {outcome : BodyOutcome} {complete allowed : Prop}
    (post : ControlPreserved context before after type outcome)
    (terminal : ∀ environment, outcome ≠ .fallthrough environment) :
    StatementsPreserved context staticFinal runtimeFinal before after type outcome complete allowed :=
  ⟨post.heap_typed, post.heap_extends, fun _ => post.returned,
    fun environment equal => (terminal environment equal).elim⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.SelectedBranchPreservation
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

theorem if_branch
    {size testSize branchSize : Nat}
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller)
    (testSmaller : testSize < size) (branchSmaller : branchSize < size)
    {scope : Scope} {context innerContext : Context} {environment : Dynamic.Environment}
    {before middle after : Heap} {condition : ExpressionId} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {truth : Bool} {outcome : BodyOutcome}
    {control : ControlContext} {facts : StatementFacts}
    (runtime : SourceRuntimeValid program context scope.source) (covers : scope.evidence.Covers context)
    (locals : EnvironmentAgrees before context.locals environment) (heap : HeapWellTyped context before)
    (typed : StatementControlFormTyping scope.source control context (.ifThen condition thenBody elseBody) facts)
    (test : Size.Expression program registry testSize scope context environment before condition (.value (.bool truth)) middle)
    (branch : Size.StatementsIn program registry false branchSize scope context environment middle
      (if truth then thenBody else elseBody.getD []) innerContext outcome after) :
    ControlPreserved context before after control.returnType outcome ∧
      (∀ env, outcome = .fallthrough env → facts.control.canFallthrough = true) := by
  cases typed with
  | ifWithoutElse conditionTyped yes =>
      have first := expressionIH testSize testSmaller runtime covers locals heap conditionTyped test
      cases truth with
      | true =>
          have post := statementsIH branchSize branchSmaller runtime covers (locals.mono first.heap_extends)
            first.heap_typed yes branch
          exact ⟨⟨post.heap_typed, first.heap_extends.trans post.heap_extends, post.returned (by simp)⟩,
            fun env equal => ControlSummary.branches_canFallthrough_left (post.fallthrough env equal).2.2⟩
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Option.getD_none] at branch
          cases branch
          exact ⟨⟨first.heap_typed, first.heap_extends, by intro value equal; cases equal⟩,
            fun _ _ => ControlSummary.branches_canFallthrough_right rfl⟩
  | ifWithElse conditionTyped yes no =>
      have first := expressionIH testSize testSmaller runtime covers locals heap conditionTyped test
      cases truth with
      | true =>
          have post := statementsIH branchSize branchSmaller runtime covers (locals.mono first.heap_extends)
            first.heap_typed yes branch
          exact ⟨⟨post.heap_typed, first.heap_extends.trans post.heap_extends, post.returned (by simp)⟩,
            fun env equal => ControlSummary.branches_canFallthrough_left (post.fallthrough env equal).2.2⟩
      | false =>
          have post := statementsIH branchSize branchSmaller runtime covers (locals.mono first.heap_extends)
            first.heap_typed no branch
          exact ⟨⟨post.heap_typed, first.heap_extends.trans post.heap_extends, post.returned (by simp)⟩,
            fun env equal => ControlSummary.branches_canFallthrough_right (post.fallthrough env equal).2.2⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.SelectedMethodPreservation
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

theorem body_all {size : Nat}
    (statementsIH : StatementsAt program registry size)
    {context : Context} {source : TypedSource} {child : Scope}
    {bodyInstance : BodyInstance} {dictionary : EvidenceEnvironment}
    {before bound after : Heap} {arguments : List Dynamic.Value}
    {inputTypes parameterTypes : List Ty}
    {lexicalContext bodyContext finalContext : Context} {facts : BodyFacts}
    {roots : List StatementId} {environment : Dynamic.Environment}
    {outcome : BodyOutcome} {result : Outcome}
    (runtime : SourceRuntimeValid program context source)
    (certificate : BodyInstanceTypingCertificate program bodyInstance inputTypes lexicalContext facts)
    (covers : dictionary.Covers bodyInstance.context)
    (beforeTyped : HeapWellTyped context before)
    (argumentsTyped : ValuesHaveTypes context before arguments inputTypes)
    (rootsEq : StatementRoots bodyInstance.source.roots roots)
    (selected : registry.Closure (globalView bodyInstance dictionary roots) child)
    (parameters : MonoBindersExtend bodyInstance.source.owner bodyInstance.context
      bodyInstance.source.inputs parameterTypes bodyContext)
    (allocate : BindersAllocate [] before bodyInstance.source.inputs arguments environment bound)
    (body : Size.StatementsIn program registry true size child bodyContext environment bound
      roots finalContext outcome after)
    (resultRule : BodyResult bodyInstance.resultType outcome result) :
    OutcomePreserved context before after bodyInstance.resultType result := by
  cases result with
  | value value =>
    have post := body_success (StatementsAt.bodySuccess statementsIH) runtime certificate covers
      beforeTyped argumentsTyped rootsEq selected parameters allocate body resultRule
    exact ⟨post.heap_typed, post.heap_extends, by intro actual equal; cases equal; exact post.value_typed⟩
  | fault failure =>
    have post := SelectedFaultPreservation.method_body_fault (StatementsAt.fault statementsIH)
      runtime certificate covers beforeTyped argumentsTyped rootsEq selected parameters allocate body resultRule
    exact ⟨post.1, post.2, by intro value equal; cases equal⟩

 theorem coercion_step_step (selectedBodies : SelectedBodies program registry) (size : Nat)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller) :
    CoercionStepAt program registry size := by
  intro scope context before after step input outcome runtime heap typed valid trace
  cases trace with
  | coercionPrimitive noMethod applies =>
    obtain ⟨outputTyped, heapTyped, extended⟩ := CoercionStepExecutes.primitivePreserves heap typed applies
    exact ⟨heapTyped, extended, by intro value equal; cases equal; exact outputTyped⟩
  | coercionRequirement _ | coercionPrimitiveInput _ _ _ =>
    exact ⟨heap, .refl _, by intro value equal; cases equal⟩
  | @coercionMethod bodySize scope context before bound after step input bodyInstance dictionary roots child
      parameterTypes bodyContext finalContext bodyEnvironment outcome result method rootsEq selected parameters allocate body resultRule =>
    cases valid with
    | intro profile requirementsProve =>
      have selectedTyped := selectedBodies.methods method rootsEq selected
      obtain ⟨lexicalContext, facts, certificate, resultEq⟩ :=
        selectedTyped.coercionCertificateOfProfile selectedBodies.signatures runtime.signatures
          runtime.requirements.idsUnique profile requirementsProve
      have covers : dictionary.Covers bodyInstance.context := by cases method; assumption
      have post := body_all (statementsIH bodySize (Size.child_lt_stepSize (by simp)))
        runtime certificate covers heap (.cons typed .nil) rootsEq selected parameters allocate body resultRule
      exact ⟨post.heap_typed, post.heap_extends, by
        intro value equal
        exact resultEq ▸ post.value_typed value equal⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.SelectedExpressionFaultPreservation
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.Staging.Recursive.FaultPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

private theorem empty_path_type {context : Context} {source target : Ty}
    (path : CoercionPathValid context source target []) : source = target := by
  cases path
  rfl

private theorem unary_dispatch_same
    {operator : Syntax.UnaryOp} {leftTrait leftMethod rightTrait rightMethod : String}
    (left : UnaryTraitDispatch operator leftTrait leftMethod)
    (right : UnaryTraitDispatch operator rightTrait rightMethod) :
    leftTrait = rightTrait ∧ leftMethod = rightMethod := by
  cases left <;> cases right
  exact ⟨rfl, rfl⟩

private theorem binary_dispatch_same
    {operator : Syntax.BinaryOp} {leftTrait leftMethod rightTrait rightMethod : String}
    (left : BinaryTraitDispatch operator leftTrait leftMethod)
    (right : BinaryTraitDispatch operator rightTrait rightMethod) :
    leftTrait = rightTrait ∧ leftMethod = rightMethod := by
  cases left <;> cases right <;> exact ⟨rfl, rfl⟩

theorem expression_fault_step (selectedBodies : SelectedPreservation.SelectedBodies program registry) (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (expressionsIH : ∀ smaller, smaller < size → ExpressionsAt program registry smaller)
    (appliesIH : ∀ smaller, smaller < size → AppliesAt program registry smaller)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller)
    (rawIH : ∀ smaller, smaller < size → RawFormAt program registry smaller)
    (pathIH : ∀ smaller, smaller < size → CoercionPathAt program registry smaller)
    (expressionAllIH : ∀ smaller, smaller < size → SelectedPreservation.ExpressionAt program registry smaller)
    (expressionsAllIH : ∀ smaller, smaller < size → SelectedPreservation.ExpressionsAt program registry smaller)
    (rawAllIH : ∀ smaller, smaller < size → SelectedPreservation.RawFormAt program registry smaller) :
    ExpressionAt program registry size := by
  intro scope context environment before after id failure type runtime covers locals heap typed trace
  cases trace with
  | @coercedFault rawSize scope context environment before after id node failure contains _nonempty raw =>
      cases typed with
      | @intro _ _ actual rawType plan typedContains typedForm rawTypeEq _ _ valid =>
          have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
            (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
          subst actual
          exact rawIH rawSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap
            ⟨id, node, contains, rfl, rawTypeEq⟩ typedForm valid raw
  | @coercedValue rawSize pathSize scope context environment before middle after id node value outcome contains _nonempty raw path =>
      cases typed with
      | @intro _ _ actual rawType plan typedContains typedForm rawTypeEq _ _ valid =>
          have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
            (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
          subst actual
          obtain ⟨valueTyped, middleTyped, rawExtends⟩ := SelectedPreservation.raw_form_value (rawAllIH _ (Size.child_lt_stepSize (by simp))) runtime covers locals heap
            ⟨id, node, contains, rfl, rawTypeEq⟩ typedForm valid raw
          obtain ⟨afterTyped, pathExtends⟩ := pathIH pathSize (Size.child_lt_stepSize (by simp))
            runtime middleTyped valueTyped valid.outputPath path
          exact ⟨afterTyped, rawExtends.trans pathExtends⟩
  | atomicFault _ atomic _ faultRule =>
      have same := atomic_fault_heap atomic faultRule
      subst after
      exact ⟨heap, .refl _⟩
  | @generalizedLocal pathSize scope context environment before after id node name binder owned
      location cell function substitution produced outcome contains _form _layout _lookup read descriptor contextFields instantiation path =>
      cases typed with
      | @intro _ _ actual rawType plan typedContains _typedForm rawTypeEq _ _ valid =>
          have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
            (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
          subst actual
          have cellTyped := heap cell read.member
          have functionTyped := (cellTyped.generalized_inv descriptor).2
          have definitionCatalog : SignatureCatalogWellFormed function.definitionContext.signatures := by
            rw [← contextFields.signatures, runtime.signatures]
            exact selectedBodies.signatures
          have rawTyped := functionTyped.instantiateHasType definitionCatalog contextFields covers instantiation
          rw [rawTypeEq] at rawTyped
          exact pathIH pathSize (Size.child_lt_stepSize (by simp))
            runtime heap rawTyped valid.outputPath path
  | generalizedLocalRequirement => exact ⟨heap, .refl _⟩
  | @group childSize scope context environment before after id inner outcome occurrence child =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | group innerTyped =>
          exact expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap innerTyped child
  | @pairLeftFault childSize scope context environment before after id left right failure occurrence child =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | tuple elementsTyped =>
          cases elementsTyped with
          | cons firstTyped _ =>
              exact expressionIH childSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap firstTyped child
  | @pairRightFault firstSize secondSize scope context environment before middle after id left right value failure
      occurrence first second =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | tuple elementsTyped =>
          cases elementsTyped with
          | cons firstTyped restTyped =>
              cases restTyped with
              | cons secondTyped _ =>
                  obtain ⟨_valueTyped, middleTyped, firstExtends⟩ := SelectedPreservation.expression_value (expressionAllIH _ (Size.child_lt_stepSize (by simp)))
                    runtime covers locals heap firstTyped first
                  obtain ⟨afterTyped, secondExtends⟩ := expressionIH secondSize (Size.child_lt_stepSize (by simp))
                    runtime covers (locals.mono firstExtends) middleTyped secondTyped second
                  exact ⟨afterTyped, firstExtends.trans secondExtends⟩
  | @tupleFault childrenSize scope context environment before after id elements failure occurrence children =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | tuple elementsTyped =>
          exact expressionsIH childrenSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap elementsTyped children
  | @constructorFault childrenSize scope context environment before after id instantiation arguments failure occurrence children =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | constructor _valid argumentsTyped =>
          exact expressionsIH childrenSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap argumentsTyped children
  | @indexBaseFault firstSize scope context environment before after id base key failure occurrence first =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | index baseTyped _ =>
          exact expressionIH firstSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap baseTyped first
  | @indexKeyFault firstSize secondSize scope context environment before middle after id base key value failure occurrence first second =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | index baseTyped keyTyped =>
          obtain ⟨_valueTyped, middleTyped, firstExtends⟩ := SelectedPreservation.expression_value (expressionAllIH _ (Size.child_lt_stepSize (by simp))) runtime covers locals heap baseTyped first
          obtain ⟨afterTyped, secondExtends⟩ := expressionIH secondSize (Size.child_lt_stepSize (by simp))
            runtime covers (locals.mono firstExtends) middleTyped keyTyped second
          exact ⟨afterTyped, firstExtends.trans secondExtends⟩
  | @indexResult firstSize secondSize scope context environment before middle after id base key baseValue keyValue outcome occurrence first second _result =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | index baseTyped keyTyped =>
          obtain ⟨_baseTyped, middleTyped, firstExtends⟩ := SelectedPreservation.expression_value (expressionAllIH _ (Size.child_lt_stepSize (by simp))) runtime covers locals heap baseTyped first
          obtain ⟨_keyTyped, afterTyped, secondExtends⟩ := SelectedPreservation.expression_value (expressionAllIH _ (Size.child_lt_stepSize (by simp)))
            runtime covers (locals.mono firstExtends) middleTyped keyTyped second
          exact ⟨afterTyped, firstExtends.trans secondExtends⟩
  | @unaryOperandFault childSize scope context environment before after id operator operand failure requirements occurrence child =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | unary operandTyped _ =>
          exact expressionIH childSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap operandTyped child
  | @unaryInvalid childSize scope context environment before after id operator operand input occurrence child _invalid =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | unary operandTyped _ =>
          obtain ⟨_valueTyped, afterTyped, heapExtends⟩ := SelectedPreservation.expression_value (expressionAllIH _ (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap operandTyped child
          exact ⟨afterTyped, heapExtends⟩
  | @binaryLeftFault firstSize scope context environment before after id left operator right failure requirements occurrence first =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | binary leftTyped _ _ =>
          exact expressionIH firstSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap leftTyped first
  | @binaryLeftInvalid firstSize scope context environment before after id left operator right input occurrence first _invalid =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | binary leftTyped _ _ =>
          obtain ⟨_valueTyped, afterTyped, heapExtends⟩ := SelectedPreservation.expression_value (expressionAllIH _ (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap leftTyped first
          exact ⟨afterTyped, heapExtends⟩
  | @binaryRightFault firstSize secondSize scope context environment before middle after id left operator right input failure requirements
      occurrence first _continues second =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | binary leftTyped rightTyped _ =>
          obtain ⟨_valueTyped, middleTyped, firstExtends⟩ := SelectedPreservation.expression_value (expressionAllIH _ (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap leftTyped first
          obtain ⟨afterTyped, secondExtends⟩ := expressionIH secondSize (Size.child_lt_stepSize (by simp))
            runtime covers (locals.mono firstExtends) middleTyped rightTyped second
          exact ⟨afterTyped, firstExtends.trans secondExtends⟩
  | @binaryInvalid firstSize secondSize scope context environment before middle after id left operator right a b
      occurrence first _continues second _invalid =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | binary leftTyped rightTyped _ =>
          obtain ⟨_firstTyped, middleTyped, firstExtends⟩ := SelectedPreservation.expression_value (expressionAllIH _ (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap leftTyped first
          obtain ⟨_secondTyped, afterTyped, secondExtends⟩ := SelectedPreservation.expression_value (expressionAllIH _ (Size.child_lt_stepSize (by simp)))
            runtime covers (locals.mono firstExtends) middleTyped rightTyped second
          exact ⟨afterTyped, firstExtends.trans secondExtends⟩
  | @unaryMethod operandSize bodySize scope context environment before argumentsHeap bound after id operator operand input
      requirements traitName methodName bodyInstance dictionary roots child parameterTypes bodyContext finalContext bodyEnvironment outcome result
      occurrence dispatch method operandTrace rootsEq selected parameters allocate body resultRule =>
      obtain ⟨_raw, _plan, formTyped, planValid⟩ := expression_form_plan runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | unary operandTyped operatorTyped =>
          cases planValid with
          | ordinary _ _ requirementsEq =>
              simp [coercionRequirementIds] at requirementsEq
              subst requirements
              obtain ⟨inputTyped, argumentsHeapTyped, operandExtends⟩ := SelectedPreservation.expression_value (expressionAllIH _ (Size.child_lt_stepSize (by simp)))
                runtime covers locals heap operandTyped operandTrace
              cases operatorTyped with
              | logicalNot | wordBitNot | integerBitNot => cases method
              | trait staticDispatch profile requirementsProve =>
                  have same := unary_dispatch_same staticDispatch dispatch
                  rcases same with ⟨rfl, rfl⟩
                  obtain ⟨lexicalContext, facts, certificate, _resultEq⟩ :=
                    (selectedBodies.methods method rootsEq selected).certificateOfProfile selectedBodies.signatures runtime.signatures runtime.requirements.idsUnique
                      profile requirementsProve
                  have argumentsTyped := ValuesHaveTypes.cons inputTyped (.nil)
                  obtain ⟨afterTyped, bodyExtends⟩ := SelectedFaultPreservation.method_body_fault
                    (statementsIH bodySize (Size.child_lt_stepSize (by simp))) runtime certificate
                    (by cases method; assumption) argumentsHeapTyped argumentsTyped rootsEq selected parameters allocate body resultRule
                  exact ⟨afterTyped, operandExtends.trans bodyExtends⟩
  | @binaryMethod leftSize rightSize bodySize scope context environment before middle argumentsHeap bound after id left operator right a b
      requirements traitName methodName bodyInstance dictionary roots child parameterTypes bodyContext finalContext bodyEnvironment outcome result
      occurrence dispatch method first continues second rootsEq selected parameters allocate body resultRule =>
      obtain ⟨_raw, _plan, formTyped, planValid⟩ := expression_form_plan runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | binary leftTyped rightTyped operatorTyped =>
          cases planValid with
          | ordinary _ _ requirementsEq =>
              simp [coercionRequirementIds] at requirementsEq
              subst requirements
              obtain ⟨leftValueTyped, middleTyped, firstExtends⟩ := SelectedPreservation.expression_value (expressionAllIH _ (Size.child_lt_stepSize (by simp)))
                runtime covers locals heap leftTyped first
              obtain ⟨rightValueTyped, argumentsHeapTyped, secondExtends⟩ := SelectedPreservation.expression_value (expressionAllIH _ (Size.child_lt_stepSize (by simp)))
                runtime covers (locals.mono firstExtends) middleTyped rightTyped second
              cases operatorTyped with
              | wordArithmetic | integerArithmetic | wordShift | wordUnchecked | wordComparison | integerComparison | booleanAnd | booleanOr => cases method
              | trait staticDispatch profile requirementsProve =>
                have same := binary_dispatch_same staticDispatch dispatch
                rcases same with ⟨rfl, rfl⟩
                obtain ⟨lexicalContext, facts, certificate, _resultEq⟩ :=
                  (selectedBodies.methods method rootsEq selected).certificateOfProfile selectedBodies.signatures runtime.signatures runtime.requirements.idsUnique
                    profile requirementsProve
                have argumentsTyped := ValuesHaveTypes.cons (leftValueTyped.mono secondExtends)
                  (.cons rightValueTyped (.nil))
                obtain ⟨afterTyped, bodyExtends⟩ := SelectedFaultPreservation.method_body_fault
                  (statementsIH bodySize (Size.child_lt_stepSize (by simp))) runtime certificate
                  (by cases method; assumption) argumentsHeapTyped argumentsTyped rootsEq selected parameters allocate body resultRule
                exact ⟨afterTyped, firstExtends.trans (secondExtends.trans bodyExtends)⟩
  | @conditional testSize branchSize scope context environment before middle after id condition yes no truth outcome
      occurrence test branch =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | conditional conditionTyped yesTyped noTyped =>
          obtain ⟨_truthTyped, middleTyped, testExtends⟩ := SelectedPreservation.expression_value (expressionAllIH _ (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap conditionTyped test
          have branchTyped : ExpressionHasType scope.source context (if truth then yes else no) _raw := by
            split <;> assumption
          obtain ⟨afterTyped, branchExtends⟩ := expressionIH branchSize (Size.child_lt_stepSize (by simp))
            runtime covers (locals.mono testExtends) middleTyped branchTyped branch
          exact ⟨afterTyped, testExtends.trans branchExtends⟩
  | @conditionalFault testSize scope context environment before after id condition yes no failure occurrence test =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | conditional conditionTyped _ _ =>
          exact expressionIH testSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap conditionTyped test
  | @builtinArgumentsFault childrenSize scope context environment before after id callee arguments function failure
      occurrence children =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | builtinCall _calleeValid argumentsTyped =>
          exact expressionsIH childrenSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap argumentsTyped children
  | @builtinApplied childrenSize invocationSize scope context environment before argumentsHeap after
      id callee arguments function values outcome occurrence children invocation =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | builtinCall _calleeValid argumentsTyped =>
          obtain ⟨valuesTyped, argumentsHeapTyped, argumentExtends⟩ := SelectedPreservation.expressions_values (expressionsAllIH _ (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap argumentsTyped children
          have calleeTyped : ValueHasType context argumentsHeap (.builtin ⟨function⟩)
              (.function (TypeSystem.Ty.productMany function.parameterTypes) function.returnType) := by
            simpa [BuiltinFunctionId.type] using
              (ValueHasType.builtin (context := context) (heap := argumentsHeap) ⟨function⟩)
          obtain ⟨packed, packing⟩ := ValuesPack.exists_pack values
          have argumentTyped := packing.hasType valuesTyped
          obtain ⟨afterTyped, invocationExtends⟩ := appliesIH invocationSize (Size.child_lt_stepSize (by simp))
            runtime argumentsHeapTyped calleeTyped packing argumentTyped invocation
          exact ⟨afterTyped, argumentExtends.trans invocationExtends⟩
  | @directArgumentsFault childrenSize scope context environment before after id callee arguments instantiation name failure requirements
      occurrence _calleeOccurrence children =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | directCall _calleeTyped _application argumentsTyped =>
          exact expressionsIH childrenSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap argumentsTyped children
  | @directApplied childrenSize invocationSize scope context environment before argumentsHeap after
      id callee arguments instantiation name values evidence outcome requirements occurrence _calleeOccurrence valid children callEvidence invocation =>
      obtain ⟨raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | @directCall _ callee arguments instantiation parameterTypes resultType predicates _calleeTyped application argumentsTyped =>
          obtain ⟨valuesTyped, argumentsHeapTyped, argumentExtends⟩ := SelectedPreservation.expressions_values (expressionsAllIH _ (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap argumentsTyped children
          cases application with
          | intro _signature _admissible _declaration _parameters _result functionType _predicates =>
              cases callEvidence with
              | intro _coercions _requirements produces =>
                  have calleeTyped : ValueHasType context argumentsHeap (.global ⟨instantiation, evidence⟩)
                      (.function (Ty.productMany parameterTypes) raw) := by
                    rw [← functionType]
                    exact .global valid ⟨produces.valid, by
                      intro predicate member
                      exact produces.supplies predicate member⟩
                  obtain ⟨packed, packing⟩ := ValuesPack.exists_pack values
                  have argumentTyped := packing.hasType valuesTyped
                  obtain ⟨afterTyped, invocationExtends⟩ := appliesIH invocationSize (Size.child_lt_stepSize (by simp))
                    runtime argumentsHeapTyped calleeTyped packing argumentTyped invocation
                  exact ⟨afterTyped, argumentExtends.trans invocationExtends⟩
  | @calleeFault childSize scope context environment before after id callee arguments metadata failure occurrence child =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | indirectCall calleeTyped _ _ =>
          exact expressionIH childSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap calleeTyped child
  | @notCallable childSize scope context environment before after id callee arguments metadata value occurrence child _invalid =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | indirectCall calleeTyped _ _ =>
          obtain ⟨_valueTyped, afterTyped, heapExtends⟩ := SelectedPreservation.expression_value (expressionAllIH _ (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap calleeTyped child
          exact ⟨afterTyped, heapExtends⟩
  | @rejected childSize scope context environment before after id callee arguments metadata value reason occurrence child _guard =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | indirectCall calleeTyped _ _ =>
          obtain ⟨_valueTyped, afterTyped, heapExtends⟩ := SelectedPreservation.expression_value (expressionAllIH _ (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap calleeTyped child
          exact ⟨afterTyped, heapExtends⟩
  | @argumentsFault childSize childrenSize scope context environment before middle after id callee arguments metadata value failure
      occurrence child _guard children =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | indirectCall calleeTyped argumentsTyped _ =>
          obtain ⟨_valueTyped, middleTyped, calleeExtends⟩ := SelectedPreservation.expression_value (expressionAllIH _ (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap calleeTyped child
          obtain ⟨afterTyped, argumentExtends⟩ := expressionsIH childrenSize (Size.child_lt_stepSize (by simp))
            runtime covers (locals.mono calleeExtends) middleTyped argumentsTyped children
          exact ⟨afterTyped, calleeExtends.trans argumentExtends⟩
  | @sourceArity childSize childrenSize scope context environment before middle after id callee arguments metadata value values
      occurrence child _guard children _mismatch =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | indirectCall calleeTyped argumentsTyped _ =>
          obtain ⟨_valueTyped, middleTyped, calleeExtends⟩ := SelectedPreservation.expression_value (expressionAllIH _ (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap calleeTyped child
          obtain ⟨_valuesTyped, afterTyped, argumentExtends⟩ := SelectedPreservation.expressions_values (expressionsAllIH _ (Size.child_lt_stepSize (by simp)))
            runtime covers (locals.mono calleeExtends) middleTyped argumentsTyped children
          exact ⟨afterTyped, calleeExtends.trans argumentExtends⟩
  | @applied childSize childrenSize invocationSize scope context environment before calleeHeap argumentsHeap after
      id callee arguments metadata value values outcome occurrence uncoerced child _guard children _arity invocation =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | indirectCall calleeTyped argumentsTyped application =>
          obtain ⟨valueTyped, calleeHeapTyped, calleeExtends⟩ := SelectedPreservation.expression_value (expressionAllIH _ (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap calleeTyped child
          obtain ⟨valuesTyped, argumentsHeapTyped, argumentExtends⟩ := SelectedPreservation.expressions_values (expressionsAllIH _ (Size.child_lt_stepSize (by simp)))
            runtime covers (locals.mono calleeExtends) calleeHeapTyped argumentsTyped children
          obtain ⟨packed, packing⟩ := ValuesPack.exists_pack values
          have packedTyped := packing.hasType valuesTyped
          cases application with
          | intro _count beforeEq _afterEq path =>
              rw [uncoerced] at path
              rw [← beforeEq] at packedTyped
              have argumentTyped := empty_path_type path ▸ packedTyped
              obtain ⟨afterTyped, invocationExtends⟩ := appliesIH invocationSize (Size.child_lt_stepSize (by simp))
                runtime argumentsHeapTyped (valueTyped.mono argumentExtends) packing argumentTyped invocation
              exact ⟨afterTyped, calleeExtends.trans (argumentExtends.trans invocationExtends)⟩

private structure PreservedAt (program : Program) (registry : Registry) (size : Nat) : Prop where
  expression : ExpressionAt program registry size
  expressions : ExpressionsAt program registry size
  applies : AppliesAt program registry size
  statements : StatementsAt program registry size
  whileLoop : WhileAt program registry size
  matchArms : MatchAt program registry size
  forItems : ForItemsAt program registry size
  forLoop : ForLoopAt program registry size
  rawForm : RawFormAt program registry size
  coercionStep : CoercionStepAt program registry size
  coercionPath : CoercionPathAt program registry size

end Solcore.SourceSemantics.Staging.Recursive.FaultPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.SelectedRawPreservation
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

theorem raw_form_step (size : Nat)
    (expressionsIH : ∀ smaller, smaller < size → ExpressionsAt program registry smaller)
    (appliesIH : ∀ smaller, smaller < size → AppliesAt program registry smaller) :
    RawFormAt program registry size := by
  intro scope context environment before after form requirements coercions outcome rawType finalType plan
    runtime covers locals heap occurrence typed _valid trace
  cases trace with
  | rawAtomicValue atomic valueRule =>
      have post := atomic_value runtime covers locals heap occurrence typed atomic valueRule
      exact ⟨post.heap_typed, post.heap_extends, by intro value equal; cases equal; exact post.value_typed⟩
  | rawAtomicFault atomic faultRule =>
      have same := FaultPreservation.atomic_fault_heap atomic faultRule
      subst after
      exact ⟨heap, .refl _, by intro value equal; cases equal⟩
  | @rawDirectArgumentsFault childrenSize scope context environment before after callee arguments instantiation name failure requirements coercions _calleeOccurrence children =>
      cases typed with
      | directCall _calleeTyped _application argumentsTyped =>
          have post := expressionsIH childrenSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap argumentsTyped children
          exact ⟨post.heap_typed, post.heap_extends, by intro value equal; cases equal⟩
  | @rawDirectApplied childrenSize invocationSize scope context environment before argumentsHeap after callee arguments instantiation name values evidence outcome requirements coercions _calleeOccurrence valid children callEvidence invocation =>
      cases typed with
      | @directCall _ callee arguments instantiation parameterTypes resultType predicates _calleeTyped application argumentsTyped =>
          have args := expressionsIH childrenSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap argumentsTyped children
          cases application with
          | intro _signature _admissible _declaration _parameters _result functionType _predicates =>
              cases callEvidence with
              | intro _coercions _requirements produces =>
                  have calleeTyped : ValueHasType context argumentsHeap (.global ⟨instantiation, evidence⟩)
                      (.function (Ty.productMany parameterTypes) rawType) := by
                    rw [← functionType]
                    exact .global valid ⟨produces.valid, by
                      intro predicate member
                      exact produces.supplies predicate member⟩
                  obtain ⟨packed, packing⟩ := ValuesPack.exists_pack values
                  have argumentTyped := packing.hasType (args.values_typed _ rfl)
                  have post := appliesIH invocationSize (Size.child_lt_stepSize (by simp))
                    runtime args.heap_typed calleeTyped packing argumentTyped invocation
                  exact ⟨post.heap_typed, args.heap_extends.trans post.heap_extends, post.value_typed⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.SelectedExpressionSuccessPreservation
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

private theorem empty_path_type {context : Context} {source target : Ty}
    (path : CoercionPathValid context source target []) : source = target := by
  cases path
  rfl

private theorem expression_form_exact {scope : Scope} {context : Context} {id : ExpressionId}
    {form : ExpressionForm} {type : Ty} {requirements : List RequirementId}
    (unique : NodeOccurrencesUnique scope.source)
    (typed : ExpressionHasType scope.source context id type) (occurrence : Occurrence scope id form requirements) :
    ∃ plan, ExpressionFormHasRawType scope.source context form type plan ∧
      ExpressionRequirementPlan.Valid context type type plan requirements [] := by
  obtain ⟨raw, plan, formTyped, valid⟩ := FaultPreservation.expression_form_plan unique typed occurrence
  have equal := empty_path_type valid.outputPath
  subst raw
  exact ⟨plan, formTyped, valid⟩

private theorem unary_dispatch_same
    {operator : Syntax.UnaryOp} {leftTrait leftMethod rightTrait rightMethod : String}
    (left : UnaryTraitDispatch operator leftTrait leftMethod)
    (right : UnaryTraitDispatch operator rightTrait rightMethod) :
    leftTrait = rightTrait ∧ leftMethod = rightMethod := by
  cases left <;> cases right
  exact ⟨rfl, rfl⟩

private theorem binary_dispatch_same
    {operator : Syntax.BinaryOp} {leftTrait leftMethod rightTrait rightMethod : String}
    (left : BinaryTraitDispatch operator leftTrait leftMethod)
    (right : BinaryTraitDispatch operator rightTrait rightMethod) :
    leftTrait = rightTrait ∧ leftMethod = rightMethod := by
  cases left <;> cases right <;> exact ⟨rfl, rfl⟩

theorem expression_value_step (selectedBodies : SelectedBodies program registry) (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (expressionsIH : ∀ smaller, smaller < size → ExpressionsAt program registry smaller)
    (appliesIH : ∀ smaller, smaller < size → AppliesAt program registry smaller)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller)
    (rawIH : ∀ smaller, smaller < size → RawFormAt program registry smaller)
    (pathIH : ∀ smaller, smaller < size → CoercionPathAt program registry smaller)
    {scope : Scope} {context : Context} {environment : Dynamic.Environment}
    {before after : Heap} {id : ExpressionId} {value : Value} {type : Ty}
    (runtime : SourceRuntimeValid program context scope.source) (covers : scope.evidence.Covers context)
    (locals : EnvironmentAgrees before context.locals environment) (heap : HeapWellTyped context before)
    (typed : ExpressionHasType scope.source context id type)
    (trace : Size.Expression program registry size scope context environment before id (.value value) after) :
    ExpressionEvaluationPreserved context before after value type := by
  cases trace with
  | @atomicValue scope context environment before after id node value contains atomic uncoerced valueRule =>
      cases typed with
      | @intro _ _ actual rawType plan typedContains typedForm rawTypeEq _ _ valid =>
          have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
            (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
          subst actual
          have post := atomic_value runtime covers locals heap ⟨id, node, contains, rfl, rawTypeEq⟩ typedForm atomic valueRule
          have path := valid.outputPath
          rw [uncoerced] at path
          exact ⟨empty_path_type path ▸ post.value_typed, post.heap_typed, post.heap_extends⟩
  | @coercedValue rawSize pathSize scope context environment before middle after id node value outcome contains _nonempty raw path =>
      cases typed with
      | @intro _ _ actual rawType plan typedContains typedForm rawTypeEq _ _ valid =>
          have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
            (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
          subst actual
          have rawPost := rawIH rawSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap
            ⟨id, node, contains, rfl, rawTypeEq⟩ typedForm valid raw
          have post := pathIH pathSize (Size.child_lt_stepSize (by simp))
            runtime rawPost.heap_typed (rawPost.value_typed _ rfl) valid.outputPath path
          exact ⟨post.value_typed _ rfl, post.heap_typed, rawPost.heap_extends.trans post.heap_extends⟩
  | @generalizedLocal pathSize scope context environment before after id node name binder owned
      location cell function substitution produced outcome contains _form _layout _lookup read descriptor contextFields instantiation path =>
      cases typed with
      | @intro _ _ actual rawType plan typedContains _typedForm rawTypeEq _ _ valid =>
          have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
            (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
          subst actual
          have cellTyped := heap cell read.member
          have functionTyped := (cellTyped.generalized_inv descriptor).2
          have definitionCatalog : SignatureCatalogWellFormed function.definitionContext.signatures := by
            rw [← contextFields.signatures, runtime.signatures]
            exact selectedBodies.signatures
          have rawTyped := functionTyped.instantiateHasType definitionCatalog contextFields covers instantiation
          rw [rawTypeEq] at rawTyped
          have post := pathIH pathSize (Size.child_lt_stepSize (by simp))
            runtime heap rawTyped valid.outputPath path
          exact ⟨post.value_typed _ rfl, post.heap_typed, post.heap_extends⟩
  | @group childSize scope context environment before after id inner outcome occurrence child =>
      obtain ⟨_plan, formTyped, _valid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | group innerTyped =>
          exact expression_value (expressionIH childSize (Size.child_lt_stepSize (by simp))) runtime covers locals heap innerTyped child
  | @pair firstSize secondSize scope context environment before middle after id left right a b occurrence first second =>
      obtain ⟨_plan, formTyped, _valid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | tuple elementsTyped =>
          cases elementsTyped with
          | cons firstTyped restTyped =>
              cases restTyped with
              | cons secondTyped nilTyped =>
                  cases nilTyped
                  have leftPost := expressionIH firstSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap firstTyped first
                  have rightPost := expressionIH secondSize (Size.child_lt_stepSize (by simp)) runtime covers
                    (locals.mono leftPost.heap_extends) leftPost.heap_typed secondTyped second
                  exact ⟨.product ((leftPost.value_typed _ rfl).mono rightPost.heap_extends) (rightPost.value_typed _ rfl),
                    rightPost.heap_typed, leftPost.heap_extends.trans rightPost.heap_extends⟩
  | @tupleValue childrenSize scope context environment before after id elements values packed occurrence children pack =>
      obtain ⟨_plan, formTyped, _valid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | tuple elementsTyped =>
          have post := expressionsIH childrenSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap elementsTyped children
          exact ⟨pack.hasType (post.values_typed _ rfl), post.heap_typed, post.heap_extends⟩
  | @constructorValue childrenSize scope context environment before after id instantiation arguments values occurrence valid children =>
      obtain ⟨_plan, formTyped, _valid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | constructor _valid argumentsTyped =>
          have post := expressionsIH childrenSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap argumentsTyped children
          exact ⟨.constructed valid (post.values_typed _ rfl), post.heap_typed, post.heap_extends⟩
  | @indexResult firstSize secondSize scope context environment before middle after id base key baseValue keyValue outcome occurrence first second result =>
      obtain ⟨_plan, formTyped, _valid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | index baseTyped keyTyped =>
          have leftPost := expressionIH firstSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap baseTyped first
          have rightPost := expressionIH secondSize (Size.child_lt_stepSize (by simp)) runtime covers
            (locals.mono leftPost.heap_extends) leftPost.heap_typed keyTyped second
          have baseAfter := (leftPost.value_typed _ rfl).mono rightPost.heap_extends
          cases result with
          | found shape located =>
              subst baseValue
              obtain ⟨rfl, rfl, entriesTyped⟩ := baseAfter.mappingComponents
              exact ⟨located.preserves entriesTyped, rightPost.heap_typed, leftPost.heap_extends.trans rightPost.heap_extends⟩
          | default shape _absent defaulted =>
              subst baseValue
              obtain ⟨rfl, rfl, _entriesTyped⟩ := baseAfter.mappingComponents
              exact ⟨defaulted.hasType, rightPost.heap_typed, leftPost.heap_extends.trans rightPost.heap_extends⟩
  | @unary childSize scope context environment before after id operator operand input output occurrence child applies =>
      obtain ⟨_plan, formTyped, valid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | unary operandTyped operatorTyped =>
          cases valid with
          | ordinary _ _ requirementsEq =>
              simp [coercionRequirementIds] at requirementsEq
              subst requirementsEq
              have post := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap operandTyped child
              cases operatorTyped with
              | logicalNot => exact ⟨applies.preserves .logicalNot (post.value_typed _ rfl), post.heap_typed, post.heap_extends⟩
              | wordBitNot => exact ⟨applies.preserves .wordBitNot (post.value_typed _ rfl), post.heap_typed, post.heap_extends⟩
              | integerBitNot => exact ⟨applies.preserves .integerBitNot (post.value_typed _ rfl), post.heap_typed, post.heap_extends⟩
              | trait _dispatch profile requirementsProve => cases requirementsProve; cases profile
  | @binaryShortCircuit firstSize scope context environment before after id left operator right input output occurrence first circuit =>
      obtain ⟨_plan, formTyped, valid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | binary leftTyped _rightTyped operatorTyped =>
          have post := expressionIH firstSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap leftTyped first
          cases circuit <;> cases operatorTyped
          all_goals try { rename_i kind; cases kind }
          all_goals try { rename_i dispatch profile proof; cases dispatch }
          all_goals exact ⟨.bool _, post.heap_typed, post.heap_extends⟩
  | @binary firstSize secondSize scope context environment before middle after id left operator right a b output occurrence first _continues second applies =>
      obtain ⟨_plan, formTyped, valid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | binary leftTyped rightTyped operatorTyped =>
          cases valid with
          | ordinary _ _ requirementsEq =>
              simp [coercionRequirementIds] at requirementsEq
              subst requirementsEq
              have firstPost := expressionIH firstSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap leftTyped first
              have secondPost := expressionIH secondSize (Size.child_lt_stepSize (by simp)) runtime covers
                (locals.mono firstPost.heap_extends) firstPost.heap_typed rightTyped second
              have aTyped := (firstPost.value_typed _ rfl).mono secondPost.heap_extends
              have bTyped := secondPost.value_typed _ rfl
              cases operatorTyped with
              | wordArithmetic kind => exact ⟨applies.preserves (.wordArithmetic kind) aTyped bTyped, secondPost.heap_typed, firstPost.heap_extends.trans secondPost.heap_extends⟩
              | wordShift kind => exact ⟨applies.preserves (.wordShift kind) aTyped bTyped, secondPost.heap_typed, firstPost.heap_extends.trans secondPost.heap_extends⟩
              | wordUnchecked kind => exact ⟨applies.preserves (.wordUnchecked kind) aTyped bTyped, secondPost.heap_typed, firstPost.heap_extends.trans secondPost.heap_extends⟩
              | integerArithmetic kind => exact ⟨applies.preserves (.integerArithmetic kind) aTyped bTyped, secondPost.heap_typed, firstPost.heap_extends.trans secondPost.heap_extends⟩
              | wordComparison kind => exact ⟨applies.preserves (.wordComparison kind) aTyped bTyped, secondPost.heap_typed, firstPost.heap_extends.trans secondPost.heap_extends⟩
              | integerComparison kind => exact ⟨applies.preserves (.integerComparison kind) aTyped bTyped, secondPost.heap_typed, firstPost.heap_extends.trans secondPost.heap_extends⟩
              | booleanAnd => exact ⟨applies.preserves .booleanAnd aTyped bTyped, secondPost.heap_typed, firstPost.heap_extends.trans secondPost.heap_extends⟩
              | booleanOr => exact ⟨applies.preserves .booleanOr aTyped bTyped, secondPost.heap_typed, firstPost.heap_extends.trans secondPost.heap_extends⟩
              | trait _dispatch profile requirementsProve => cases requirementsProve; cases profile
  | @unaryMethod operandSize bodySize scope context environment before argumentsHeap bound after id operator operand input
      requirements traitName methodName bodyInstance dictionary roots child parameterTypes bodyContext finalContext bodyEnvironment outcome result
      occurrence dispatch method operandTrace rootsEq selected parameters allocate body resultRule =>
      obtain ⟨_plan, formTyped, planValid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | unary operandTyped operatorTyped =>
          cases planValid with
          | ordinary _ _ requirementsEq =>
              simp [coercionRequirementIds] at requirementsEq
              subst requirements
              obtain ⟨inputTyped, argumentsHeapTyped, operandExtends⟩ := expression_value (expressionIH _ (Size.child_lt_stepSize (by simp)))
                runtime covers locals heap operandTyped operandTrace
              cases operatorTyped with
              | logicalNot | wordBitNot | integerBitNot => cases method
              | trait staticDispatch profile requirementsProve =>
                  have same := unary_dispatch_same staticDispatch dispatch
                  rcases same with ⟨rfl, rfl⟩
                  obtain ⟨lexicalContext, facts, certificate, resultEq⟩ :=
                    (selectedBodies.methods method rootsEq selected).certificateOfProfile selectedBodies.signatures runtime.signatures runtime.requirements.idsUnique
                      profile requirementsProve
                  have argumentsTyped := ValuesHaveTypes.cons inputTyped (.nil)
                  obtain ⟨resultTyped, afterTyped, bodyExtends⟩ := body_success
                    (StatementsAt.bodySuccess (statementsIH bodySize (Size.child_lt_stepSize (by simp)))) runtime certificate
                    (by cases method; assumption) argumentsHeapTyped argumentsTyped rootsEq selected parameters allocate body resultRule
                  exact ⟨(by simpa [resultEq, Ty.productMany] using resultTyped), afterTyped, operandExtends.trans bodyExtends⟩
  | @binaryMethod leftSize rightSize bodySize scope context environment before middle argumentsHeap bound after id left operator right a b
      requirements traitName methodName bodyInstance dictionary roots child parameterTypes bodyContext finalContext bodyEnvironment outcome result
      occurrence dispatch method first continues second rootsEq selected parameters allocate body resultRule =>
      obtain ⟨_plan, formTyped, planValid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | binary leftTyped rightTyped operatorTyped =>
          cases planValid with
          | ordinary _ _ requirementsEq =>
              simp [coercionRequirementIds] at requirementsEq
              subst requirements
              obtain ⟨leftValueTyped, middleTyped, firstExtends⟩ := expression_value (expressionIH _ (Size.child_lt_stepSize (by simp)))
                runtime covers locals heap leftTyped first
              obtain ⟨rightValueTyped, argumentsHeapTyped, secondExtends⟩ := expression_value (expressionIH _ (Size.child_lt_stepSize (by simp)))
                runtime covers (locals.mono firstExtends) middleTyped rightTyped second
              cases operatorTyped with
              | wordArithmetic | integerArithmetic | wordShift | wordUnchecked | wordComparison | integerComparison | booleanAnd | booleanOr => cases method
              | trait staticDispatch profile requirementsProve =>
                have same := binary_dispatch_same staticDispatch dispatch
                rcases same with ⟨rfl, rfl⟩
                obtain ⟨lexicalContext, facts, certificate, resultEq⟩ :=
                  (selectedBodies.methods method rootsEq selected).certificateOfProfile selectedBodies.signatures runtime.signatures runtime.requirements.idsUnique
                    profile requirementsProve
                have argumentsTyped := ValuesHaveTypes.cons (leftValueTyped.mono secondExtends)
                  (.cons rightValueTyped (.nil))
                obtain ⟨resultTyped, afterTyped, bodyExtends⟩ := body_success
                  (StatementsAt.bodySuccess (statementsIH bodySize (Size.child_lt_stepSize (by simp)))) runtime certificate
                  (by cases method; assumption) argumentsHeapTyped argumentsTyped rootsEq selected parameters allocate body resultRule
                exact ⟨(by simpa [resultEq, Ty.productMany] using resultTyped), afterTyped, firstExtends.trans (secondExtends.trans bodyExtends)⟩
  | @conditional testSize branchSize scope context environment before middle after id condition yes no truth outcome
      occurrence test branch =>
      obtain ⟨_plan, formTyped, _planValid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | conditional conditionTyped yesTyped noTyped =>
          obtain ⟨_truthTyped, middleTyped, testExtends⟩ := expression_value (expressionIH _ (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap conditionTyped test
          have branchTyped : ExpressionHasType scope.source context (if truth then yes else no) type := by
            split <;> assumption
          obtain ⟨resultTyped, afterTyped, branchExtends⟩ := expression_value (expressionIH branchSize (Size.child_lt_stepSize (by simp)))
            runtime covers (locals.mono testExtends) middleTyped branchTyped branch
          exact ⟨resultTyped, afterTyped, testExtends.trans branchExtends⟩
  | @builtinApplied childrenSize invocationSize scope context environment before argumentsHeap after
      id callee arguments function values outcome occurrence children invocation =>
      obtain ⟨_plan, formTyped, _planValid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | builtinCall _calleeValid argumentsTyped =>
          obtain ⟨valuesTyped, argumentsHeapTyped, argumentExtends⟩ := expressions_values (expressionsIH _ (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap argumentsTyped children
          have calleeTyped : ValueHasType context argumentsHeap (.builtin ⟨function⟩)
              (.function (TypeSystem.Ty.productMany function.parameterTypes) function.returnType) := by
            simpa [BuiltinFunctionId.type] using
              (ValueHasType.builtin (context := context) (heap := argumentsHeap) ⟨function⟩)
          obtain ⟨packed, packing⟩ := ValuesPack.exists_pack values
          have argumentTyped := packing.hasType valuesTyped
          have post := appliesIH invocationSize (Size.child_lt_stepSize (by simp))
            runtime argumentsHeapTyped calleeTyped packing argumentTyped invocation
          exact ⟨post.value_typed _ rfl, post.heap_typed, argumentExtends.trans post.heap_extends⟩
  | @directApplied childrenSize invocationSize scope context environment before argumentsHeap after
      id callee arguments instantiation name values evidence outcome requirements occurrence _calleeOccurrence valid children callEvidence invocation =>
      obtain ⟨_plan, formTyped, _planValid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | @directCall _ callee arguments instantiation parameterTypes resultType predicates _calleeTyped application argumentsTyped =>
          obtain ⟨valuesTyped, argumentsHeapTyped, argumentExtends⟩ := expressions_values (expressionsIH _ (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap argumentsTyped children
          cases application with
          | intro _signature _admissible _declaration _parameters _result functionType _predicates =>
              cases callEvidence with
              | intro _coercions _requirements produces =>
                  have calleeTyped : ValueHasType context argumentsHeap (.global ⟨instantiation, evidence⟩)
                      (.function (Ty.productMany parameterTypes) type) := by
                    rw [← functionType]
                    exact .global valid ⟨produces.valid, by
                      intro predicate member
                      exact produces.supplies predicate member⟩
                  obtain ⟨packed, packing⟩ := ValuesPack.exists_pack values
                  have argumentTyped := packing.hasType valuesTyped
                  have post := appliesIH invocationSize (Size.child_lt_stepSize (by simp))
                    runtime argumentsHeapTyped calleeTyped packing argumentTyped invocation
                  exact ⟨post.value_typed _ rfl, post.heap_typed, argumentExtends.trans post.heap_extends⟩
  | @applied childSize childrenSize invocationSize scope context environment before calleeHeap argumentsHeap after
      id callee arguments metadata value values outcome occurrence uncoerced child _guard children _arity invocation =>
      obtain ⟨_plan, formTyped, _planValid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | indirectCall calleeTyped argumentsTyped application =>
          obtain ⟨valueTyped, calleeHeapTyped, calleeExtends⟩ := expression_value (expressionIH _ (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap calleeTyped child
          obtain ⟨valuesTyped, argumentsHeapTyped, argumentExtends⟩ := expressions_values (expressionsIH _ (Size.child_lt_stepSize (by simp)))
            runtime covers (locals.mono calleeExtends) calleeHeapTyped argumentsTyped children
          obtain ⟨packed, packing⟩ := ValuesPack.exists_pack values
          have packedTyped := packing.hasType valuesTyped
          cases application with
          | intro _count beforeEq _afterEq path =>
              rw [uncoerced] at path
              rw [← beforeEq] at packedTyped
              have argumentTyped := empty_path_type path ▸ packedTyped
              have post := appliesIH invocationSize (Size.child_lt_stepSize (by simp))
                runtime argumentsHeapTyped (valueTyped.mono argumentExtends) packing argumentTyped invocation
              exact ⟨post.value_typed _ rfl, post.heap_typed, calleeExtends.trans (argumentExtends.trans post.heap_extends)⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.SelectedExpressionPreservation
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

theorem expression_step (selectedBodies : SelectedBodies program registry) (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (expressionsIH : ∀ smaller, smaller < size → ExpressionsAt program registry smaller)
    (appliesIH : ∀ smaller, smaller < size → AppliesAt program registry smaller)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller)
    (rawIH : ∀ smaller, smaller < size → RawFormAt program registry smaller)
    (pathIH : ∀ smaller, smaller < size → CoercionPathAt program registry smaller) :
    ExpressionAt program registry size := by
  intro scope context environment before after id outcome type runtime covers locals heap typed trace
  cases outcome with
  | value value =>
      have post := expression_value_step selectedBodies size expressionIH expressionsIH appliesIH statementsIH
        rawIH pathIH runtime covers locals heap typed trace
      exact ⟨post.heap_typed, post.heap_extends, by intro actual equal; cases equal; exact post.value_typed⟩
  | fault failure =>
      have post := FaultPreservation.expression_fault_step selectedBodies size
        (fun n smaller => ExpressionAt.fault (expressionIH n smaller))
        (fun n smaller => ExpressionsAt.fault (expressionsIH n smaller))
        (fun n smaller => AppliesAt.fault (appliesIH n smaller))
        (fun n smaller => StatementsAt.fault (statementsIH n smaller))
        (fun n smaller => RawFormAt.fault (rawIH n smaller))
        (fun n smaller => CoercionPathAt.fault (pathIH n smaller))
        expressionIH expressionsIH rawIH runtime covers locals heap typed trace
      exact ⟨post.1, post.2, by intro value equal; cases equal⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.SelectedForItemsPreservation
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

theorem for_items_step (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (expressionsIH : ∀ smaller, smaller < size → ExpressionsAt program registry smaller)
    (itemsIH : ∀ smaller, smaller < size → ForItemsAt program registry smaller) :
    ForItemsAt program registry size := by
  intro scope context staticFinal runtimeFinal environment before after items outcome control
    runtime covers locals heap typed trace
  cases trace with
  | empty =>
      cases typed
      exact ⟨heap, .refl _, by intro environment equal; cases equal; exact ⟨rfl, locals⟩⟩
  | @absent nextSize scope context middleContext finalContext environment before bound after binder rest location outcome
      mono extended allocated next =>
      cases typed with
      | cons headTyped tailTyped =>
          cases headTyped with
          | letUninitialized _staticMono _generalizes staticExtended =>
              have same := Solcore.SourceSemantics.Dynamic.BinderExtends.functional extended staticExtended
              cases same
              have allocationExtends := HeapTypesExtend.of_allocation allocated
              have boundTyped := heap.allocate (.none _) allocated
              have boundLocals : EnvironmentAgrees bound middleContext.locals ((binder.id, location) :: environment) := by
                cases extended
                exact .cons allocated.reads_new rfl (.ordinary mono rfl) (locals.mono allocationExtends)
              have fields := RuntimeContextFields.ofBinderExtends extended
              have closed := fields.targetClosed runtime.closed
              have boundAtMiddle := boundTyped.transportClosed fields.signatures runtime.closed closed
                runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)
              have post := itemsIH nextSize (Size.child_lt_stepSize (by simp)) (runtime.transport fields)
                (fields.covers covers) boundLocals boundAtMiddle tailTyped next
              exact ⟨post.heap_typed.transportClosed fields.signatures.symm closed runtime.closed
                (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
                allocationExtends.trans post.heap_extends, post.done⟩
  | @initialized childSize nextSize scope context middleContext finalContext environment before middle bound after
      binder initializer rest value location outcome mono extended child allocated next =>
      cases typed with
      | cons headTyped tailTyped =>
          cases headTyped with
          | letInitialized initializerTyped _mono _generalizes staticExtended =>
              have same := Solcore.SourceSemantics.Dynamic.BinderExtends.functional extended staticExtended
              cases same
              have childPost := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap initializerTyped child
              have allocationExtends := HeapTypesExtend.of_allocation allocated
              have boundTyped := childPost.heap_typed.allocate (.some (childPost.value_typed _ rfl)) allocated
              have boundLocals : EnvironmentAgrees bound middleContext.locals ((binder.id, location) :: environment) := by
                cases extended
                exact .cons allocated.reads_new rfl (.ordinary mono rfl) (locals.mono (childPost.heap_extends.trans allocationExtends))
              have fields := RuntimeContextFields.ofBinderExtends extended
              have closed := fields.targetClosed runtime.closed
              have boundAtMiddle := boundTyped.transportClosed fields.signatures runtime.closed closed
                runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)
              have post := itemsIH nextSize (Size.child_lt_stepSize (by simp)) (runtime.transport fields)
                (fields.covers covers) boundLocals boundAtMiddle tailTyped next
              exact ⟨post.heap_typed.transportClosed fields.signatures.symm closed runtime.closed
                (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
                childPost.heap_extends.trans (allocationExtends.trans post.heap_extends), post.done⟩
          | letInitializedGeneralized poly _ _ _ _ => exact (poly mono).elim
  | @initializedGeneralized nextSize scope context middleContext finalContext environment before snapshotHeap bound
      after binder initializer rest captured function location outcome snapshot captures polymorphic extended
      allocated next =>
      cases typed with
      | cons headTyped tailTyped =>
          cases headTyped with
          | letInitialized _ monomorphic _ _ => exact (polymorphic monomorphic).elim
          | letInitializedGeneralized staticPolymorphic requirements generalizes initializerTyped staticExtended =>
              have same := Solcore.SourceSemantics.Dynamic.BinderExtends.functional extended staticExtended
              cases same
              have functionTyped := captures.wellTyped runtime (snapshot.agrees locals) staticPolymorphic requirements
                generalizes initializerTyped staticExtended
              have allocationExtends :=
                snapshot.metadata_extends.trans (HeapTypesExtend.of_generalized_allocation allocated)
              have boundTyped := (heap.copy snapshot).allocateGeneralized functionTyped allocated
              have boundLocals : EnvironmentAgrees bound middleContext.locals ((binder.id, location) :: environment) := by
                cases extended
                exact .cons allocated.reads_new
                  (congrArg (fun retained : TypedBinder => retained.scheme.body) captures.binder_eq)
                  (.generalized rfl (congrArg TypedBinder.id captures.binder_eq)
                    (congrArg TypedBinder.scheme captures.binder_eq))
                  (locals.mono allocationExtends)
              have fields := RuntimeContextFields.ofBinderExtends extended
              have closed := fields.targetClosed runtime.closed
              have boundAtMiddle := boundTyped.transportClosed fields.signatures runtime.closed closed
                runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)
              have post := itemsIH nextSize (Size.child_lt_stepSize (by simp)) (runtime.transport fields)
                (fields.covers covers) boundLocals boundAtMiddle tailTyped next
              exact ⟨post.heap_typed.transportClosed fields.signatures.symm closed runtime.closed
                (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
                allocationExtends.trans post.heap_extends, post.done⟩
  | @initializerFault childSize scope context environment before after binder initializer rest failure mono child =>
      cases typed with
      | cons headTyped _ =>
          cases headTyped with
          | letInitialized initializerTyped _ _ _ =>
              have post := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap initializerTyped child
              exact ⟨post.heap_typed, post.heap_extends, by intro environment equal; cases equal⟩
          | letInitializedGeneralized poly _ _ _ _ => exact (poly mono).elim
  | @expression childSize nextSize scope context finalContext environment before middle after expression rest value outcome child next =>
      cases typed with
      | cons headTyped tailTyped =>
          cases headTyped with
          | expression expressionTyped =>
              have first := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap expressionTyped child
              have post := itemsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
                (locals.mono first.heap_extends) first.heap_typed tailTyped next
              exact ⟨post.heap_typed, first.heap_extends.trans post.heap_extends, post.done⟩
  | @expressionFailure childSize scope context environment before after expression rest failure child =>
      cases typed with
      | cons headTyped _ =>
          cases headTyped with
          | expression expressionTyped =>
              have post := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap expressionTyped child
              exact ⟨post.heap_typed, post.heap_extends, by intro environment equal; cases equal⟩
  | @projectedBitNot keysSize nextSize scope context finalContext environment before targetHeap written after assignment values target updated rest outcome
      _projected keys snapshot write next =>
      cases typed with
      | cons headTyped tailTyped =>
          cases headTyped with
          | assignBitNot assignmentTyped =>
              cases assignmentTyped with
              | intro targetTyped _ =>
                  obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
                  have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                    runtime covers locals heap keyTyped keys
                  obtain ⟨root, savedTyped⟩ := projected_target_typed runtime.graph.nodeOccurrencesUnique
                    locals keyPost.heap_typed keyPost.heap_extends targetTyped keyTyped (keyPost.values_typed _ rfl) snapshot
                  obtain ⟨writtenTyped, writtenExtends⟩ := projected_write_bitNot savedTyped keyPost.heap_typed write
                  have totalExtends := keyPost.heap_extends.trans writtenExtends
                  have post := itemsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
                    (locals.mono totalExtends) writtenTyped tailTyped next
                  exact ⟨post.heap_typed, totalExtends.trans post.heap_extends, post.done⟩
  | projectedBitNotRootFault => exact ⟨heap, .refl _, by intro environment equal; cases equal⟩
  | @projectedBitNotKeysFault keysSize scope context environment before after assignment rest failure
      _projected _ready keys =>
      cases typed with
      | cons headTyped tailTyped =>
          cases headTyped with
          | assignBitNot assignmentTyped =>
              cases assignmentTyped with
              | intro targetTyped _ =>
                  obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
                  have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                    runtime covers locals heap keyTyped keys
                  exact ⟨keyPost.heap_typed, keyPost.heap_extends, by intro environment equal; cases equal⟩
  | @projectedBitNotGetterFault keysSize scope context environment before after assignment values rest reason
      _projected keys _failed =>
      cases typed with
      | cons headTyped tailTyped =>
          cases headTyped with
          | assignBitNot assignmentTyped =>
              cases assignmentTyped with
              | intro targetTyped _ =>
                  obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
                  have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                    runtime covers locals heap keyTyped keys
                  exact ⟨keyPost.heap_typed, keyPost.heap_extends, by intro environment equal; cases equal⟩
  | @projectedAssignment keysSize childSize nextSize scope context finalContext environment before targetHeap middle written after assignment operator rhs values target value updated rest outcome
      _projected keys snapshot child write next =>
      cases typed with
      | cons headTyped tailTyped =>
          cases headTyped with
          | assignValue assignmentTyped =>
              cases assignmentTyped with
              | equal targetTyped rhsTyped _ =>
                  obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
                  have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                    runtime covers locals heap keyTyped keys
                  obtain ⟨root, savedTyped⟩ := projected_target_typed runtime.graph.nodeOccurrencesUnique
                    locals keyPost.heap_typed keyPost.heap_extends targetTyped keyTyped (keyPost.values_typed _ rfl) snapshot
                  have first := expression_value (expressionIH childSize (Size.child_lt_stepSize (by simp)))
                    runtime covers (locals.mono keyPost.heap_extends) keyPost.heap_typed rhsTyped child
                  obtain ⟨writtenTyped, writtenExtends⟩ := projected_write_equal savedTyped first write
                  have totalExtends := keyPost.heap_extends.trans writtenExtends
                  have post := itemsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
                    (locals.mono totalExtends) writtenTyped tailTyped next
                  exact ⟨post.heap_typed, totalExtends.trans post.heap_extends, post.done⟩
              | wordCompound kind targetTyped rhsTyped _ =>
                  obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
                  have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                    runtime covers locals heap keyTyped keys
                  obtain ⟨root, savedTyped⟩ := projected_target_typed runtime.graph.nodeOccurrencesUnique
                    locals keyPost.heap_typed keyPost.heap_extends targetTyped keyTyped (keyPost.values_typed _ rfl) snapshot
                  have first := expression_value (expressionIH childSize (Size.child_lt_stepSize (by simp)))
                    runtime covers (locals.mono keyPost.heap_extends) keyPost.heap_typed rhsTyped child
                  obtain ⟨writtenTyped, writtenExtends⟩ := projected_write_compound kind savedTyped first write
                  have totalExtends := keyPost.heap_extends.trans writtenExtends
                  have post := itemsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
                    (locals.mono totalExtends) writtenTyped tailTyped next
                  exact ⟨post.heap_typed, totalExtends.trans post.heap_extends, post.done⟩
  | projectedAssignmentRootFault => exact ⟨heap, .refl _, by intro environment equal; cases equal⟩
  | @projectedAssignmentKeysFault keysSize scope context environment before after assignment operator rhs rest failure
      _projected _ready keys =>
      cases typed with
      | cons headTyped tailTyped =>
          cases headTyped with
          | assignValue assignmentTyped =>
              cases assignmentTyped with
              | equal targetTyped rhsTyped _ | wordCompound _ targetTyped rhsTyped _ =>
                  obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
                  have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                    runtime covers locals heap keyTyped keys
                  exact ⟨keyPost.heap_typed, keyPost.heap_extends, by intro environment equal; cases equal⟩
  | @projectedAssignmentGetterFault keysSize scope context environment before after assignment operator rhs values rest reason
      _projected keys _failed =>
      cases typed with
      | cons headTyped tailTyped =>
          cases headTyped with
          | assignValue assignmentTyped =>
              cases assignmentTyped with
              | equal targetTyped rhsTyped _ | wordCompound _ targetTyped rhsTyped _ =>
                  obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
                  have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                    runtime covers locals heap keyTyped keys
                  exact ⟨keyPost.heap_typed, keyPost.heap_extends, by intro environment equal; cases equal⟩
  | @projectedAssignmentRhsFault keysSize childSize scope context environment before targetHeap after assignment operator rhs values target rest failure
      _projected keys _snapshot child =>
      cases typed with
      | cons headTyped tailTyped =>
          cases headTyped with
          | assignValue assignmentTyped =>
              cases assignmentTyped with
              | equal targetTyped rhsTyped _ | wordCompound _ targetTyped rhsTyped _ =>
                  obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
                  have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                    runtime covers locals heap keyTyped keys
                  have post := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers
                    (locals.mono keyPost.heap_extends) keyPost.heap_typed rhsTyped child
                  exact ⟨post.heap_typed, keyPost.heap_extends.trans post.heap_extends, by intro environment equal; cases equal⟩
  | @projectedAssignmentWriteFault keysSize childSize scope context environment before targetHeap after assignment operator rhs values target right rest reason
      _projected keys _snapshot child _failed =>
      cases typed with
      | cons headTyped tailTyped =>
          cases headTyped with
          | assignValue assignmentTyped =>
              cases assignmentTyped with
              | equal targetTyped rhsTyped _ | wordCompound _ targetTyped rhsTyped _ =>
                  obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
                  have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                    runtime covers locals heap keyTyped keys
                  have post := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers
                    (locals.mono keyPost.heap_extends) keyPost.heap_typed rhsTyped child
                  exact ⟨post.heap_typed, keyPost.heap_extends.trans post.heap_extends, by intro environment equal; cases equal⟩
  | @assignment childSize nextSize scope context finalContext environment before middle written after
      assignment operator rhs value target updated rest outcome snapshot child write next =>
      cases typed with
      | cons headTyped tailTyped =>
          cases headTyped with
          | assignValue assignmentTyped =>
              cases assignmentTyped with
              | equal targetTyped rhsTyped _ =>
                  have first := expression_value (expressionIH childSize (Size.child_lt_stepSize (by simp))) runtime covers locals heap rhsTyped child
                  obtain ⟨writtenTyped, writtenExtends⟩ := bare_write locals heap targetTyped snapshot first write
                  have post := itemsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
                    (locals.mono writtenExtends) writtenTyped tailTyped next
                  exact ⟨post.heap_typed, writtenExtends.trans post.heap_extends, post.done⟩
              | wordCompound kind targetTyped rhsTyped _ =>
                  have first := expression_value (expressionIH childSize (Size.child_lt_stepSize (by simp))) runtime covers locals heap rhsTyped child
                  obtain ⟨writtenTyped, writtenExtends⟩ := bare_write_compound kind locals heap targetTyped snapshot first write
                  have post := itemsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
                    (locals.mono writtenExtends) writtenTyped tailTyped next
                  exact ⟨post.heap_typed, writtenExtends.trans post.heap_extends, post.done⟩
  | @assignmentFailure childSize scope context environment before after assignment operator rhs target rest failure snapshot child =>
      cases typed with
      | cons headTyped _ =>
          cases headTyped with
          | assignValue assignmentTyped =>
              cases assignmentTyped with
              | equal _targetTyped rhsTyped _ =>
                  have post := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap rhsTyped child
                  exact ⟨post.heap_typed, post.heap_extends, by intro environment equal; cases equal⟩
              | wordCompound _ _ rhsTyped _ =>
                  have post := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap rhsTyped child
                  exact ⟨post.heap_typed, post.heap_extends, by intro environment equal; cases equal⟩
  | @assignmentOperands childSize scope context environment before after assignment operator rhs target right
      currentCell initial currentSelected rest _snapshot child _currentRead _rootType _initialValue _pathRead _invalid =>
      cases typed with
      | cons headTyped _ =>
          cases headTyped with
          | assignValue assignmentTyped =>
              cases assignmentTyped with
              | equal _ rhsTyped _ | wordCompound _ _ rhsTyped _ =>
                  have post := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap rhsTyped child
                  exact ⟨post.heap_typed, post.heap_extends, by intro environment equal; cases equal⟩
  | bitNotFault => exact ⟨heap, .refl _, by intro environment equal; cases equal⟩
  | @bitNot nextSize scope context finalContext environment before written after assignment target updated rest outcome
      snapshot write next =>
      cases typed with
      | cons headTyped tailTyped =>
          cases headTyped with
          | assignBitNot assignmentTyped =>
              obtain ⟨writtenTyped, writtenExtends⟩ := bare_write_bitNot locals heap assignmentTyped snapshot write
              have post := itemsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
                (locals.mono writtenExtends) writtenTyped tailTyped next
              exact ⟨post.heap_typed, writtenExtends.trans post.heap_extends, post.done⟩
  | unbound | dangling => exact ⟨heap, .refl _, by intro environment equal; cases equal⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.SelectedLoopPreservation
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

theorem while_step (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller)
    (whileIH : ∀ smaller, smaller < size → WhileAt program registry smaller) :
    WhileAt program registry size := by
  intro scope context bodyFinal environment before after condition statements outcome control facts
    runtime covers locals heap conditionTyped bodyTyped trace
  cases trace with
  | @done testSize scope context environment before after condition statements test =>
      have post := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      exact ⟨post.heap_typed, post.heap_extends, by intro value equal; cases equal⟩
  | @conditionFault testSize scope context environment before after condition statements failure test =>
      have post := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      exact ⟨post.heap_typed, post.heap_extends, by intro value equal; cases equal⟩
  | @returned testSize bodySize scope context innerContext environment before middle after condition statements value test body =>
      have first := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      have post := statementsIH bodySize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed bodyTyped body
      exact ⟨post.heap_typed, first.heap_extends.trans post.heap_extends, post.returned (by simp)⟩
  | @breakFromBody testSize bodySize scope context innerContext environment before middle after condition statements innerEnvironment test body =>
      have first := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      have post := statementsIH bodySize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed bodyTyped body
      exact ⟨post.heap_typed, first.heap_extends.trans post.heap_extends, by intro value equal; cases equal⟩
  | @bodyFault testSize bodySize scope context innerContext environment before middle after condition statements failure test body =>
      have first := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      have post := statementsIH bodySize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed bodyTyped body
      exact ⟨post.heap_typed, first.heap_extends.trans post.heap_extends, post.returned (by simp)⟩
  | @next testSize bodySize nextSize scope context innerContext environment innerEnvironment before middle bodyHeap after condition statements outcome test body next =>
      have first := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      have middlePost := statementsIH bodySize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed bodyTyped body
      have post := whileIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono (first.heap_extends.trans middlePost.heap_extends)) middlePost.heap_typed conditionTyped bodyTyped next
      exact ⟨post.heap_typed, first.heap_extends.trans (middlePost.heap_extends.trans post.heap_extends), post.returned⟩

  | @continueNext testSize bodySize nextSize scope context innerContext environment innerEnvironment before middle bodyHeap after condition statements outcome test body next =>
      have first := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      have middlePost := statementsIH bodySize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed bodyTyped body
      have post := whileIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono (first.heap_extends.trans middlePost.heap_extends)) middlePost.heap_typed conditionTyped bodyTyped next
      exact ⟨post.heap_typed, first.heap_extends.trans (middlePost.heap_extends.trans post.heap_extends), post.returned⟩

theorem for_loop_step (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller)
    (itemsIH : ∀ smaller, smaller < size → ForItemsAt program registry smaller)
    (loopIH : ∀ smaller, smaller < size → ForLoopAt program registry smaller) :
    ForLoopAt program registry size := by
  intro scope context bodyFinal postFinal environment before after condition post body outcome control facts
    runtime covers locals heap conditionTyped bodyTyped postTyped trace
  cases trace with
  | @testFault testSize scope context environment before after condition post body failure test =>
      have result := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      exact ⟨result.heap_typed, result.heap_extends, by intro value equal; cases equal⟩
  | @finished testSize scope context environment before after condition post body test =>
      have result := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      exact ⟨result.heap_typed, result.heap_extends, by intro value equal; cases equal⟩
  | @bodyFailure testSize branchSize scope context innerContext environment before middle after condition post body failure test branch =>
      have first := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      have result := statementsIH branchSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed bodyTyped branch
      exact ⟨result.heap_typed, first.heap_extends.trans result.heap_extends, result.returned (by simp)⟩
  | @returnedFromBody testSize branchSize scope context innerContext environment before middle after condition post body value test branch =>
      have first := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      have result := statementsIH branchSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed bodyTyped branch
      exact ⟨result.heap_typed, first.heap_extends.trans result.heap_extends, result.returned (by simp)⟩
  | @forBreakFromBody testSize branchSize scope context innerContext environment before middle after condition post body innerEnvironment test branch =>
      have first := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      have result := statementsIH branchSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed bodyTyped branch
      exact ⟨result.heap_typed, first.heap_extends.trans result.heap_extends, by intro value equal; cases equal⟩
  | @postFailure testSize branchSize postTraceSize scope context innerContext postContext environment innerEnvironment
      before middle bodyHeap after condition post body failure test branch postTrace =>
      have first := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      have second := statementsIH branchSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed bodyTyped branch
      have result := itemsIH postTraceSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono (first.heap_extends.trans second.heap_extends)) second.heap_typed postTyped postTrace
      exact ⟨result.heap_typed, first.heap_extends.trans (second.heap_extends.trans result.heap_extends), by intro value equal; cases equal⟩
  | @continuePostFailure testSize branchSize postTraceSize scope context innerContext postContext environment innerEnvironment
      before middle bodyHeap after condition post body failure test branch postTrace =>
      have first := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      have second := statementsIH branchSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed bodyTyped branch
      have result := itemsIH postTraceSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono (first.heap_extends.trans second.heap_extends)) second.heap_typed postTyped postTrace
      exact ⟨result.heap_typed, first.heap_extends.trans (second.heap_extends.trans result.heap_extends), by intro value equal; cases equal⟩
  | @iterate testSize branchSize postTraceSize nextSize scope context innerContext postContext environment innerEnvironment postEnvironment
      before middle bodyHeap postHeap after condition post body outcome test branch postTrace next =>
      have first := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      have second := statementsIH branchSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed bodyTyped branch
      have third := itemsIH postTraceSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono (first.heap_extends.trans second.heap_extends)) second.heap_typed postTyped postTrace
      have result := loopIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono (first.heap_extends.trans (second.heap_extends.trans third.heap_extends)))
        third.heap_typed conditionTyped bodyTyped postTyped next
      exact ⟨result.heap_typed, first.heap_extends.trans (second.heap_extends.trans (third.heap_extends.trans result.heap_extends)), result.returned⟩

  | @continueIterate testSize branchSize postTraceSize nextSize scope context innerContext postContext environment innerEnvironment postEnvironment
      before middle bodyHeap postHeap after condition post body outcome test branch postTrace next =>
      have first := expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
      have second := statementsIH branchSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed bodyTyped branch
      have third := itemsIH postTraceSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono (first.heap_extends.trans second.heap_extends)) second.heap_typed postTyped postTrace
      have result := loopIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono (first.heap_extends.trans (second.heap_extends.trans third.heap_extends)))
        third.heap_typed conditionTyped bodyTyped postTyped next
      exact ⟨result.heap_typed, first.heap_extends.trans (second.heap_extends.trans (third.heap_extends.trans result.heap_extends)), result.returned⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.SelectedMatchControlPreservation
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

def MatchControlAt (program : Program) (registry : Registry) (size : Nat) : Prop :=
  ∀ {scope : Scope} {context : Context} {environment resultEnvironment : Dynamic.Environment}
    {before after : Heap} {resolution : MatchResolution} {outcome : BodyOutcome}
    {control : ControlContext} {facts : StatementFacts},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    StatementControlFormTyping scope.source control context (.matchWith resolution) facts →
    Size.Match program registry size scope context environment before resolution outcome after →
    outcome = .fallthrough resultEnvironment → facts.control.canFallthrough = true

theorem match_control_step (catalog : SignatureCatalogWellFormed program.signatures) (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller) :
    MatchControlAt program registry size := by
  intro scope context environment resultEnvironment before after resolution outcome control facts
    runtime covers locals heap controlTyped trace falls
  cases trace with
  | scrutineeFault | patternFault => cases falls
  | @arm childSize bodySize scope context armContext finalContext environment armEnvironment
      before middle hidden bound after resolution node value location statements bindings outcome
      contains scrutinee hiddenAllocated selected extended allocated body =>
      have common : ∃ scrutineeType caseFacts fallbackFacts summary,
          facts.control = summary.eraseValue ∧
          ExpressionHasType scope.source context resolution.scrutinee scrutineeType ∧
          MatchCasesHaveType scope.source control context scrutineeType resolution.cases caseFacts ∧
          mergeBodyControls caseFacts fallbackFacts = some summary := by
        cases controlTyped with
        | matchWithoutDefault _ scrutineeTyped casesTyped _ merged => exact ⟨_, _, none, _, rfl, scrutineeTyped, casesTyped, merged⟩
        | matchWithDefault _ scrutineeTyped casesTyped _ merged => exact ⟨_, _, some _, _, rfl, scrutineeTyped, casesTyped, merged⟩
      obtain ⟨scrutineeType, caseFacts, fallbackFacts, summary, summaryEq, scrutineeTyped, casesTyped, merged⟩ := common
      obtain ⟨valueTyped, middleTyped, firstExtends⟩ := expression_value (expressionIH _ (Size.child_lt_stepSize (by simp)))
        runtime covers locals heap scrutineeTyped scrutinee
      obtain ⟨typedNode, typedContains, sameType⟩ := scrutineeTyped.stored_type
      have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
        (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
      subst typedNode
      have hiddenTyped := middleTyped.allocate (.some (sameType ▸ valueTyped)) hiddenAllocated
      have hiddenExtends := HeapTypesExtend.of_allocation hiddenAllocated
      obtain ⟨staticBinders, staticArmContext, staticFinal, armFacts,
        bindingsTyped, bindersEq, staticExtended, armTyped, armMember, monomorphic⟩ :=
        selected.arm_preserves_typing casesTyped (valueTyped.mono hiddenExtends)
      have exactExtended : BindersExtend scope.source.owner context (bindings.map Prod.fst) staticArmContext :=
        bindersEq.symm ▸ staticExtended
      have sameContext := Solcore.SourceSemantics.Dynamic.BindersExtend.functional extended exactExtended
      subst staticArmContext
      have valuesTyped : ValuesHaveTypes context hidden (bindings.map Prod.snd)
          ((bindings.map Prod.fst).map fun binder => binder.scheme.body) := by
        simpa only [List.map_map, Function.comp_def] using bindingsTyped.unzip
      have boundTyped := allocated.preservesHeapTyping hiddenTyped valuesTyped
      have boundExtends := allocated.extendsHeapTypes
      have armLocals := allocated.preservesEnvironmentAgreement exactExtended
        (fun binder member => monomorphic binder (bindersEq ▸ member))
        (locals.mono (firstExtends.trans hiddenExtends))
      have fields := Solcore.SourceSemantics.Dynamic.BindersExtend.runtimeContextFields extended
      have armClosed := fields.targetClosed runtime.closed
      have boundAtArm := boundTyped.transportClosed fields.signatures runtime.closed armClosed
        runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)
      have bodyPost := statementsIH bodySize (Size.child_lt_stepSize (by simp))
        (runtime.transport fields) (fields.covers covers) armLocals boundAtArm armTyped body
      have armFalls : armFacts.control.canFallthrough = true := by
        cases outcome with
        | fallthrough env => exact (bodyPost.fallthrough env rfl).2.2
        | returned | breaking | continuing | fault => cases falls
      rw [summaryEq]
      exact ControlSummary.eraseValue_canFallthrough
        (MergeBodyControls.allows_of_mem (outcome := .fallthrough environment) merged armMember armFalls)
  | @default childSize bodySize scope context finalContext environment before middle hidden after
      resolution node value location statements outcome contains scrutinee hiddenAllocated selected body =>
      cases controlTyped with
      | matchWithoutDefault absent _ _ _ _ =>
          have present := selected.defaultBody_eq
          rw [absent] at present
          contradiction
      | matchWithDefault present scrutineeTyped casesTyped defaultTyped merged =>
          have exactBody := selected.defaultBody_eq
          have sameBody := Option.some.inj (present.symm.trans exactBody)
          subst statements
          obtain ⟨valueTyped, middleTyped, firstExtends⟩ := expression_value (expressionIH childSize (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap scrutineeTyped scrutinee
          obtain ⟨typedNode, typedContains, sameType⟩ := scrutineeTyped.stored_type
          have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
            (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
          subst typedNode
          have hiddenTyped := middleTyped.allocate (.some (sameType ▸ valueTyped)) hiddenAllocated
          have hiddenExtends := HeapTypesExtend.of_allocation hiddenAllocated
          have bodyPost := statementsIH bodySize (Size.child_lt_stepSize (by simp)) runtime covers
            (locals.mono (firstExtends.trans hiddenExtends)) hiddenTyped defaultTyped body
          have defaultFalls := by
            cases outcome with
            | fallthrough env => exact (bodyPost.fallthrough env rfl).2.2
            | returned | breaking | continuing | fault => cases falls
          exact ControlSummary.eraseValue_canFallthrough
            (MergeBodyControls.allows_of_fallback (outcome := .fallthrough environment) merged defaultFalls)
  | @noBranch childSize scope context environment before middle hidden resolution node value location contains scrutinee allocated selected =>
      cases controlTyped with
      | matchWithoutDefault absent scrutineeTyped casesTyped exhaustive _merged =>
          have typed := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap scrutineeTyped scrutinee
          rw [absent] at selected
          exact (selected.noBranch_impossible_of_exhaustive
            (by simpa [runtime.signatures] using catalog) casesTyped (typed.value_typed _ rfl) exhaustive).elim
      | matchWithDefault present _ _ _ _ =>
          have absent := selected.noBranch_defaultBody_eq
          rw [present] at absent
          contradiction

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.SelectedMatchPreservation
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

theorem match_step (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller) :
    MatchAt program registry size := by
  intro scope context environment before after resolution outcome control type caseFacts
    runtime covers locals heap scrutineeTyped casesTyped defaultTyped trace
  cases trace with
  | @scrutineeFault childSize scope context environment before after resolution actualFailure scrutinee =>
      have post := expressionIH childSize (Size.child_lt_stepSize (by simp))
        runtime covers locals heap scrutineeTyped scrutinee
      exact ⟨post.heap_typed, post.heap_extends, by intro value equal; cases equal⟩
  | @patternFault childSize scope context environment before middle hidden resolution node value location
      contains scrutinee allocated invalid =>
      obtain ⟨valueTyped, middleTyped, firstExtends⟩ := expression_value (expressionIH _ (Size.child_lt_stepSize (by simp)))
        runtime covers locals heap scrutineeTyped scrutinee
      obtain ⟨typedNode, typedContains, sameType⟩ := scrutineeTyped.stored_type
      have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
          (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
      subst typedNode
      exact ⟨middleTyped.allocate (.some (sameType ▸ valueTyped)) allocated,
        firstExtends.trans (HeapTypesExtend.of_allocation allocated), by intro result equal; cases equal⟩
  | @arm childSize bodySize scope context armContext finalContext environment armEnvironment
      before middle hidden bound after resolution node value location statements bindings outcome
      contains scrutinee hiddenAllocated selected extended allocated body =>
      obtain ⟨valueTyped, middleTyped, firstExtends⟩ := expression_value (expressionIH _ (Size.child_lt_stepSize (by simp)))
        runtime covers locals heap scrutineeTyped scrutinee
      obtain ⟨typedNode, typedContains, sameType⟩ := scrutineeTyped.stored_type
      have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
        (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
      subst typedNode
      have hiddenTyped := middleTyped.allocate (.some (sameType ▸ valueTyped)) hiddenAllocated
      have hiddenExtends := HeapTypesExtend.of_allocation hiddenAllocated
      obtain ⟨staticBinders, staticArmContext, staticFinal, armFacts,
        bindingsTyped, bindersEq, staticExtended, armTyped, monomorphic⟩ :=
        selected.armPreserves casesTyped (valueTyped.mono hiddenExtends)
      have exactExtended : BindersExtend scope.source.owner context (bindings.map Prod.fst) staticArmContext :=
        bindersEq.symm ▸ staticExtended
      have sameContext := Solcore.SourceSemantics.Dynamic.BindersExtend.functional extended exactExtended
      subst staticArmContext
      have valuesTyped : ValuesHaveTypes context hidden (bindings.map Prod.snd)
          ((bindings.map Prod.fst).map fun binder => binder.scheme.body) := by
        simpa only [List.map_map, Function.comp_def] using bindingsTyped.unzip
      have boundTyped := allocated.preservesHeapTyping hiddenTyped valuesTyped
      have boundExtends := allocated.extendsHeapTypes
      have armLocals := allocated.preservesEnvironmentAgreement exactExtended
        (fun binder member => monomorphic binder (bindersEq ▸ member))
        (locals.mono (firstExtends.trans hiddenExtends))
      have fields := Solcore.SourceSemantics.Dynamic.BindersExtend.runtimeContextFields extended
      have armClosed := fields.targetClosed runtime.closed
      have boundAtArm := boundTyped.transportClosed fields.signatures runtime.closed armClosed
        runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)
      have bodyPost := statementsIH bodySize (Size.child_lt_stepSize (by simp))
        (runtime.transport fields) (fields.covers covers) armLocals boundAtArm armTyped body
      exact ⟨bodyPost.heap_typed.transportClosed fields.signatures.symm armClosed runtime.closed
        (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
        firstExtends.trans (hiddenExtends.trans (boundExtends.trans bodyPost.heap_extends)), by
          intro result equal
          have returned : outcome = .returned result := by cases outcome <;> simp_all [BodyOutcome.restore]
          exact (bodyPost.returned (by simp) result returned).transportClosed fields.signatures.symm armClosed runtime.closed
            (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open⟩
  | @default childSize bodySize scope context finalContext environment before middle hidden after
      resolution node value location statements outcome contains scrutinee hiddenAllocated selected body =>
      obtain ⟨valueTyped, middleTyped, firstExtends⟩ := expression_value (expressionIH _ (Size.child_lt_stepSize (by simp)))
        runtime covers locals heap scrutineeTyped scrutinee
      obtain ⟨typedNode, typedContains, sameType⟩ := scrutineeTyped.stored_type
      have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
        (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
      subst typedNode
      have hiddenTyped := middleTyped.allocate (.some (sameType ▸ valueTyped)) hiddenAllocated
      have hiddenExtends := HeapTypesExtend.of_allocation hiddenAllocated
      obtain ⟨staticFinal, facts, bodyTyped⟩ := defaultTyped statements selected.defaultBody_eq
      have bodyPost := statementsIH bodySize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono (firstExtends.trans hiddenExtends)) hiddenTyped bodyTyped body
      exact ⟨bodyPost.heap_typed, firstExtends.trans (hiddenExtends.trans bodyPost.heap_extends), by
          intro result equal
          have returned : outcome = .returned result := by cases outcome <;> simp_all [BodyOutcome.restore]
          exact bodyPost.returned (by simp) result returned⟩
  | @noBranch childSize scope context environment before middle hidden resolution node value location contains scrutinee allocated _selected =>
      obtain ⟨valueTyped, middleTyped, firstExtends⟩ := expression_value (expressionIH childSize (Size.child_lt_stepSize (by simp)))
        runtime covers locals heap scrutineeTyped scrutinee
      obtain ⟨typedNode, typedContains, sameType⟩ := scrutineeTyped.stored_type
      have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
          (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
      subst typedNode
      exact ⟨middleTyped.allocate (.some (sameType ▸ valueTyped)) allocated,
        firstExtends.trans (HeapTypesExtend.of_allocation allocated), by intro result equal; cases equal⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.SelectedStatementsPreservation
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

theorem statements_step (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (expressionsIH : ∀ smaller, smaller < size → ExpressionsAt program registry smaller)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller)
    (whileIH : ∀ smaller, smaller < size → WhileAt program registry smaller)
    (matchIH : ∀ smaller, smaller < size → MatchAt program registry smaller)
    (matchControlIH : ∀ smaller, smaller < size → MatchControlAt program registry smaller)
    (itemsIH : ∀ smaller, smaller < size → ForItemsAt program registry smaller)
    (loopIH : ∀ smaller, smaller < size → ForLoopAt program registry smaller) :
    StatementsAt program registry size := by
  intro mode scope context staticFinal runtimeFinal environment before after statements outcome control facts
    runtime covers locals heap typed trace
  cases trace with
  | nil =>
      cases typed
      exact ⟨heap, .refl _, (by intro _ value equal; cases equal), by
        intro result equal; cases equal; exact ⟨rfl, locals, rfl⟩⟩
  | breaking _ _ | continuing _ _ =>
      exact ⟨heap, .refl _, (by intro _ value equal; cases equal),
        by intro result equal; cases equal⟩
  | returnUnit contains form =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped, _, _⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | returnUnit resultEq =>
          exact terminal_statements ⟨heap, .refl _, by intro value equal; cases equal; exact resultEq.symm ▸ .unit⟩
            (by intro env equal; cases equal)
  | @returnValue childSize mode scope context environment before after id rest node expression value contains form child =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped, _, _⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | returnValue expressionTyped =>
          have post := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap expressionTyped child
          exact terminal_statements ⟨post.heap_typed, post.heap_extends, by
            intro actual equal; cases equal; exact post.value_typed _ rfl⟩ (by intro env equal; cases equal)
  | @tail childSize scope context environment before after id node expression value contains form child =>
      cases typed with
      | singleton headTyped =>
          have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
          cases controlTyped with
          | expressionValue expressionTyped =>
              have post := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap expressionTyped child
              refine ⟨post.heap_typed, post.heap_extends, ?_, by intro env equal; cases equal⟩
              intro complete actual equal
              cases equal
              have resultEq := complete rfl
              simp [BodyCompletes, BodyFacts.singleton, ControlSummary.ordinary] at resultEq
              exact resultEq ▸ post.value_typed _ rfl
  | bitNotBareFault => exact fault_statements heap (.refl _)
  | @bitNotBare nextSize mode scope context finalContext environment before written after
      id rest node assignment target updated outcome contains form snapshot write next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignBitNot assignmentTyped =>
          obtain ⟨writtenTyped, writtenExtends⟩ := bare_write_bitNot locals heap assignmentTyped snapshot write
          have post := statementsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
            (locals.mono writtenExtends) writtenTyped tailTyped next
          have headFalls : headFacts.control.canFallthrough = true := by
            have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
            cases controlTyped
            rfl
          exact (continue_tail headFalls completeTail fallthroughWhole next post).prepend writtenExtends
  | @bitNotProjected keysSize nextSize mode scope context finalContext environment before targetHeap written after assignment values target updated id rest node outcome
      contains form _projected keys snapshot write next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignBitNot assignmentTyped =>
          cases assignmentTyped with
          | intro targetTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
              have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap keyTyped keys
              obtain ⟨root, savedTyped⟩ := projected_target_typed runtime.graph.nodeOccurrencesUnique
                locals keyPost.heap_typed keyPost.heap_extends targetTyped keyTyped (keyPost.values_typed _ rfl) snapshot
              obtain ⟨writtenTyped, writtenExtends⟩ := projected_write_bitNot savedTyped keyPost.heap_typed write
              have totalExtends := keyPost.heap_extends.trans writtenExtends
              have post := statementsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
                (locals.mono totalExtends) writtenTyped tailTyped next
              have headFalls : headFacts.control.canFallthrough = true := by
                have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
                cases controlTyped
                rfl
              exact (continue_tail headFalls completeTail fallthroughWhole next post).prepend totalExtends
  | bitNotProjectedRootFault => exact fault_statements heap (.refl _)
  | @bitNotProjectedKeysFault keysSize mode scope context environment before after assignment id rest node failure
      contains form _projected _ready keys =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignBitNot assignmentTyped =>
          cases assignmentTyped with
          | intro targetTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
              have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap keyTyped keys
              exact fault_statements keyPost.heap_typed keyPost.heap_extends
  | @bitNotProjectedGetterFault keysSize mode scope context environment before after assignment values id rest node reason
      contains form _projected keys _failed =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignBitNot assignmentTyped =>
          cases assignmentTyped with
          | intro targetTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
              have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap keyTyped keys
              exact fault_statements keyPost.heap_typed keyPost.heap_extends
  | @assignProjected keysSize childSize nextSize mode scope context finalContext environment before targetHeap middle written after assignment operator rhs values target value updated id rest node outcome
      contains form _projected keys snapshot child write next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal targetTyped rhsTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
              have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap keyTyped keys
              obtain ⟨root, savedTyped⟩ := projected_target_typed runtime.graph.nodeOccurrencesUnique
                locals keyPost.heap_typed keyPost.heap_extends targetTyped keyTyped (keyPost.values_typed _ rfl) snapshot
              have first := expression_value (expressionIH childSize (Size.child_lt_stepSize (by simp)))
                runtime covers (locals.mono keyPost.heap_extends) keyPost.heap_typed rhsTyped child
              obtain ⟨writtenTyped, writtenExtends⟩ := projected_write_equal savedTyped first write
              have totalExtends := keyPost.heap_extends.trans writtenExtends
              have post := statementsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
                (locals.mono totalExtends) writtenTyped tailTyped next
              have headFalls : headFacts.control.canFallthrough = true := by
                have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
                cases controlTyped
                rfl
              exact (continue_tail headFalls completeTail fallthroughWhole next post).prepend totalExtends
          | wordCompound kind targetTyped rhsTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
              have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap keyTyped keys
              obtain ⟨root, savedTyped⟩ := projected_target_typed runtime.graph.nodeOccurrencesUnique
                locals keyPost.heap_typed keyPost.heap_extends targetTyped keyTyped (keyPost.values_typed _ rfl) snapshot
              have first := expression_value (expressionIH childSize (Size.child_lt_stepSize (by simp)))
                runtime covers (locals.mono keyPost.heap_extends) keyPost.heap_typed rhsTyped child
              obtain ⟨writtenTyped, writtenExtends⟩ := projected_write_compound kind savedTyped first write
              have totalExtends := keyPost.heap_extends.trans writtenExtends
              have post := statementsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
                (locals.mono totalExtends) writtenTyped tailTyped next
              have headFalls : headFacts.control.canFallthrough = true := by
                have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
                cases controlTyped
                rfl
              exact (continue_tail headFalls completeTail fallthroughWhole next post).prepend totalExtends
  | assignProjectedRootFault => exact fault_statements heap (.refl _)
  | @assignProjectedKeysFault keysSize mode scope context environment before after assignment operator rhs id rest node failure
      contains form _projected _ready keys =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal targetTyped rhsTyped _ | wordCompound _ targetTyped rhsTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
              have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap keyTyped keys
              exact fault_statements keyPost.heap_typed keyPost.heap_extends
  | @assignProjectedGetterFault keysSize mode scope context environment before after assignment operator rhs values id rest node reason
      contains form _projected keys _failed =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal targetTyped rhsTyped _ | wordCompound _ targetTyped rhsTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
              have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap keyTyped keys
              exact fault_statements keyPost.heap_typed keyPost.heap_extends
  | @assignProjectedRhsFault keysSize childSize mode scope context environment before targetHeap after assignment operator rhs values target id rest node failure
      contains form _projected keys _snapshot child =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal targetTyped rhsTyped _ | wordCompound _ targetTyped rhsTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
              have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap keyTyped keys
              have post := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers
                (locals.mono keyPost.heap_extends) keyPost.heap_typed rhsTyped child
              exact fault_statements post.heap_typed (keyPost.heap_extends.trans post.heap_extends)
  | @assignProjectedWriteFault keysSize childSize mode scope context environment before targetHeap after assignment operator rhs values target right id rest node reason
      contains form _projected keys _snapshot child _failed =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal targetTyped rhsTyped _ | wordCompound _ targetTyped rhsTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
              have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap keyTyped keys
              have post := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers
                (locals.mono keyPost.heap_extends) keyPost.heap_typed rhsTyped child
              exact fault_statements post.heap_typed (keyPost.heap_extends.trans post.heap_extends)
  | assignBareUnbound | assignBareDangling => exact fault_statements heap (.refl _)
  | @assignBare childSize nextSize mode scope context finalContext environment before middle written after
      id rest node assignment operator rhs value target updated outcome contains form snapshot child write next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal targetTyped rhsTyped _ =>
              have first := expression_value (expressionIH childSize (Size.child_lt_stepSize (by simp))) runtime covers locals heap rhsTyped child
              obtain ⟨writtenTyped, writtenExtends⟩ := bare_write locals heap targetTyped snapshot first write
              have post := statementsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
                (locals.mono writtenExtends) writtenTyped tailTyped next
              have headFalls : headFacts.control.canFallthrough = true := by
                have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
                cases controlTyped
                rfl
              exact (continue_tail headFalls completeTail fallthroughWhole next post).prepend writtenExtends
          | wordCompound kind targetTyped rhsTyped _ =>
              have first := expression_value (expressionIH childSize (Size.child_lt_stepSize (by simp))) runtime covers locals heap rhsTyped child
              obtain ⟨writtenTyped, writtenExtends⟩ := bare_write_compound kind locals heap targetTyped snapshot first write
              have post := statementsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
                (locals.mono writtenExtends) writtenTyped tailTyped next
              have headFalls : headFacts.control.canFallthrough = true := by
                have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
                cases controlTyped
                rfl
              exact (continue_tail headFalls completeTail fallthroughWhole next post).prepend writtenExtends
  | @returnFault childSize mode scope context environment before after id rest node expression failure contains form child =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | returnValue expressionTyped =>
          have post := expressionIH childSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap expressionTyped child
          exact fault_statements post.heap_typed post.heap_extends
  | @expressionFault childSize mode scope context environment before after id rest node expression semicolon failure
      contains form child =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | expressionValue expressionTyped | expressionDiscard expressionTyped =>
          have post := expressionIH childSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap expressionTyped child
          exact fault_statements post.heap_typed post.heap_extends
  | @assignBareFault childSize mode scope context environment before after id rest node assignment operator rhs target failure
      contains form _snapshot child =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal _ rhsTyped _ =>
              have post := expressionIH childSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap rhsTyped child
              exact fault_statements post.heap_typed post.heap_extends
          | wordCompound _ _ rhsTyped _ =>
              have post := expressionIH childSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap rhsTyped child
              exact fault_statements post.heap_typed post.heap_extends
  | @assignBareOperands childSize mode scope context environment before after id rest node assignment operator rhs
      target right currentCell initial currentSelected contains form _snapshot child _currentRead _rootType _initialValue _pathRead _invalid =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped, _completeTail, _fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal _ rhsTyped _ | wordCompound _ _ rhsTyped _ =>
              have post := expressionIH childSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap rhsTyped child
              exact fault_statements post.heap_typed post.heap_extends
  | @letFault childSize mode scope context environment before after id rest node binder expression failure
      contains form monomorphic child =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | letInitialized expressionTyped _ _ =>
          have post := expressionIH childSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap expressionTyped child
          exact fault_statements post.heap_typed post.heap_extends
      | letInitializedGeneralized polymorphic _ _ _ _ => exact (polymorphic monomorphic).elim
  | @ifConditionFault testSize mode scope context environment before after id rest node condition thenBody elseBody failure
      contains form test =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | ifWithoutElse conditionTyped _ | ifWithElse conditionTyped _ _ =>
          have post := expressionIH testSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap conditionTyped test
          exact fault_statements post.heap_typed post.heap_extends
  | @forInitializerFault initialSize mode scope context failedContext environment before after id rest node initial condition post body
      failure contains form initialTrace =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, _tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | forLoop initialTyped _ _ _ =>
          have post := itemsIH initialSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap initialTyped initialTrace
          exact fault_statements post.heap_typed post.heap_extends
  | @discard childSize nextSize mode scope context finalContext environment before middle after id rest node expression
      value outcome contains form child next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | expressionDiscard expressionTyped =>
          obtain ⟨_valueTyped, middleTyped, headExtends⟩ := expression_value (expressionIH childSize (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap expressionTyped child
          have post := statementsIH nextSize (Size.child_lt_stepSize (by simp))
            runtime covers (locals.mono headExtends) middleTyped tailTyped next
          have headFalls : headFacts.control.canFallthrough = true := by
            have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
            cases controlTyped
            rfl
          exact (continue_tail headFalls completeTail fallthroughWhole next post).prepend headExtends
  | @discardValue childSize nextSize scope context finalContext environment before middle after id rest node expression
      value outcome contains form child next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | expressionValue expressionTyped =>
          obtain ⟨_valueTyped, middleTyped, headExtends⟩ := expression_value (expressionIH childSize (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap expressionTyped child
          have post := statementsIH nextSize (Size.child_lt_stepSize (by simp))
            runtime covers (locals.mono headExtends) middleTyped tailTyped next
          have headFalls : headFacts.control.canFallthrough = true := by
            have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
            cases controlTyped
            rfl
          exact (continue_tail headFalls completeTail fallthroughWhole next post).prepend headExtends
  | @letUninitialized nextSize mode scope context middleContext finalContext environment before bound after id rest node
      binder location outcome contains form monomorphic extension allocate next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | letUninitialized _ staticExtension =>
          have sameContext := Solcore.SourceSemantics.Dynamic.BinderExtends.functional extension staticExtension
          subst staticMiddle
          have allocationExtends := HeapTypesExtend.of_allocation allocate
          have boundTyped := heap.allocate (.none _) allocate
          have boundEnvironment : EnvironmentAgrees bound middleContext.locals ((binder.id, location) :: environment) := by
            cases extension
            exact .cons allocate.reads_new rfl (.ordinary monomorphic rfl) (locals.mono allocationExtends)
          have fields := RuntimeContextFields.ofBinderExtends extension
          have middleClosed := fields.targetClosed runtime.closed
          have boundAtMiddle := boundTyped.transportClosed fields.signatures runtime.closed middleClosed
            runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)
          have post := statementsIH nextSize (Size.child_lt_stepSize (by simp))
            (runtime.transport fields) (fields.covers covers) boundEnvironment boundAtMiddle tailTyped next
          have headFalls : headFacts.control.canFallthrough = true := by
            have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
            cases controlTyped
            rfl
          exact ((continue_tail headFalls completeTail fallthroughWhole next post).transportEntry runtime fields).prepend (allocationExtends)
  | @letGeneralized nextSize mode scope context middleContext finalContext environment before snapshotHeap bound
      after id rest node binder initializer captured function location outcome contains form snapshot captures
      polymorphic extension allocate next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | letInitialized _ monomorphic _ => exact (polymorphic monomorphic).elim
      | letInitializedGeneralized staticPolymorphic requirements generalizes initializerTyped staticExtension =>
          have sameContext := Solcore.SourceSemantics.Dynamic.BinderExtends.functional extension staticExtension
          subst staticMiddle
          have functionTyped := captures.wellTyped runtime (snapshot.agrees locals) staticPolymorphic requirements
            generalizes initializerTyped staticExtension
          have allocationExtends :=
            snapshot.metadata_extends.trans (HeapTypesExtend.of_generalized_allocation allocate)
          have boundTyped := (heap.copy snapshot).allocateGeneralized functionTyped allocate
          have boundEnvironment : EnvironmentAgrees bound middleContext.locals ((binder.id, location) :: environment) := by
            cases extension
            exact .cons allocate.reads_new
              (congrArg (fun retained : TypedBinder => retained.scheme.body) captures.binder_eq)
              (.generalized rfl (congrArg TypedBinder.id captures.binder_eq)
                (congrArg TypedBinder.scheme captures.binder_eq))
              (locals.mono allocationExtends)
          have fields := RuntimeContextFields.ofBinderExtends extension
          have middleClosed := fields.targetClosed runtime.closed
          have boundAtMiddle := boundTyped.transportClosed fields.signatures runtime.closed middleClosed
            runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)
          have post := statementsIH nextSize (Size.child_lt_stepSize (by simp))
            (runtime.transport fields) (fields.covers covers) boundEnvironment boundAtMiddle tailTyped next
          have headFalls : headFacts.control.canFallthrough = true := by
            have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
            cases controlTyped
            rfl
          exact ((continue_tail headFalls completeTail fallthroughWhole next post).transportEntry runtime fields).prepend allocationExtends
  | @letInitialized childSize nextSize mode scope context middleContext finalContext environment before middle bound after
      id rest node binder expression value location outcome contains form child monomorphic extension allocate next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | letInitialized expressionTyped _ staticExtension =>
          have sameContext := Solcore.SourceSemantics.Dynamic.BinderExtends.functional extension staticExtension
          subst staticMiddle
          obtain ⟨valueTyped, middleTyped, headExtends⟩ := expression_value (expressionIH childSize (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap expressionTyped child
          have allocationExtends := HeapTypesExtend.of_allocation allocate
          have boundTyped := middleTyped.allocate (.some valueTyped) allocate
          have boundEnvironment : EnvironmentAgrees bound middleContext.locals ((binder.id, location) :: environment) := by
            cases extension
            exact .cons allocate.reads_new rfl (.ordinary monomorphic rfl)
              ((locals.mono headExtends).mono allocationExtends)
          have fields := RuntimeContextFields.ofBinderExtends extension
          have middleClosed := fields.targetClosed runtime.closed
          have boundAtMiddle := boundTyped.transportClosed fields.signatures runtime.closed middleClosed
            runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)
          have post := statementsIH nextSize (Size.child_lt_stepSize (by simp))
            (runtime.transport fields) (fields.covers covers) boundEnvironment boundAtMiddle tailTyped next
          have headFalls : headFacts.control.canFallthrough = true := by
            have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
            cases controlTyped
            rfl
          exact ((continue_tail headFalls completeTail fallthroughWhole next post).transportEntry runtime fields).prepend (headExtends.trans allocationExtends)
      | letInitializedGeneralized polymorphic _ _ _ _ => exact (polymorphic monomorphic).elim
  | @ifReturned testSize branchSize mode scope context innerContext environment before middle after id rest node condition thenBody elseBody truth value contains form test branch =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      obtain ⟨first, firstFalls⟩ := if_branch expressionIH statementsIH
        (Size.child_lt_stepSize (by simp)) (Size.child_lt_stepSize (by simp)) runtime covers locals heap controlTyped test branch
      exact terminal_statements first (by intro env equal; cases equal)
  | @ifContinuing testSize branchSize mode scope context innerContext environment before middle after id rest node condition thenBody elseBody truth innerEnvironment contains form test branch =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      obtain ⟨first, firstFalls⟩ := if_branch expressionIH statementsIH
        (Size.child_lt_stepSize (by simp)) (Size.child_lt_stepSize (by simp)) runtime covers locals heap controlTyped test branch
      exact terminal_statements ⟨first.heap_typed, first.heap_extends, by intro value equal; cases equal⟩ (by intro env equal; cases equal)
  | @ifBreaking testSize branchSize mode scope context innerContext environment before middle after id rest node condition thenBody elseBody truth innerEnvironment contains form test branch =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      obtain ⟨first, firstFalls⟩ := if_branch expressionIH statementsIH
        (Size.child_lt_stepSize (by simp)) (Size.child_lt_stepSize (by simp)) runtime covers locals heap controlTyped test branch
      exact terminal_statements ⟨first.heap_typed, first.heap_extends, by intro value equal; cases equal⟩ (by intro env equal; cases equal)
  | @ifFault testSize branchSize mode scope context innerContext environment before middle after id rest node condition thenBody elseBody truth failure contains form test branch =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      obtain ⟨first, firstFalls⟩ := if_branch expressionIH statementsIH
        (Size.child_lt_stepSize (by simp)) (Size.child_lt_stepSize (by simp)) runtime covers locals heap controlTyped test branch
      exact fault_statements first.heap_typed first.heap_extends
  | @ifFallthrough testSize branchSize nextSize mode scope context innerContext finalContext environment innerEnvironment before middle branchHeap after id rest node condition thenBody elseBody truth outcome contains form test branch next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have execution : StatementExecutes program context scope.evidence scope.source environment before id
          context (.fallthrough environment) branchHeap :=
        StatementsPlain.if_execute contains form test.sound.value_plain branch.sound.fallthrough_scoped
      have sameContext := execution.final_context_of_typing runtime.graph headTyped
      subst staticMiddle
      have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      obtain ⟨first, firstFalls⟩ := if_branch expressionIH statementsIH
        (Size.child_lt_stepSize (by simp)) (Size.child_lt_stepSize (by simp)) runtime covers locals heap controlTyped test branch
      have post := statementsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed tailTyped next
      exact (continue_tail (firstFalls _ rfl) completeTail fallthroughWhole next post).prepend first.heap_extends
  | @blockReturned innerSize mode scope context innerContext environment before after id rest node statements value contains form inner =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases controlTyped with
      | block innerTyped =>
          have first := statementsIH innerSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap innerTyped inner
          exact terminal_statements ⟨first.heap_typed, first.heap_extends, first.returned (by simp)⟩ (by intro env equal; cases equal)
  | @blockContinuing innerSize mode scope context innerContext environment before after id rest node statements innerEnvironment contains form inner =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases controlTyped with
      | block innerTyped =>
          have first := statementsIH innerSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap innerTyped inner
          exact terminal_statements ⟨first.heap_typed, first.heap_extends, by intro value equal; cases equal⟩ (by intro env equal; cases equal)
  | @blockBreaking innerSize mode scope context innerContext environment before after id rest node statements innerEnvironment contains form inner =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases controlTyped with
      | block innerTyped =>
          have first := statementsIH innerSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap innerTyped inner
          exact terminal_statements ⟨first.heap_typed, first.heap_extends, by intro value equal; cases equal⟩ (by intro env equal; cases equal)
  | @blockFault innerSize mode scope context innerContext environment before after id rest node statements failure contains form inner =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases controlTyped with
      | block innerTyped =>
          have first := statementsIH innerSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap innerTyped inner
          exact fault_statements first.heap_typed first.heap_extends
  | @blockFallthrough innerSize nextSize mode scope context innerContext finalContext environment innerEnvironment before middle after id rest node statements outcome contains form inner next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have execution : StatementExecutes program context scope.evidence scope.source environment before id
          context (.fallthrough environment) middle := .block contains form inner.sound.fallthrough_scoped
      have sameContext := execution.final_context_of_typing runtime.graph headTyped
      subst staticMiddle
      have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases controlTyped with
      | block innerTyped =>
          have first := statementsIH innerSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap innerTyped inner
          have headFalls := ControlSummary.eraseValue_canFallthrough (first.fallthrough _ rfl).2.2
          have post := statementsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
            (locals.mono first.heap_extends) first.heap_typed tailTyped next
          exact (continue_tail headFalls completeTail fallthroughWhole next post).prepend first.heap_extends

  | @whileReturned loopSize mode scope context environment before after id rest node condition statements value contains form loop =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | whileLoop conditionTyped bodyTyped =>
          have first := whileIH loopSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped bodyTyped loop
          exact terminal_statements first (by intro env equal; cases equal)
  | @whileFault loopSize mode scope context environment before after id rest node condition statements failure contains form loop =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | whileLoop conditionTyped bodyTyped =>
          have first := whileIH loopSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped bodyTyped loop
          exact fault_statements first.heap_typed first.heap_extends
  | @whileFallthrough loopSize nextSize mode scope context finalContext environment before middle after id rest node condition statements outcome contains form loop next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | whileLoop conditionTyped bodyTyped =>
          have first := whileIH loopSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped bodyTyped loop
          have headFalls : headFacts.control.canFallthrough = true := by
            have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
            cases controlTyped
            rfl
          have post := statementsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
            (locals.mono first.heap_extends) first.heap_typed tailTyped next
          exact (continue_tail headFalls completeTail fallthroughWhole next post).prepend first.heap_extends
  | @matchReturned matchSize mode scope context environment before after id rest node resolution value contains form matched =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      have same : staticMiddle = context := by cases formTyped <;> rfl
      subst staticMiddle
      have common : ∃ type caseFacts,
          ExpressionHasType scope.source context resolution.scrutinee type ∧
          MatchCasesHaveType scope.source control context type resolution.cases caseFacts ∧
          (∀ statements, resolution.defaultBody = some statements →
            ∃ final facts, StatementsHaveType scope.source control context statements final facts) := by
        cases formTyped with
        | matchWithoutDefault absent scrutineeTyped casesTyped =>
          exact ⟨_, _, scrutineeTyped, casesTyped, fun statements found => by simp_all⟩
        | matchWithDefault present scrutineeTyped casesTyped defaultTyped =>
          exact ⟨_, _, scrutineeTyped, casesTyped, fun statements found => by
            cases Option.some.inj (present.symm.trans found)
            exact ⟨_, _, defaultTyped⟩⟩
      obtain ⟨type, caseFacts, scrutineeTyped, casesTyped, defaults⟩ := common
      have first := matchIH matchSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap scrutineeTyped casesTyped defaults matched
      exact terminal_statements first (by intro env equal; cases equal)
  | @matchContinuing matchSize mode scope context environment before after id rest node resolution contains form matched =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      have same : staticMiddle = context := by cases formTyped <;> rfl
      subst staticMiddle
      have common : ∃ type caseFacts,
          ExpressionHasType scope.source context resolution.scrutinee type ∧
          MatchCasesHaveType scope.source control context type resolution.cases caseFacts ∧
          (∀ statements, resolution.defaultBody = some statements →
            ∃ final facts, StatementsHaveType scope.source control context statements final facts) := by
        cases formTyped with
        | matchWithoutDefault absent scrutineeTyped casesTyped =>
          exact ⟨_, _, scrutineeTyped, casesTyped, fun statements found => by simp_all⟩
        | matchWithDefault present scrutineeTyped casesTyped defaultTyped =>
          exact ⟨_, _, scrutineeTyped, casesTyped, fun statements found => by
            cases Option.some.inj (present.symm.trans found)
            exact ⟨_, _, defaultTyped⟩⟩
      obtain ⟨type, caseFacts, scrutineeTyped, casesTyped, defaults⟩ := common
      have first := matchIH matchSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap scrutineeTyped casesTyped defaults matched
      exact terminal_statements first (by intro env equal; cases equal)
  | @matchBreaking matchSize mode scope context environment before after id rest node resolution contains form matched =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      have same : staticMiddle = context := by cases formTyped <;> rfl
      subst staticMiddle
      have common : ∃ type caseFacts,
          ExpressionHasType scope.source context resolution.scrutinee type ∧
          MatchCasesHaveType scope.source control context type resolution.cases caseFacts ∧
          (∀ statements, resolution.defaultBody = some statements →
            ∃ final facts, StatementsHaveType scope.source control context statements final facts) := by
        cases formTyped with
        | matchWithoutDefault absent scrutineeTyped casesTyped =>
          exact ⟨_, _, scrutineeTyped, casesTyped, fun statements found => by simp_all⟩
        | matchWithDefault present scrutineeTyped casesTyped defaultTyped =>
          exact ⟨_, _, scrutineeTyped, casesTyped, fun statements found => by
            cases Option.some.inj (present.symm.trans found)
            exact ⟨_, _, defaultTyped⟩⟩
      obtain ⟨type, caseFacts, scrutineeTyped, casesTyped, defaults⟩ := common
      have first := matchIH matchSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap scrutineeTyped casesTyped defaults matched
      exact terminal_statements first (by intro env equal; cases equal)
  | @matchFault matchSize mode scope context environment before after id rest node resolution failure contains form matched =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      have same : staticMiddle = context := by cases formTyped <;> rfl
      subst staticMiddle
      have common : ∃ type caseFacts,
          ExpressionHasType scope.source context resolution.scrutinee type ∧
          MatchCasesHaveType scope.source control context type resolution.cases caseFacts ∧
          (∀ statements, resolution.defaultBody = some statements →
            ∃ final facts, StatementsHaveType scope.source control context statements final facts) := by
        cases formTyped with
        | matchWithoutDefault absent scrutineeTyped casesTyped =>
          exact ⟨_, _, scrutineeTyped, casesTyped, fun statements found => by simp_all⟩
        | matchWithDefault present scrutineeTyped casesTyped defaultTyped =>
          exact ⟨_, _, scrutineeTyped, casesTyped, fun statements found => by
            cases Option.some.inj (present.symm.trans found)
            exact ⟨_, _, defaultTyped⟩⟩
      obtain ⟨type, caseFacts, scrutineeTyped, casesTyped, defaults⟩ := common
      have first := matchIH matchSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap scrutineeTyped casesTyped defaults matched
      exact fault_statements first.heap_typed first.heap_extends
  | @matchFallthrough matchSize nextSize mode scope context finalContext environment before middle after id rest node resolution outcome contains form matched next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      have same : staticMiddle = context := by cases formTyped <;> rfl
      subst staticMiddle
      have common : ∃ type caseFacts,
          ExpressionHasType scope.source context resolution.scrutinee type ∧
          MatchCasesHaveType scope.source control context type resolution.cases caseFacts ∧
          (∀ statements, resolution.defaultBody = some statements →
            ∃ final facts, StatementsHaveType scope.source control context statements final facts) := by
        cases formTyped with
        | matchWithoutDefault absent scrutineeTyped casesTyped =>
          exact ⟨_, _, scrutineeTyped, casesTyped, fun statements found => by simp_all⟩
        | matchWithDefault present scrutineeTyped casesTyped defaultTyped =>
          exact ⟨_, _, scrutineeTyped, casesTyped, fun statements found => by
            cases Option.some.inj (present.symm.trans found)
            exact ⟨_, _, defaultTyped⟩⟩
      obtain ⟨type, caseFacts, scrutineeTyped, casesTyped, defaults⟩ := common
      have first := matchIH matchSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap scrutineeTyped casesTyped defaults matched
      have headFalls := matchControlIH matchSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap
        (statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form) matched rfl
      have post := statementsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed tailTyped next
      exact (continue_tail headFalls completeTail fallthroughWhole next post).prepend first.heap_extends
  | @forReturned initialSize loopSize mode scope context loopContext environment loopEnvironment before initialized after id rest node initial condition post body value contains form initialTrace loop =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | forLoop initialTyped conditionTyped bodyTyped postTyped =>
          have initialPost := itemsIH initialSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap initialTyped initialTrace
          obtain ⟨same, initialLocals⟩ := initialPost.done _ rfl
          subst loopContext
          have fields := ForItemsHaveType.runtimeContextFields initialTyped
          have loopClosed := fields.targetClosed runtime.closed
          have initialAtLoop := initialPost.heap_typed.transportClosed fields.signatures runtime.closed loopClosed
            runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)
          have loopPost := loopIH loopSize (Size.child_lt_stepSize (by simp)) (runtime.transport fields)
            (fields.covers covers) initialLocals initialAtLoop conditionTyped bodyTyped postTyped loop
          have first : ControlPreserved context before _ control.returnType _ := ⟨
            loopPost.heap_typed.transportClosed fields.signatures.symm loopClosed runtime.closed
              (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
            initialPost.heap_extends.trans loopPost.heap_extends,
            fun value equal => (loopPost.returned value equal).transportClosed fields.signatures.symm loopClosed runtime.closed
              (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open⟩
          exact terminal_statements first (by intro env equal; cases equal)
  | @forFault initialSize loopSize mode scope context loopContext environment loopEnvironment before initialized after id rest node initial condition post body failure contains form initialTrace loop =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | forLoop initialTyped conditionTyped bodyTyped postTyped =>
          have initialPost := itemsIH initialSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap initialTyped initialTrace
          obtain ⟨same, initialLocals⟩ := initialPost.done _ rfl
          subst loopContext
          have fields := ForItemsHaveType.runtimeContextFields initialTyped
          have loopClosed := fields.targetClosed runtime.closed
          have initialAtLoop := initialPost.heap_typed.transportClosed fields.signatures runtime.closed loopClosed
            runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)
          have loopPost := loopIH loopSize (Size.child_lt_stepSize (by simp)) (runtime.transport fields)
            (fields.covers covers) initialLocals initialAtLoop conditionTyped bodyTyped postTyped loop
          have first : ControlPreserved context before _ control.returnType _ := ⟨
            loopPost.heap_typed.transportClosed fields.signatures.symm loopClosed runtime.closed
              (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
            initialPost.heap_extends.trans loopPost.heap_extends,
            fun value equal => (loopPost.returned value equal).transportClosed fields.signatures.symm loopClosed runtime.closed
              (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open⟩
          exact fault_statements first.heap_typed first.heap_extends
  | @forFallthrough initialSize loopSize nextSize mode scope context loopContext finalContext environment loopEnvironment before initialized middle after id rest node initial condition post body outcome contains form initialTrace loop next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | forLoop initialTyped conditionTyped bodyTyped postTyped =>
          have initialPost := itemsIH initialSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap initialTyped initialTrace
          obtain ⟨same, initialLocals⟩ := initialPost.done _ rfl
          subst loopContext
          have fields := ForItemsHaveType.runtimeContextFields initialTyped
          have loopClosed := fields.targetClosed runtime.closed
          have initialAtLoop := initialPost.heap_typed.transportClosed fields.signatures runtime.closed loopClosed
            runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)
          have loopPost := loopIH loopSize (Size.child_lt_stepSize (by simp)) (runtime.transport fields)
            (fields.covers covers) initialLocals initialAtLoop conditionTyped bodyTyped postTyped loop
          have first : ControlPreserved context before _ control.returnType _ := ⟨
            loopPost.heap_typed.transportClosed fields.signatures.symm loopClosed runtime.closed
              (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
            initialPost.heap_extends.trans loopPost.heap_extends,
            fun value equal => (loopPost.returned value equal).transportClosed fields.signatures.symm loopClosed runtime.closed
              (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open⟩
          have headFalls : headFacts.control.canFallthrough = true := by
            have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
            cases controlTyped
            rfl
          have post := statementsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
            (locals.mono first.heap_extends) first.heap_typed tailTyped next
          exact (continue_tail headFalls completeTail fallthroughWhole next post).prepend first.heap_extends

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
end
