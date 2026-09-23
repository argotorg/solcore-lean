import Solcore.Frontend.SourceStagedValue
import Solcore.SourceSemantics.Dynamic.Evidence
import Solcore.SourceSemantics.Dynamic.Evaluation
import Solcore.SourceSemantics.Dynamic.Primitive
import Solcore.SourceSemantics.Dynamic.Typing
import Solcore.SourceSemantics.Staging.Classification

/-!
Declarative materialization at the source staging boundary.

The semantic carrier in this module is deliberately independent of the
frontend's executable staged-value carrier.  Only Unit, Bool, Word, and
binary products can cross the boundary.  Integers, nominal values, mappings,
proxies, and functions may participate in source evaluation, but cannot be
materialized as residual runtime data.

Expression evaluation is an abstract relation parameter.  This keeps staging
independent of the concrete source evaluator while still stating the exact
classification, typing, heap, and dictionary obligations at the boundary.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Staging

open Frontend
open Frontend.SourceInference

/-- Closed semantic data which can be transferred from staged source
evaluation into residual runtime code. -/
inductive MaterializedValue where
  | unit
  | bool (value : Bool)
  | word (value : Core.Word)
  | product (left right : MaterializedValue)
  deriving Repr, BEq, DecidableEq

namespace MaterializedValue

/-- Exact source type carried by materialized data. -/
def sourceType : MaterializedValue → TypeSystem.Ty
  | .unit => .unit
  | .bool _ => .bool
  | .word _ => .word
  | .product left right => .product left.sourceType right.sourceType

end MaterializedValue

/-- Structural classification of dynamic values admitted at materialization.
This definition does not mention a conversion function or a frontend result. -/
inductive Materializable : Dynamic.Value → Prop where
  | unit : Materializable .unit
  | bool (value : Bool) : Materializable (.bool value)
  | word (value : Core.Word) : Materializable (.word value)
  | product
      {left right : Dynamic.Value}
      (left_materializable : Materializable left)
      (right_materializable : Materializable right) :
      Materializable (.product left right)

/-- Exact relational materialization of a dynamic source value. -/
inductive Materializes : Dynamic.Value → MaterializedValue → Prop where
  | unit : Materializes .unit .unit
  | bool (value : Bool) : Materializes (.bool value) (.bool value)
  | word (value : Core.Word) : Materializes (.word value) (.word value)
  | product
      {left right : Dynamic.Value}
      {materializedLeft materializedRight : MaterializedValue}
      (left_materializes : Materializes left materializedLeft)
      (right_materializes : Materializes right materializedRight) :
      Materializes (.product left right)
        (.product materializedLeft materializedRight)

namespace Materializes

/-- Materialization implies the independent admissibility classification. -/
theorem materializable
    {value : Dynamic.Value} {materialized : MaterializedValue}
    (relation : Materializes value materialized) : Materializable value := by
  induction relation with
  | unit => exact .unit
  | bool value => exact .bool value
  | word value => exact .word value
  | product _ _ left_ih right_ih => exact .product left_ih right_ih

/-- A fixed dynamic value has one materialized representation. -/
theorem functional
    {value : Dynamic.Value} {left right : MaterializedValue}
    (left_relation : Materializes value left)
    (right_relation : Materializes value right) : left = right := by
  induction left_relation generalizing right with
  | unit => cases right_relation; rfl
  | bool value => cases right_relation; rfl
  | word value => cases right_relation; rfl
  | product _ _ left_ih right_ih =>
      cases right_relation with
      | product otherLeft otherRight =>
          rw [left_ih otherLeft, right_ih otherRight]

/-- Every materialization has its exact structural source type in every
semantic context and heap. -/
theorem hasType
    {context : Context} {heap : Dynamic.Heap}
    {value : Dynamic.Value} {materialized : MaterializedValue}
    (relation : Materializes value materialized) :
    Dynamic.ValueHasType context heap value materialized.sourceType := by
  induction relation with
  | unit => exact .unit
  | bool value => exact .bool value
  | word value => exact .word value
  | product _ _ left_ih right_ih => exact .product left_ih right_ih

end Materializes

namespace Materializable

/-- Every admitted dynamic value has a materialized representation. -/
theorem exists_materialized
    {value : Dynamic.Value} (admitted : Materializable value) :
    ∃ materialized, Materializes value materialized := by
  induction admitted with
  | unit => exact ⟨.unit, .unit⟩
  | bool value => exact ⟨.bool value, .bool value⟩
  | word value => exact ⟨.word value, .word value⟩
  | product _ _ left_ih right_ih =>
      rcases left_ih with ⟨left, leftRelation⟩
      rcases right_ih with ⟨right, rightRelation⟩
      exact ⟨.product left right, .product leftRelation rightRelation⟩

end Materializable

/-- Relational and classificatory accounts of admissibility coincide. -/
theorem materializes_exists_iff (value : Dynamic.Value) :
    (∃ materialized, Materializes value materialized) ↔ Materializable value := by
  constructor
  · rintro ⟨materialized, relation⟩
    exact relation.materializable
  · exact Materializable.exists_materialized

/-- Structural correspondence with the executable frontend carrier.  This is
separate from `Materializes`: the normative boundary does not depend on a
frontend conversion succeeding. -/
inductive FrontendValueRepresents :
    MaterializedValue → Frontend.SourceStagedValue.Value → Prop where
  | unit : FrontendValueRepresents .unit .unit
  | bool (value : Bool) : FrontendValueRepresents (.bool value) (.bool value)
  | word (value : Core.Word) : FrontendValueRepresents (.word value) (.word value)
  | product
      {left right : MaterializedValue}
      {frontendLeft frontendRight : Frontend.SourceStagedValue.Value}
      (left_represents : FrontendValueRepresents left frontendLeft)
      (right_represents : FrontendValueRepresents right frontendRight) :
      FrontendValueRepresents (.product left right)
        (.product frontendLeft frontendRight)

namespace FrontendValueRepresents

/-- Every semantic materialized value has a frontend representation. -/
theorem exists_frontend (value : MaterializedValue) :
    ∃ frontend, FrontendValueRepresents value frontend := by
  induction value with
  | unit => exact ⟨.unit, .unit⟩
  | bool value => exact ⟨.bool value, .bool value⟩
  | word value => exact ⟨.word value, .word value⟩
  | product left right left_ih right_ih =>
      rcases left_ih with ⟨frontendLeft, leftRelation⟩
      rcases right_ih with ⟨frontendRight, rightRelation⟩
      exact ⟨.product frontendLeft frontendRight,
        .product leftRelation rightRelation⟩

/-- A semantic materialized value has one frontend representation. -/
theorem functional
    {value : MaterializedValue}
    {left right : Frontend.SourceStagedValue.Value}
    (left_relation : FrontendValueRepresents value left)
    (right_relation : FrontendValueRepresents value right) : left = right := by
  induction left_relation generalizing right with
  | unit => cases right_relation; rfl
  | bool value => cases right_relation; rfl
  | word value => cases right_relation; rfl
  | product _ _ left_ih right_ih =>
      cases right_relation with
      | product otherLeft otherRight =>
          rw [left_ih otherLeft, right_ih otherRight]

/-- The independent correspondence preserves exact source types. -/
theorem sourceType_eq
    {value : MaterializedValue}
    {frontend : Frontend.SourceStagedValue.Value}
    (relation : FrontendValueRepresents value frontend) :
    Frontend.SourceStagedValue.sourceType frontend = value.sourceType := by
  induction relation with
  | unit | bool | word => rfl
  | product _ _ left_ih right_ih =>
      simp only [Frontend.SourceStagedValue.sourceType,
        MaterializedValue.sourceType, left_ih, right_ih]

end FrontendValueRepresents

/-- Materialization always has a unique corresponding frontend carrier. -/
theorem Materializes.frontend_exists_unique
    {value : Dynamic.Value} {materialized : MaterializedValue}
    (_relation : Materializes value materialized) :
    ∃ frontend,
      FrontendValueRepresents materialized frontend ∧
      ∀ other, FrontendValueRepresents materialized other → other = frontend := by
  rcases FrontendValueRepresents.exists_frontend materialized with
    ⟨frontend, representation⟩
  exact ⟨frontend, representation, fun other otherRepresentation =>
    FrontendValueRepresents.functional otherRepresentation representation⟩

/-- Ambient source expression evaluation, with its program and dictionary
inputs already fixed by the caller. -/
abbrev ExpressionEvaluationRelation :=
  Dynamic.Environment → Dynamic.Heap → ExpressionId →
    Dynamic.Value → Dynamic.Heap → Prop

/-- Closed dictionary inputs are proof evidence, not ordinary dynamic values.
They cross their own boundary and are therefore intentionally absent from
`Materializes`. -/
structure DictionaryInputsValid
    (context : Context) (inputs : Dynamic.EvidenceEnvironment) : Prop where
  covers : inputs.Covers context

/-- Every local classified compile time has an initialized, typed, and
materializable dynamic cell.  Runtime and deferred locals impose no
materialization obligation here. -/
def ComptimeLocalsAvailable
    (context : Context) (scope : StageScope)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) : Prop :=
  ∀ id, scope.Lookup id .comptime →
    ∃ scheme location cell value materialized,
      context.LocalLookup id scheme ∧
      Dynamic.Environment.LooksUp environment id location ∧
      Dynamic.Heap.Reads heap location cell ∧
      cell.type = scheme.body ∧
      cell.value = some value ∧
      Dynamic.ValueHasType context heap value scheme.body ∧
      Materializes value materialized

/-- Complete state admitted at one compile-time evaluation boundary. -/
structure ComptimeEvaluationBoundary
    (context : Context) (scope : StageScope)
    (dictionaryInputs : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) : Prop where
  heap_typed : Dynamic.HeapWellTyped context heap
  environment_agrees :
    Dynamic.EnvironmentAgrees heap context.locals environment
  comptime_locals :
    ComptimeLocalsAvailable context scope environment heap
  dictionaries : DictionaryInputsValid context dictionaryInputs

/-- Pointwise admission of evaluated direct-call arguments at a staged
parameter boundary.  A parameter may be forced compile time by the enclosing
function policy even when it has no explicit marker, so the exact classified
argument stages are retained as a separate index. -/
inductive ComptimeParameterInputs (context : Context) (heap : Dynamic.Heap) :
    List TypedBinder → List Stage → List Dynamic.Value →
      List MaterializedValue → Prop where
  | nil : ComptimeParameterInputs context heap [] [] [] []
  | cons
      {binder : TypedBinder} {binders : List TypedBinder}
      {stage : Stage} {stages : List Stage}
      {value : Dynamic.Value} {values : List Dynamic.Value}
      {materialized : MaterializedValue}
      {materializedValues : List MaterializedValue}
      (comptime : stage = .comptime)
      (typed : Dynamic.ValueHasType context heap value binder.scheme.body)
      (materializes : Materializes value materialized)
      (tail : ComptimeParameterInputs context heap binders stages values
        materializedValues) :
      ComptimeParameterInputs context heap (binder :: binders)
        (stage :: stages) (value :: values)
        (materialized :: materializedValues)

namespace ComptimeParameterInputs

/-- Every argument admitted at this boundary was classified compile time. -/
theorem allComptime
    {context : Context} {heap : Dynamic.Heap}
    {binders : List TypedBinder} {stages : List Stage}
    {values : List Dynamic.Value}
    {materializedValues : List MaterializedValue}
    (inputs : ComptimeParameterInputs context heap binders stages values
      materializedValues) : AllComptime stages := by
  intro stage member
  induction inputs with
  | nil => simp at member
  | cons comptime _ _ _ ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact comptime
      · exact ih member

/-- Parameter, stage, dynamic-value, and materialized-value vectors have the
same exact arity. -/
theorem lengths
    {context : Context} {heap : Dynamic.Heap}
    {binders : List TypedBinder} {stages : List Stage}
    {values : List Dynamic.Value}
    {materializedValues : List MaterializedValue}
    (inputs : ComptimeParameterInputs context heap binders stages values
      materializedValues) :
    binders.length = stages.length ∧
      stages.length = values.length ∧
      values.length = materializedValues.length := by
  induction inputs with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons _ _ _ _ induction =>
      rcases induction with ⟨first, second, third⟩
      simp only [List.length_cons, Nat.succ.injEq]
      exact ⟨first, second, third⟩

end ComptimeParameterInputs

/-- Direct staged invocation keeps value inputs and dictionary inputs visibly
separate.  Only parameter values materialize; dictionaries remain closed
semantic evidence. -/
structure ComptimeInvocationBoundary
    (context : Context) (heap : Dynamic.Heap)
    (parameters : List TypedBinder) (argumentStages : List Stage)
    (arguments : List Dynamic.Value)
    (materializedArguments : List MaterializedValue)
    (dictionaryInputs : Dynamic.EvidenceEnvironment) : Prop where
  parameters_valid : ComptimeParameterInputs context heap parameters
    argumentStages arguments materializedArguments
  dictionaries_valid : DictionaryInputsValid context dictionaryInputs

/-- Declarative staged evaluation and materialization of one classified source
expression.  The conditional rules evaluate the condition and exactly the
selected branch.  The other branch still carries compile-time classification
and static typing premises, but deliberately has no evaluation premise. -/
inductive ComptimeExpressionMaterializes
    (EvaluateExpression : ExpressionEvaluationRelation)
    (ExecuteCoercions : Dynamic.Heap → List CoercionStep → Dynamic.Value →
      Dynamic.Value → Dynamic.Heap → Prop)
    (source : TypedSource) (context : Context) (scope : StageScope)
    (dictionaryInputs : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) :
    Dynamic.Heap → ExpressionId → MaterializedValue → Dynamic.Heap → Prop where
  | ordinary
      {before after : Dynamic.Heap} {id : ExpressionId}
      {node : ExpressionNode} {value : Dynamic.Value}
      {materialized : MaterializedValue}
      (contains : ContainsExpression source id node)
      (not_conditional : ∀ condition thenBranch elseBranch,
        node.form ≠ .conditional condition thenBranch elseBranch)
      (classified : HasStage source scope id .comptime)
      (typed : ExpressionHasType source context id node.type)
      (boundary : ComptimeEvaluationBoundary context scope dictionaryInputs
        environment before)
      (evaluates : EvaluateExpression environment before id value after)
      (materializes : Materializes value materialized) :
      ComptimeExpressionMaterializes EvaluateExpression ExecuteCoercions source context scope
        dictionaryInputs environment before id materialized after
  | conditionalTrue
      {before conditionHeap branchHeap after : Dynamic.Heap}
      {id condition thenBranch elseBranch : ExpressionId}
      {node : ExpressionNode} {branchValue finalValue : Dynamic.Value}
      {materialized : MaterializedValue}
      (contains : ContainsExpression source id node)
      (form_eq : node.form =
        .conditional condition thenBranch elseBranch)
      (whole_classified : HasStage source scope id .comptime)
      (condition_classified : HasStage source scope condition .comptime)
      (then_classified : HasStage source scope thenBranch .comptime)
      (else_classified : HasStage source scope elseBranch .comptime)
      (whole_typed : ExpressionHasType source context id node.type)
      (condition_typed : ExpressionHasType source context condition .bool)
      (then_typed : ExpressionHasType source context thenBranch node.rawType)
      (else_typed : ExpressionHasType source context elseBranch node.rawType)
      (boundary : ComptimeEvaluationBoundary context scope dictionaryInputs
        environment before)
      (condition_evaluates : EvaluateExpression environment before condition
        (.bool true) conditionHeap)
      (then_evaluates : EvaluateExpression environment conditionHeap thenBranch
        branchValue branchHeap)
      (coercions_apply : ExecuteCoercions branchHeap node.coercions
        branchValue finalValue after)
      (materializes : Materializes finalValue materialized) :
      ComptimeExpressionMaterializes EvaluateExpression ExecuteCoercions source context scope
        dictionaryInputs environment before id materialized after
  | conditionalFalse
      {before conditionHeap branchHeap after : Dynamic.Heap}
      {id condition thenBranch elseBranch : ExpressionId}
      {node : ExpressionNode} {branchValue finalValue : Dynamic.Value}
      {materialized : MaterializedValue}
      (contains : ContainsExpression source id node)
      (form_eq : node.form =
        .conditional condition thenBranch elseBranch)
      (whole_classified : HasStage source scope id .comptime)
      (condition_classified : HasStage source scope condition .comptime)
      (then_classified : HasStage source scope thenBranch .comptime)
      (else_classified : HasStage source scope elseBranch .comptime)
      (whole_typed : ExpressionHasType source context id node.type)
      (condition_typed : ExpressionHasType source context condition .bool)
      (then_typed : ExpressionHasType source context thenBranch node.rawType)
      (else_typed : ExpressionHasType source context elseBranch node.rawType)
      (boundary : ComptimeEvaluationBoundary context scope dictionaryInputs
        environment before)
      (condition_evaluates : EvaluateExpression environment before condition
        (.bool false) conditionHeap)
      (else_evaluates : EvaluateExpression environment conditionHeap elseBranch
        branchValue branchHeap)
      (coercions_apply : ExecuteCoercions branchHeap node.coercions
        branchValue finalValue after)
      (materializes : Materializes finalValue materialized) :
      ComptimeExpressionMaterializes EvaluateExpression ExecuteCoercions source context scope
        dictionaryInputs environment before id materialized after

/-- The normative source staging boundary obtained by instantiating the
generic selected-branch interface with the declarative source evaluator and
effectful coercion semantics. -/
def SourceComptimeExpressionMaterializes
    (program : Program) (source : TypedSource) (context : Context)
    (scope : StageScope) (dictionaryInputs : Dynamic.EvidenceEnvironment)
    (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (id : ExpressionId) (materialized : MaterializedValue)
    (after : Dynamic.Heap) : Prop :=
  ComptimeExpressionMaterializes
    (Dynamic.ExpressionEvaluates program context dictionaryInputs source)
    (Dynamic.CoercionPathExecutes program context dictionaryInputs)
    source context scope dictionaryInputs environment before id materialized after

namespace ComptimeExpressionMaterializes

/-- Every successful staged boundary result belongs to the closed
materialization fragment. -/
theorem result_materializable
    {EvaluateExpression : ExpressionEvaluationRelation}
    {ExecuteCoercions : Dynamic.Heap → List CoercionStep → Dynamic.Value →
      Dynamic.Value → Dynamic.Heap → Prop}
    {source : TypedSource} {context : Context} {scope : StageScope}
    {dictionaryInputs : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId}
    {materialized : MaterializedValue}
    (evaluation : ComptimeExpressionMaterializes EvaluateExpression ExecuteCoercions source
      context scope dictionaryInputs environment before id materialized after) :
    ∃ value, Materializes value materialized := by
  cases evaluation with
  | ordinary _ _ _ _ _ _ materializes => exact ⟨_, materializes⟩
  | conditionalTrue _ _ _ _ _ _ _ _ _ _ _ _ _ coercions materializes =>
      exact ⟨_, materializes⟩
  | conditionalFalse _ _ _ _ _ _ _ _ _ _ _ _ _ coercions materializes =>
      exact ⟨_, materializes⟩

/-- A staged result always has a unique corresponding frontend carrier. -/
theorem frontend_exists_unique
    {EvaluateExpression : ExpressionEvaluationRelation}
    {ExecuteCoercions : Dynamic.Heap → List CoercionStep → Dynamic.Value →
      Dynamic.Value → Dynamic.Heap → Prop}
    {source : TypedSource} {context : Context} {scope : StageScope}
    {dictionaryInputs : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId}
    {materialized : MaterializedValue}
    (evaluation : ComptimeExpressionMaterializes EvaluateExpression ExecuteCoercions source
      context scope dictionaryInputs environment before id materialized after) :
    ∃ frontend,
      FrontendValueRepresents materialized frontend ∧
      ∀ other, FrontendValueRepresents materialized other → other = frontend := by
  rcases evaluation.result_materializable with ⟨value, relation⟩
  exact relation.frontend_exists_unique

end ComptimeExpressionMaterializes

end Solcore.SourceSemantics.Staging
