import Solcore.Frontend.SourceStageAnalysis
import Solcore.SourceSemantics.Dynamic.Typing
import Solcore.Core.Correspondence
import Solcore.Core.Internal.Renaming
import Solcore.SourceSemantics.Dynamic
import Solcore.Frontend.SourceCoreElaboration
import Solcore.SourceSemantics.Dynamic.Evaluation
import Solcore.Core.Primitive
import Solcore.Core.Eval
import Solcore.SourceSemantics.Dynamic.Primitive
import Solcore.SourceSemantics.Graph
import Solcore.TypeSystem.Internal.SchemeLaws

/-!
# Literals and staged values

Literal meaning, integer primitives, staged values, read-only renaming, scalar statement views, and the empty source substitution.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.StagedValue
/-!
Independent source meaning and execution of reified staged values.

This is the value-embedding part of source-to-Core correctness. It connects
the existing `SourceStagedValue.toCoreExpr` implementation to mathematical
source values and to Core's declarative and executable semantics. It does not
assume or establish correctness of the staged evaluator that produced a value.
No typed-source runtime is imported or used as the source specification.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering

open Frontend

namespace StagedValue

/-- Interpret the closed staging carrier as an independent source value. -/
def toSource : SourceStagedValue.Value → Dynamic.Value
  | .unit => .unit
  | .bool value => .bool value
  | .word value => .word value
  | .product left right => .product (toSource left) (toSource right)

/-- Scalar/product representation, independent of any staging computation. -/
inductive Represents : Dynamic.Value → Core.Value → Prop where
  | unit : Represents .unit .unit
  | bool (value : Bool) : Represents (.bool value) (.bool value)
  | word (value : Core.Word) : Represents (.word value) (.word value)
  | product {left right : Dynamic.Value} {coreLeft coreRight : Core.Value}
      (left_related : Represents left coreLeft)
      (right_related : Represents right coreRight) :
      Represents (.product left right) (.pair coreLeft coreRight)

theorem toCore_represents (value : SourceStagedValue.Value) :
    Represents (toSource value) (SourceStagedValue.toCore value) := by
  induction value with
  | unit => exact .unit
  | bool value => exact .bool value
  | word value => exact .word value
  | product _ _ left right => exact .product left right

/-- Reification does not require inspecting the source heap or its values. -/
theorem toSource_hasType (value : SourceStagedValue.Value)
    (context : Context) (heap : Dynamic.Heap) :
    Dynamic.ValueHasType context heap (toSource value)
      (SourceStagedValue.sourceType value) := by
  induction value with
  | unit => exact .unit
  | bool value => exact .bool value
  | word value => exact .word value
  | product _ _ left right => exact .product left right

/-- Reified constants are typed in any lexical and nominal context. -/
theorem toCoreExpr_hasType (value : SourceStagedValue.Value)
    (context : Core.Context) (definitions : Core.DataEnvironment) :
    Core.HasType context (SourceStagedValue.toCoreExpr value)
      (SourceStagedValue.coreType value) definitions := by
  induction value with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | product _ _ left right => exact .pair left right

/-- The executable Core checker accepts the actual reification output. -/
theorem toCoreExpr_infers (value : SourceStagedValue.Value)
    (context : Core.Context) (definitions : Core.DataEnvironment) :
    Core.infer? context (SourceStagedValue.toCoreExpr value) definitions =
      some (SourceStagedValue.coreType value) :=
  Core.infer_complete (toCoreExpr_hasType value context definitions)

/-- Every related scalar/product value comes from the existing staging
carrier. This rules out an unconstrained representation relation. -/
theorem Represents.exists_staged
    {source : Dynamic.Value} {core : Core.Value}
    (related : Represents source core) :
    ∃ value : SourceStagedValue.Value,
      source = toSource value ∧ core = SourceStagedValue.toCore value := by
  induction related with
  | unit => exact ⟨.unit, rfl, rfl⟩
  | bool value => exact ⟨.bool value, rfl, rfl⟩
  | word value => exact ⟨.word value, rfl, rfl⟩
  | product _ _ left right =>
      obtain ⟨leftValue, rfl, rfl⟩ := left
      obtain ⟨rightValue, rfl, rfl⟩ := right
      exact ⟨.product leftValue rightValue, rfl, rfl⟩

theorem toSource_injective : Function.Injective toSource := by
  intro left
  induction left with
  | unit =>
      intro right equal
      cases right <;> cases equal
      rfl
  | bool value =>
      intro right equal
      cases right <;> cases equal
      rfl
  | word value =>
      intro right equal
      cases right <;> cases equal
      rfl
  | product left right leftInduction rightInduction =>
      intro other equal
      cases other with
      | unit | bool | word => cases equal
      | product otherLeft otherRight =>
          obtain ⟨leftEqual, rightEqual⟩ := Dynamic.Value.product.inj equal
          rw [leftInduction leftEqual, rightInduction rightEqual]

/-- The representation neither conflates source values nor admits several
different Core encodings of a single staged value. -/
theorem represents_toSource_iff (value : SourceStagedValue.Value)
    (core : Core.Value) :
    Represents (toSource value) core ↔ core = SourceStagedValue.toCore value := by
  constructor
  · intro related
    obtain ⟨other, sameSource, sameCore⟩ := related.exists_staged
    have equal := toSource_injective sameSource
    simpa only [← equal] using sameCore
  · intro equal
    rw [equal]
    exact toCore_represents value

/-- The actual Core constant expression returns the represented value and
leaves every surrounding store unchanged. -/
theorem toCoreExpr_evaluates (value : SourceStagedValue.Value)
    (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates environment store (SourceStagedValue.toCoreExpr value)
      (SourceStagedValue.toCore value) store := by
  induction value with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | product _ _ left right => exact .pair left right

/-- Reflection includes the final store, rather than only the returned value. -/
theorem toCoreExpr_evaluates_iff (value : SourceStagedValue.Value)
    (environment : Core.Environment) (initial : Core.Store)
    (result : Core.Value) (final : Core.Store) :
    Core.Evaluates environment initial (SourceStagedValue.toCoreExpr value)
        result final ↔
      Represents (toSource value) result ∧ final = initial := by
  constructor
  · intro evaluated
    obtain ⟨resultEqual, storeEqual⟩ := Core.evaluation_deterministic evaluated
      (toCoreExpr_evaluates value environment initial)
    exact ⟨(represents_toSource_iff value result).2 resultEqual, storeEqual⟩
  · rintro ⟨related, sameStore⟩
    subst final
    rw [(represents_toSource_iff value result).1 related]
    exact toCoreExpr_evaluates value environment initial

/-- Reification has a finite execution witness; no general source termination
claim or typed-source execution premise is needed. -/
theorem toCoreExpr_run_complete (value : SourceStagedValue.Value)
    (environment : Core.Environment) (store : Core.Store) :
    ∃ required, ∀ fuel, required ≤ fuel →
      Core.runStateful fuel
          (Core.State.initial (SourceStagedValue.toCoreExpr value)
            environment store) =
        .done (SourceStagedValue.toCore value) store :=
  Core.evaluation_runStateful_complete_with_sufficient_fuel
    (toCoreExpr_evaluates value environment store)

/-- Any completed execution of a reified constant reflects its independent
source value and has no store effects. -/
theorem toCoreExpr_run_sound (value : SourceStagedValue.Value)
    (environment : Core.Environment) (initial : Core.Store)
    {fuel : Nat} {result : Core.Value} {final : Core.Store}
    (executed : Core.runStateful fuel
      (Core.State.initial (SourceStagedValue.toCoreExpr value)
        environment initial) = .done result final) :
    Represents (toSource value) result ∧ final = initial :=
  (toCoreExpr_evaluates_iff value environment initial result final).1
    (Core.runStateful_evaluation_sound executed)

end StagedValue

end Solcore.SourceSemantics.CoreLowering
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ReadOnlyRenaming
/-! Exact renaming for a restricted Core expression grammar. It reads existing
values but never creates or calls a closure, allocates, or writes a cell.
Consequently inserted lexical binders do not change any returned value or
store, even when the existing environment and store contain closures. This is
not an exact-renaming claim for arbitrary Core programs. -/

set_option autoImplicit false

namespace Solcore.Core.ReadOnly

inductive Expression : Expr → Prop where
  | unit : Expression .unit
  | bool {value} : Expression (.bool value)
  | word {value} : Expression (.word value)
  | var {index} : Expression (.var index)
  | pair {left right} : Expression left → Expression right → Expression (.pair left right)
  | first {operand} : Expression operand → Expression (.first operand)
  | second {operand} : Expression operand → Expression (.second operand)
  | inLeft {type payload} : Expression payload → Expression (.inLeft type payload)
  | inRight {type payload} : Expression payload → Expression (.inRight type payload)
  | caseE {scrutinee left right} : Expression scrutinee → Expression left → Expression right →
      Expression (.caseE scrutinee left right)
  | loadCell {reference} : Expression reference → Expression (.loadCell reference)
  | unary {operator operand} : Expression operand → Expression (.unary operator operand)
  | binary {operator left right} : Expression left → Expression right → Expression (.binary operator left right)
  | ternary {operator first second third} : Expression first → Expression second → Expression third →
      Expression (.ternary operator first second third)
  | letE {value body} : Expression value → Expression body → Expression (.letE value body)
  | ifE {condition left right} : Expression condition → Expression left → Expression right →
      Expression (.ifE condition left right)

/-- Lookups return the same value; no closure environment is rewritten. -/
def EnvironmentsAgree (mapping : Renaming) (source target : Environment) : Prop :=
  ∀ {index : Nat} {value : Value}, source[index]? = some value → target[mapping index]? = some value

theorem EnvironmentsAgree.lift {mapping : Renaming} {source target : Environment}
    (related : EnvironmentsAgree mapping source target) (value : Value) :
    EnvironmentsAgree mapping.lift (value :: source) (value :: target) := by
  intro index foundValue found
  cases index with
  | zero => exact found
  | succ index => exact related found

theorem EnvironmentsAgree.insertion (environment : Environment) (cutoff : Nat) (inserted : Value) :
    EnvironmentsAgree (Renaming.insertion cutoff) environment (Environment.insertAt environment cutoff inserted) := by
  induction environment generalizing cutoff with
  | nil => intro index value impossible; simp at impossible
  | cons head tail ih =>
      cases cutoff with
      | zero => intro index value found; simpa [Renaming.insertion, Environment.insertAt] using found
      | succ cutoff =>
          intro index value found
          have lifted := EnvironmentsAgree.lift (ih cutoff) head found
          simpa only [Environment.insertAt, Renaming.lift_insertion] using lifted

theorem Expression.rename {expression : Expr} (restricted : Expression expression) (mapping : Renaming) :
    Expression (expression.rename mapping) := by
  induction restricted generalizing mapping with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | var => exact .var
  | pair _ _ left right => exact .pair (left mapping) (right mapping)
  | first _ ih => exact .first (ih mapping)
  | second _ ih => exact .second (ih mapping)
  | inLeft _ ih => exact .inLeft (ih mapping)
  | inRight _ ih => exact .inRight (ih mapping)
  | caseE _ _ _ scrutinee left right => exact .caseE (scrutinee mapping) (left mapping.lift) (right mapping.lift)
  | loadCell _ ih => exact .loadCell (ih mapping)
  | unary _ ih => exact .unary (ih mapping)
  | binary _ _ left right => exact .binary (left mapping) (right mapping)
  | ternary _ _ _ first second third => exact .ternary (first mapping) (second mapping) (third mapping)
  | letE _ _ value body => exact .letE (value mapping) (body mapping.lift)
  | ifE _ _ _ condition left right => exact .ifE (condition mapping) (left mapping) (right mapping)

theorem Expression.weakenAt {expression : Expr} (restricted : Expression expression) (cutoff : Nat) :
    Expression (expression.weakenAt cutoff) := by
  simpa using restricted.rename (Renaming.insertion cutoff)

/-- Transport an existing finite evaluation using the syntax restriction and
lookup agreement. No store typing or first-order payload premise is needed. -/
theorem Expression.evaluation_rename {expression : Expr} (restricted : Expression expression)
    {environment target : Environment} {before after : Store} {result : Value} {mapping : Renaming}
    (evaluation : Evaluates environment before expression result after)
    (related : EnvironmentsAgree mapping environment target) :
    Evaluates target before (expression.rename mapping) result after := by
  induction restricted generalizing environment target before after result mapping with
  | unit => cases evaluation; exact .unit
  | bool => cases evaluation; exact .bool
  | word => cases evaluation; exact .word
  | var => cases evaluation with | var found => exact .var (related found)
  | pair _ _ left right =>
      cases evaluation with
      | pair leftEvaluation rightEvaluation => exact .pair (left leftEvaluation related) (right rightEvaluation related)
  | first _ ih => cases evaluation with | first evaluated => exact .first (ih evaluated related)
  | second _ ih => cases evaluation with | second evaluated => exact .second (ih evaluated related)
  | inLeft _ ih => cases evaluation with | inLeft evaluated => exact .inLeft (ih evaluated related)
  | inRight _ ih => cases evaluation with | inRight evaluated => exact .inRight (ih evaluated related)
  | caseE _ _ _ scrutinee left right =>
      cases evaluation with
      | caseLeft selected branch => exact .caseLeft (scrutinee selected related) (left branch (related.lift _))
      | caseRight selected branch => exact .caseRight (scrutinee selected related) (right branch (related.lift _))
  | loadCell _ ih =>
      cases evaluation with
      | loadCell reference read => exact .loadCell (ih reference related) read
  | unary _ ih => cases evaluation with | unary evaluated applied => exact .unary (ih evaluated related) applied
  | binary _ _ left right =>
      cases evaluation with
      | binary leftEvaluation rightEvaluation applied =>
          exact .binary (left leftEvaluation related) (right rightEvaluation related) applied
  | ternary _ _ _ first second third =>
      cases evaluation with
      | ternary firstEvaluation secondEvaluation thirdEvaluation applied =>
          exact .ternary (first firstEvaluation related) (second secondEvaluation related) (third thirdEvaluation related) applied
  | letE _ _ value body =>
      cases evaluation with
      | letE evaluated branch => exact .letE (value evaluated related) (body branch (related.lift _))
  | ifE _ _ _ condition left right =>
      cases evaluation with
      | ifTrue selected branch => exact .ifTrue (condition selected related) (left branch related)
      | ifFalse selected branch => exact .ifFalse (condition selected related) (right branch related)

theorem Expression.evaluation_weakenAt {expression : Expr} (restricted : Expression expression)
    {environment : Environment} {before after : Store} {result : Value}
    (evaluation : Evaluates environment before expression result after) (cutoff : Nat) (inserted : Value) :
    Evaluates (Environment.insertAt environment cutoff inserted) before (expression.weakenAt cutoff) result after := by
  simpa using restricted.evaluation_rename evaluation (EnvironmentsAgree.insertion environment cutoff inserted)

theorem Expression.evaluation_weakenAt_zero {expression : Expr} (restricted : Expression expression)
    {environment : Environment} {before after : Store} {result : Value}
    (evaluation : Evaluates environment before expression result after) (inserted : Value) :
    Evaluates (inserted :: environment) before (expression.weakenAt 0) result after := by
  simpa [Environment.insertAt] using restricted.evaluation_weakenAt evaluation 0 inserted

end Solcore.Core.ReadOnly
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ScalarStatementViews
/-! Occurrence-unique inversion views for the source statement judgments.
These views inspect declarative derivations and do not evaluate source code. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ScalarStatementViews

open Frontend Frontend.SourceInference

private theorem statement_shape {source : TypedSource} {id : StatementId} {node : StatementNode}
    {form : StatementForm} (unique : NodeOccurrencesUnique source)
    (contains : ContainsStatement source id node) (sameForm : node.form = form) :
    ∀ other, ContainsStatement source id other → other.form = form := by
  intro other otherContains
  have same : other = node := Option.some.inj
    ((lookupStatement?_complete unique otherContains).symm.trans (lookupStatement?_complete unique contains))
  exact same ▸ sameForm

section Views

variable {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : StatementId} {node : StatementNode} {outcome : Dynamic.ControlOutcome}
  (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)

include unique contains

theorem breaking (form : node.form = .breakStmt)
    (evaluated : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ outcome = .breaking environment ∧ after = before := by
  have shape := statement_shape unique contains form
  clear contains form
  cases evaluated <;> have actualForm := shape _ (by assumption) <;> simp_all

theorem continuing (form : node.form = .continueStmt)
    (evaluated : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ outcome = .continuing environment ∧ after = before := by
  have shape := statement_shape unique contains form
  clear contains form
  cases evaluated <;> have actualForm := shape _ (by assumption) <;> simp_all

theorem returnUnit (form : node.form = .returnStmt none)
    (evaluated : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ outcome = .returned .unit ∧ after = before := by
  have shape := statement_shape unique contains form
  clear contains form
  cases evaluated <;> have actualForm := shape _ (by assumption) <;> simp_all

theorem returnValue {expression : ExpressionId} (form : node.form = .returnStmt (some expression))
    (evaluated : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ ∃ value, outcome = .returned value ∧
      Dynamic.ExpressionEvaluates program context evidence source environment before expression value after := by
  have shape := statement_shape unique contains form
  clear contains form
  cases evaluated <;> have actualForm := shape _ (by assumption) <;> simp_all

theorem expression {expression : ExpressionId} {semicolon : Bool} (form : node.form = .expression expression semicolon)
    (evaluated : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ outcome = .fallthrough environment ∧ ∃ value,
      Dynamic.ExpressionEvaluates program context evidence source environment before expression value after := by
  have shape := statement_shape unique contains form
  clear contains form
  cases evaluated <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨_, by assumption⟩

theorem assignValue {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (form : node.form = .assignValue assignment operator rhs)
    (evaluated : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ outcome = .fallthrough environment ∧ ∃ updated,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before assignment.target rhs updated after := by
  have shape := statement_shape unique contains form
  clear contains form
  cases evaluated <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨_, by assumption⟩

theorem letUninitialized {binder : TypedBinder} (form : node.form = .letDecl binder none)
    (evaluated : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    BinderExtends source.owner context binder finalContext ∧ ∃ location,
      outcome = .fallthrough ((binder.id, location) :: environment) ∧
      Dynamic.Heap.Allocates before binder.scheme.body none location after := by
  have shape := statement_shape unique contains form
  clear contains form
  cases evaluated <;> have actualForm := shape _ (by assumption) <;> simp_all

theorem letInitialized {binder : TypedBinder} {initializer : ExpressionId}
    (form : node.form = .letDecl binder (some initializer)) (mono : binder.scheme.quantified = [])
    (evaluated : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    BinderExtends source.owner context binder finalContext ∧ ∃ location value middle,
      outcome = .fallthrough ((binder.id, location) :: environment) ∧
      Dynamic.ExpressionEvaluates program context evidence source environment before initializer value middle ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location after := by
  have shape := statement_shape unique contains form
  clear contains form
  cases evaluated <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨_, _, by assumption, by assumption⟩

theorem block {statements : List StatementId} (form : node.form = .block statements)
    (evaluated : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ ∃ innerContext innerOutcome,
      outcome = Dynamic.restoreControl environment innerOutcome ∧
      Dynamic.StatementsExecute program context evidence source environment before statements innerContext innerOutcome after := by
  have shape := statement_shape unique contains form
  clear contains form
  cases evaluated <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨_, _, rfl, by assumption⟩

theorem whileLoop {condition : ExpressionId} {statements : List StatementId} (form : node.form = .whileLoop condition statements)
    (evaluated : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ ∃ innerContext innerOutcome,
      outcome = Dynamic.restoreControl environment innerOutcome ∧
      Dynamic.WhileExecutes program context evidence source environment before condition statements innerContext innerOutcome after := by
  have shape := statement_shape unique contains form
  clear contains form
  cases evaluated <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨_, _, rfl, by assumption⟩

theorem ifThen {condition : ExpressionId} {thenBody : List StatementId} {elseBody : Option (List StatementId)}
    (form : node.form = .ifThen condition thenBody elseBody)
    (evaluated : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ ∃ boolean middle innerContext innerOutcome,
      Dynamic.ExpressionEvaluates program context evidence source environment before condition (.bool boolean) middle ∧
      outcome = Dynamic.restoreControl environment innerOutcome ∧
      Dynamic.StatementsExecute program context evidence source environment middle
        (if boolean then thenBody else elseBody.getD []) innerContext innerOutcome after := by
  have shape := statement_shape unique contains form
  clear contains form
  cases evaluated <;> have actualForm := shape _ (by assumption) <;> simp_all
  · exact .inr ⟨_, by assumption, _, _, rfl, by assumption⟩
  · exact .inl ⟨_, by assumption, context, .fallthrough environment, rfl, .nil⟩
  · exact .inl ⟨_, by assumption, _, _, rfl, by assumption⟩

variable {reason : Dynamic.SemanticFault}

omit unique in
private theorem not_missing : ¬ Dynamic.StatementMissing source id :=
  fun absent => Dynamic.StatementAbsentIn.excludes_contains absent contains

theorem breaking_cannot_fault (form : node.form = .breakStmt)
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) : False := by
  have shape := statement_shape unique contains form
  have present := not_missing contains
  clear contains form
  cases fault
  all_goals first
    | exact present (by assumption)
    | have actualForm := shape _ (by assumption); simp_all

theorem continuing_cannot_fault (form : node.form = .continueStmt)
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) : False := by
  have shape := statement_shape unique contains form
  have present := not_missing contains
  clear contains form
  cases fault
  all_goals first
    | exact present (by assumption)
    | have actualForm := shape _ (by assumption); simp_all

theorem returnUnit_cannot_fault (form : node.form = .returnStmt none)
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) : False := by
  have shape := statement_shape unique contains form
  have present := not_missing contains
  clear contains form
  cases fault
  all_goals first
    | exact present (by assumption)
    | have actualForm := shape _ (by assumption); simp_all

theorem returnValue_fault {expression : ExpressionId} (form : node.form = .returnStmt (some expression))
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) :
    Dynamic.ExpressionFaults program context evidence source environment before expression reason after := by
  have shape := statement_shape unique contains form
  have present := not_missing contains
  clear contains form
  cases fault
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := shape _ (by assumption); simp_all

theorem expression_fault {expression : ExpressionId} {semicolon : Bool} (form : node.form = .expression expression semicolon)
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) :
    Dynamic.ExpressionFaults program context evidence source environment before expression reason after := by
  have shape := statement_shape unique contains form
  have present := not_missing contains
  clear contains form
  cases fault
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := shape _ (by assumption); simp_all

theorem assignValue_fault {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (form : node.form = .assignValue assignment operator rhs)
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) :
    Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target operator rhs reason after := by
  have shape := statement_shape unique contains form
  have present := not_missing contains
  clear contains form
  cases fault
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := shape _ (by assumption); simp_all

theorem letUninitialized_cannot_fault {binder : TypedBinder} (form : node.form = .letDecl binder none)
    (mono : binder.scheme.quantified = [])
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) : False := by
  have shape := statement_shape unique contains form
  have present := not_missing contains
  clear contains form
  cases fault
  all_goals first
    | exact present (by assumption)
    | have actualForm := shape _ (by assumption); simp_all

theorem letInitialized_fault {binder : TypedBinder} {initializer : ExpressionId}
    (form : node.form = .letDecl binder (some initializer)) (mono : binder.scheme.quantified = [])
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) :
    Dynamic.ExpressionFaults program context evidence source environment before initializer reason after := by
  have shape := statement_shape unique contains form
  have present := not_missing contains
  clear contains form
  cases fault
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := shape _ (by assumption); simp_all

theorem block_fault {statements : List StatementId} (form : node.form = .block statements)
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) :
    ∃ innerContext, Dynamic.StatementsFault program context evidence source environment before statements innerContext reason after := by
  have shape := statement_shape unique contains form
  have present := not_missing contains
  clear contains form
  cases fault
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := shape _ (by assumption); simp_all
  exact ⟨_, by assumption⟩

theorem whileLoop_fault {condition : ExpressionId} {statements : List StatementId} (form : node.form = .whileLoop condition statements)
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) :
    Dynamic.WhileFaults program context evidence source environment before condition statements reason after := by
  have shape := statement_shape unique contains form
  have present := not_missing contains
  clear contains form
  cases fault
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := shape _ (by assumption); simp_all

theorem ifThen_fault {condition : ExpressionId} {thenBody : List StatementId} {elseBody : Option (List StatementId)}
    (form : node.form = .ifThen condition thenBody elseBody)
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) :
    Dynamic.ExpressionFaults program context evidence source environment before condition reason after ∨
    (∃ value actualType,
      Dynamic.ExpressionEvaluates program context evidence source environment before condition value after ∧
      (¬ Dynamic.BooleanValue value) ∧ Dynamic.ValueRuntimeType value actualType ∧ reason = .typeMismatch .bool actualType) ∨
    (∃ boolean middle innerContext,
      Dynamic.ExpressionEvaluates program context evidence source environment before condition (.bool boolean) middle ∧
      Dynamic.StatementsFault program context evidence source environment middle
        (if boolean then thenBody else elseBody.getD []) innerContext reason after) := by
  have shape := statement_shape unique contains form
  have present := not_missing contains
  clear contains form
  cases fault
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := shape _ (by assumption); simp_all
  · exact .inr (.inl ⟨_, by assumption, by assumption, by assumption⟩)
  · exact .inr (.inr (.inr ⟨_, by assumption, _, by assumption⟩))
  · exact .inr (.inr (.inl ⟨_, by assumption, _, by assumption⟩))

end Views

/-- Function mode adds only the implicit final-expression convention. -/
def ListExecutes (functionMode : Bool) (program : Program) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (statements : List StatementId) (finalContext : Context)
    (outcome : Dynamic.ControlOutcome) (after : Dynamic.Heap) : Prop :=
  if functionMode then Dynamic.FunctionStatementsExecute program context evidence source environment before statements finalContext outcome after
  else Dynamic.StatementsExecute program context evidence source environment before statements finalContext outcome after

def ListFaults (functionMode : Bool) (program : Program) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (statements : List StatementId) (finalContext : Context)
    (reason : Dynamic.SemanticFault) (after : Dynamic.Heap) : Prop :=
  if functionMode then Dynamic.FunctionStatementsFault program context evidence source environment before statements finalContext reason after
  else Dynamic.StatementsFault program context evidence source environment before statements finalContext reason after

theorem nil_view
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ControlOutcome} (functionMode : Bool)
    (executed : ListExecutes functionMode program context evidence source environment before [] finalContext outcome after) :
    finalContext = context ∧ outcome = .fallthrough environment ∧ after = before := by
  cases functionMode <;> cases executed <;> exact ⟨rfl, rfl, rfl⟩

theorem nil_cannot_fault
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {reason : Dynamic.SemanticFault} (functionMode : Bool)
    (fault : ListFaults functionMode program context evidence source environment before [] finalContext reason after) : False := by
  cases functionMode <;> cases fault

/-- Every non-tail-expression head either continues with the remainder or
terminates at the head. Context/environment changes are retained exactly. -/
theorem cons_view
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ControlOutcome} {id : StatementId} {node : StatementNode} {rest : List StatementId}
    (functionMode : Bool) (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (notTail : functionMode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false)
    (executed : ListExecutes functionMode program context evidence source environment before (id :: rest) finalContext outcome after) :
    (∃ middleContext nextEnvironment middle,
      Dynamic.StatementExecutes program context evidence source environment before id middleContext (.fallthrough nextEnvironment) middle ∧
      ListExecutes functionMode program middleContext evidence source nextEnvironment middle rest finalContext outcome after) ∨
    (Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after ∧ Dynamic.TerminalControl outcome) := by
  cases functionMode with
  | false =>
      cases executed with
      | cons head tail => exact .inl ⟨_, _, _, head, tail⟩
      | terminal head terminal => exact .inr ⟨head, terminal⟩
  | true =>
      cases executed with
      | tailExpression otherContains form _ =>
          have same := statement_shape unique otherContains form _ contains
          exact False.elim (notTail rfl rfl _ same)
      | singleton _ _ head =>
          cases outcome with
          | fallthrough nextEnvironment => exact .inl ⟨_, nextEnvironment, _, head, .nil⟩
          | returned value => exact .inr ⟨head, .returned value⟩
          | breaking nextEnvironment => exact .inr ⟨head, .breaking nextEnvironment⟩
          | continuing nextEnvironment => exact .inr ⟨head, .continuing nextEnvironment⟩
          | fault reason => exact .inr ⟨head, .fault reason⟩
      | cons head tail => exact .inl ⟨_, _, _, head, tail⟩
      | terminal head terminal => exact .inr ⟨head, terminal⟩

theorem cons_fault_view
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {reason : Dynamic.SemanticFault} {id : StatementId} {node : StatementNode} {rest : List StatementId}
    (functionMode : Bool) (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (notTail : functionMode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false)
    (fault : ListFaults functionMode program context evidence source environment before (id :: rest) finalContext reason after) :
    (finalContext = context ∧ Dynamic.StatementFaults program context evidence source environment before id reason after) ∨
    (∃ middleContext nextEnvironment middle,
      Dynamic.StatementExecutes program context evidence source environment before id middleContext (.fallthrough nextEnvironment) middle ∧
      ListFaults functionMode program middleContext evidence source nextEnvironment middle rest finalContext reason after) := by
  cases functionMode with
  | false =>
      cases fault with
      | head fault => exact .inl ⟨rfl, fault⟩
      | tail head tail => exact .inr ⟨_, _, _, head, tail⟩
  | true =>
      cases fault with
      | singleton fault | head fault => exact .inl ⟨rfl, fault⟩
      | tailExpression otherContains form _ =>
          have same := statement_shape unique otherContains form _ contains
          exact False.elim (notTail rfl rfl _ same)
      | tail head tail => exact .inr ⟨_, _, _, head, tail⟩

end Solcore.SourceSemantics.CoreLowering.ScalarStatementViews
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.Literals
/-!
Meaning preservation for the existing expression lowerer's literal trees.

The certificate below is a declarative finite grammar over actual source
occurrences. It requires exact type metadata, empty evidence/coercion paths,
and strict in-range Word literals. It neither assumes a compiler result nor
uses the typed-source evaluator. The internal lowering profile has no staged
cache, so these results do not establish correctness of staging or of the
whole-program compilation pipeline.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.Literals

open Frontend Frontend.SourceInference TypeSystem

/-- Closed literal trees accepted by the current ordinary-expression profile.
The index records a sufficient traversal depth, not runtime execution fuel. -/
inductive Tree (source : TypedSource) :
    ExpressionId → SourceStagedValue.Value → Nat → Prop where
  | unit {id : ExpressionId} {node : ExpressionNode}
      (contains : ContainsExpression source id node)
      (form : node.form = .tuple []) (typed : node.type = .unit)
      (requirements : node.requirements = []) (coercions : node.coercions = []) :
      Tree source id .unit 1
  | bool {id : ExpressionId} {node : ExpressionNode} {name : String} {value : Bool}
      (contains : ContainsExpression source id node)
      (form : node.form = .reference name (.builtinBoolean value))
      (typed : node.type = .bool)
      (requirements : node.requirements = []) (coercions : node.coercions = []) :
      Tree source id (.bool value) 1
  | word {id : ExpressionId} {node : ExpressionNode}
      {literal : Syntax.CoreLiteralValue} {value : Core.Word}
      (contains : ContainsExpression source id node)
      (form : node.form = .literal literal) (typed : node.type = .word)
      (requirements : node.requirements = []) (coercions : node.coercions = [])
      (meaning : WordLiteralDenotes ⟨node.span, literal⟩ value) :
      Tree source id (.word value) 1
  | pair {id leftId rightId : ExpressionId} {node : ExpressionNode}
      {left right : SourceStagedValue.Value} {leftDepth rightDepth : Nat}
      (contains : ContainsExpression source id node)
      (form : node.form = .tuple [leftId, rightId])
      (typed : node.type = .product (SourceStagedValue.sourceType left)
        (SourceStagedValue.sourceType right))
      (requirements : node.requirements = []) (coercions : node.coercions = [])
      (leftTree : Tree source leftId left leftDepth)
      (rightTree : Tree source rightId right rightDepth) :
      Tree source id (.product left right) (max leftDepth rightDepth + 1)

private theorem lowerType_sourceType (value : SourceStagedValue.Value)
    (site : SourceCoreElaboration.ErrorSite) :
    SourceCoreElaboration.lowerType site (SourceStagedValue.sourceType value) =
      .ok (SourceStagedValue.coreType value) := by
  induction value with
  | unit | bool | word => rfl
  | product left right leftInduction rightInduction =>
      exact SourceCoreElaboration.lowerType_product leftInduction rightInduction

/-- The actual recursive lowerer succeeds for every sufficient traversal
budget; no lowering-success premise appears in the certificate. -/
theorem Tree.lower {source : TypedSource} {id : ExpressionId}
    {value : SourceStagedValue.Value} {depth : Nat}
    (tree : Tree source id value depth) (unique : NodeOccurrencesUnique source)
    (scope : Resolved.Context) (fuel : Nat) (enough : depth ≤ fuel) :
    SourceCoreElaboration.Internal.lowerExpression fuel source scope id =
      .ok { resolved := SourceStagedValue.toResolved value
            consumedRequirements := [] } := by
  induction tree generalizing fuel with
  | unit contains form typed requirements coercions =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreElaboration.Internal.lowerExpression_unit
            fuel source scope _ _ (lookupExpression?_complete unique contains)
            form typed requirements coercions
  | bool contains form typed requirements coercions =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreElaboration.Internal.lowerExpression_bool
            fuel source scope _ _ _ _ (lookupExpression?_complete unique contains)
            form typed requirements coercions
  | word contains form typed requirements coercions meaning =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreElaboration.Internal.lowerExpression_word
            fuel source scope _ _ _ _ (lookupExpression?_complete unique contains)
            form typed requirements coercions meaning
  | pair contains form typed requirements coercions _ _ leftInduction rightInduction =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          exact SourceCoreElaboration.Internal.lowerExpression_pair fuel source scope
            _ _ _ _ _ _ _ _ _ _ (lookupExpression?_complete unique contains)
            form typed requirements coercions (lowerType_sourceType _ _)
            (lowerType_sourceType _ _) (leftInduction fuel (by omega))
            (rightInduction fuel (by omega))

private theorem word_constructs {span : Syntax.SourceSpan}
    {literal : Syntax.CoreLiteralValue} {value : Core.Word}
    (meaning : WordLiteralDenotes ⟨span, literal⟩ value) :
    Dynamic.LiteralConstructs literal (.word value) := by
  have modulo : Core.Word.ofNatModulo value.val = value := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt value.isLt
  rw [← modulo]
  exact .word meaning

/-- Each tree has an independent source derivation in every surrounding
runtime context, and does not change its heap. -/
theorem Tree.source_evaluates {source : TypedSource} {id : ExpressionId}
    {value : SourceStagedValue.Value} {depth : Nat}
    (tree : Tree source id value depth)
    (program : Program) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment)
    (heap : Dynamic.Heap) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap
      id (StagedValue.toSource value) heap := by
  induction tree with
  | unit contains form typed requirements coercions =>
      apply Dynamic.ExpressionEvaluates.intro contains
      · rw [form, requirements, coercions]
        exact .tuple rfl .nil .nil
      · rw [coercions]
        exact .nil
  | bool contains form typed requirements coercions =>
      apply Dynamic.ExpressionEvaluates.intro contains
      · rw [form, requirements, coercions]
        exact .builtinBoolean rfl
      · rw [coercions]
        exact .nil
  | word contains form typed requirements coercions meaning =>
      apply Dynamic.ExpressionEvaluates.intro contains
      · rw [form, requirements, coercions]
        exact .literal rfl (word_constructs meaning)
      · rw [coercions]
        exact .nil
  | pair contains form typed requirements coercions _ _ leftInduction rightInduction =>
      apply Dynamic.ExpressionEvaluates.intro contains
      · rw [form, requirements, coercions]
        exact .tuple rfl (.cons leftInduction (.cons rightInduction .nil))
          (.cons (.singleton _))
      · rw [coercions]
        exact .nil

private theorem contains_unique {source : TypedSource} {id : ExpressionId}
    {left right : ExpressionNode} (unique : NodeOccurrencesUnique source)
    (leftContains : ContainsExpression source id left)
    (rightContains : ContainsExpression source id right) : left = right := by
  have leftLookup := lookupExpression?_complete unique leftContains
  have rightLookup := lookupExpression?_complete unique rightContains
  rw [leftLookup] at rightLookup
  exact Option.some.inj rightLookup

private theorem expression_evaluation_raw
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode}
    {result : Dynamic.Value}
    (unique : NodeOccurrencesUnique source)
    (contains : ContainsExpression source id node)
    (ordinary : ∀ name binder, node.form ≠ .reference name (.local binder))
    (empty : node.coercions = [])
    (evaluated : Dynamic.ExpressionEvaluates program context evidence source
      environment before id result after) :
    Dynamic.ExpressionFormEvaluates program context evidence source environment
      before node.form node.requirements node.coercions result after := by
  cases evaluated with
  | intro otherContains form coercions =>
      have same := contains_unique unique otherContains contains
      rw [same] at form coercions
      rw [empty] at coercions
      cases coercions
      exact form
  | generalizedLocal otherContains form _ _ _ _ _ _ _ =>
      have same := contains_unique unique otherContains contains
      rw [same] at form
      exact False.elim (ordinary _ _ form)

/-- Every independent successful source derivation has exactly the literal
tree's value and unchanged heap. Occurrence uniqueness rules out an alternate
node at the same ID; no whole-language determinism assumption is used. -/
theorem Tree.source_sound {source : TypedSource} {id : ExpressionId}
    {value : SourceStagedValue.Value} {depth : Nat}
    (tree : Tree source id value depth) (unique : NodeOccurrencesUnique source)
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {result : Dynamic.Value}
    (evaluated : Dynamic.ExpressionEvaluates program context evidence source
      environment before id result after) :
    result = StagedValue.toSource value ∧ after = before := by
  induction tree generalizing before after result with
  | unit contains form typed requirements coercions =>
      have raw := expression_evaluation_raw unique contains
        (by simp [form]) coercions evaluated
      rw [form] at raw
      cases raw with
      | tuple _ elements pack =>
          cases elements
          cases pack
          exact ⟨rfl, rfl⟩
  | bool contains form typed requirements coercions =>
      have raw := expression_evaluation_raw unique contains
        (by simp [form]) coercions evaluated
      rw [form] at raw
      cases raw
      exact ⟨rfl, rfl⟩
  | word contains form typed requirements coercions meaning =>
      have raw := expression_evaluation_raw unique contains
        (by simp [form]) coercions evaluated
      rw [form] at raw
      cases raw with
      | literal _ construction =>
          exact ⟨Dynamic.LiteralConstructs.functional construction
            (word_constructs meaning), rfl⟩
  | pair contains form typed requirements coercions _ _ leftInduction rightInduction =>
      have raw := expression_evaluation_raw unique contains
        (by simp [form]) coercions evaluated
      rw [form] at raw
      cases raw with
      | tuple _ elements pack =>
          cases elements with
          | cons left rest =>
              cases rest with
              | cons right rest =>
                  cases rest
                  obtain ⟨rfl, rfl⟩ := leftInduction left
                  obtain ⟨rfl, rfl⟩ := rightInduction right
                  exact ⟨Dynamic.ValuesPack.functional pack
                    (.cons (.singleton _)), rfl⟩

/-- The existing ordinary expression traversal followed by the existing
resolved-to-Core traversal. This is a relation over their actual outputs. -/
def ExpressionLowers (fuel : Nat) (source : TypedSource)
    (scope : Resolved.Context) (id : ExpressionId) (expression : Core.Expr) : Prop :=
  ∃ lowered : SourceCoreElaboration.LoweredExpression,
    SourceCoreElaboration.Internal.lowerExpression fuel source scope id =
      .ok lowered ∧ lowered.resolved.lower? (scope.map Prod.fst) = some expression

section Correspondence

variable {source : TypedSource} {id : ExpressionId}
  {value : SourceStagedValue.Value} {depth traversalFuel : Nat}
  (tree : Tree source id value depth) (unique : NodeOccurrencesUnique source)
  (scope : Resolved.Context) (enough : depth ≤ traversalFuel)

include tree unique enough

/-- Construct an actual successful lowering, rather than requiring compiler
acceptance as part of the source certificate. -/
theorem Tree.lowers : ExpressionLowers traversalFuel source scope id
    (SourceStagedValue.toCoreExpr value) :=
  ⟨{ resolved := SourceStagedValue.toResolved value, consumedRequirements := [] },
    tree.lower unique scope traversalFuel enough,
    SourceStagedValue.toResolved_lower value (scope.map Prod.fst)⟩

theorem Tree.lowering_unique {expression : Core.Expr}
    (lowered : ExpressionLowers traversalFuel source scope id expression) :
    expression = SourceStagedValue.toCoreExpr value := by
  obtain ⟨intermediate, compiled, resolved⟩ := lowered
  rw [tree.lower unique scope traversalFuel enough] at compiled
  cases compiled
  rw [SourceStagedValue.toResolved_lower] at resolved
  exact (Option.some.inj resolved).symm

/-- Core checker acceptance is derived from the lowering output, rather than
added as an assumption of semantic preservation. -/
theorem Tree.lowered_infers {expression : Core.Expr}
    (lowered : ExpressionLowers traversalFuel source scope id expression)
    (context : Core.Context) (definitions : Core.DataEnvironment) :
    Core.infer? context expression definitions =
      some (SourceStagedValue.coreType value) := by
  rw [tree.lowering_unique unique scope enough lowered]
  exact StagedValue.toCoreExpr_infers value context definitions

/-- Finite successful executions agree in both directions. Both final heaps
are explicit: literal trees leave the source heap and the Core store intact.
The source side is the independent occurrence-based dynamic judgment. -/
theorem Tree.evaluates_iff {expression : Core.Expr}
    (lowered : ExpressionLowers traversalFuel source scope id expression)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (sourceEnvironment : Dynamic.Environment)
    (sourceBefore sourceAfter : Dynamic.Heap)
    (coreEnvironment : Core.Environment) (coreBefore coreAfter : Core.Store)
    (result : Core.Value) :
    (Core.Evaluates coreEnvironment coreBefore expression result coreAfter ∧
        sourceAfter = sourceBefore) ↔
      ∃ sourceResult,
        Dynamic.ExpressionEvaluates program context evidence source sourceEnvironment
          sourceBefore id sourceResult sourceAfter ∧
        StagedValue.Represents sourceResult result ∧ coreAfter = coreBefore := by
  rw [tree.lowering_unique unique scope enough lowered]
  constructor
  · rintro ⟨evaluated, sameHeap⟩
    subst sourceAfter
    obtain ⟨related, sameStore⟩ := (StagedValue.toCoreExpr_evaluates_iff value
      coreEnvironment coreBefore result coreAfter).1 evaluated
    exact ⟨StagedValue.toSource value,
      tree.source_evaluates program context evidence sourceEnvironment sourceBefore,
      related, sameStore⟩
  · rintro ⟨sourceResult, evaluated, related, sameStore⟩
    obtain ⟨sameValue, sameHeap⟩ := tree.source_sound unique evaluated
    rw [sameValue] at related
    exact ⟨(StagedValue.toCoreExpr_evaluates_iff value coreEnvironment coreBefore
      result coreAfter).2 ⟨related, sameStore⟩, sameHeap⟩

/-- A finite source derivation yields a sufficiently fueled completed Core
execution. Traversal fuel and runtime fuel are separate quantities. -/
theorem Tree.run_complete {expression : Core.Expr}
    (lowered : ExpressionLowers traversalFuel source scope id expression)
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {sourceEnvironment : Dynamic.Environment}
    {sourceBefore sourceAfter : Dynamic.Heap} {sourceResult : Dynamic.Value}
    (evaluated : Dynamic.ExpressionEvaluates program context evidence source
      sourceEnvironment sourceBefore id sourceResult sourceAfter)
    (coreEnvironment : Core.Environment) (coreBefore : Core.Store) :
    ∃ required, ∀ fuel, required ≤ fuel →
      ∃ result,
        Core.runStateful fuel (Core.State.initial expression coreEnvironment coreBefore) =
          .done result coreBefore ∧
        StagedValue.Represents sourceResult result ∧ sourceAfter = sourceBefore := by
  rw [tree.lowering_unique unique scope enough lowered]
  obtain ⟨sameValue, sameHeap⟩ := tree.source_sound unique evaluated
  obtain ⟨required, completes⟩ :=
    StagedValue.toCoreExpr_run_complete value coreEnvironment coreBefore
  refine ⟨required, fun fuel enoughFuel => ⟨SourceStagedValue.toCore value,
    completes fuel enoughFuel, ?_, sameHeap⟩⟩
  rw [sameValue]
  exact StagedValue.toCore_represents value

/-- Any completed Core execution of the actual lowering output reflects a
finite source derivation and its represented value, with both stores intact. -/
theorem Tree.run_sound {expression : Core.Expr}
    (lowered : ExpressionLowers traversalFuel source scope id expression)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (sourceEnvironment : Dynamic.Environment) (sourceHeap : Dynamic.Heap)
    (coreEnvironment : Core.Environment) (coreBefore : Core.Store)
    {fuel : Nat} {result : Core.Value} {coreAfter : Core.Store}
    (executed : Core.runStateful fuel
      (Core.State.initial expression coreEnvironment coreBefore) = .done result coreAfter) :
    ∃ sourceResult,
      Dynamic.ExpressionEvaluates program context evidence source sourceEnvironment
        sourceHeap id sourceResult sourceHeap ∧
      StagedValue.Represents sourceResult result ∧ coreAfter = coreBefore :=
  (tree.evaluates_iff unique scope enough lowered program context evidence
    sourceEnvironment sourceHeap sourceHeap coreEnvironment coreBefore coreAfter result).1
      ⟨Core.runStateful_evaluation_sound executed, rfl⟩

end Correspondence

end Solcore.SourceSemantics.CoreLowering.Literals
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.IntegerPrimitives
/-! Native mathematical-integer helper definitions implement the independent
source primitive relations, including all signs and the zero-divisor cases. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.IntegerPrimitives

open Solcore.SourceSemantics.Dynamic

theorem divide_source (left right : Int) :
    BinaryPrimitiveApplies .divide (.integer left) (.integer right)
      (.integer (Core.Integer.divide left right)) := by
  by_cases zero : right = 0
  · subst right
    simpa only [Core.Integer.divide_zero] using BinaryPrimitiveApplies.integerDivideZero left
  · simpa only [Core.Integer.divide_nonzero left right zero] using
      BinaryPrimitiveApplies.integerDivide left right zero

theorem modulo_source (left right : Int) :
    BinaryPrimitiveApplies .modulo (.integer left) (.integer right)
      (.integer (Core.Integer.modulo left right)) := by
  by_cases zero : right = 0
  · subst right
    simpa only [Core.Integer.modulo_zero] using BinaryPrimitiveApplies.integerModuloZero left
  · simpa only [Core.Integer.modulo_nonzero left right zero] using
      BinaryPrimitiveApplies.integerModulo left right zero

theorem bitAnd_eq_source (left right : Int) :
    Core.Integer.bitAnd left right = Dynamic.integerBitAnd left right := by
  cases left <;> cases right <;> rfl

theorem bitOr_eq_source (left right : Int) :
    Core.Integer.bitOr left right = Dynamic.integerBitOr left right := by
  cases left <;> cases right <;> rfl

theorem bitXor_eq_source (left right : Int) :
    Core.Integer.bitXor left right = Dynamic.integerBitXor left right := by
  cases left <;> cases right <;> rfl

theorem bitAnd_source (left right : Int) :
    BinaryPrimitiveApplies .bitAnd (.integer left) (.integer right)
      (.integer (Core.Integer.bitAnd left right)) := by
  rw [bitAnd_eq_source]
  exact .integerBitAnd left right

theorem bitOr_source (left right : Int) :
    BinaryPrimitiveApplies .bitOr (.integer left) (.integer right)
      (.integer (Core.Integer.bitOr left right)) := by
  rw [bitOr_eq_source]
  exact .integerBitOr left right

theorem bitXor_source (left right : Int) :
    BinaryPrimitiveApplies .bitXor (.integer left) (.integer right)
      (.integer (Core.Integer.bitXor left right)) := by
  rw [bitXor_eq_source]
  exact .integerBitXor left right

/-- Only mathematical scalar results cross this primitive correspondence. -/
inductive ResultRepresents : Dynamic.Value → Core.Value → Prop where
  | integer (value : Int) : ResultRepresents (.integer value) (.integer value)
  | word (value : Core.Word) : ResultRepresents (.word value) (.word value)
  | bool (value : Bool) : ResultRepresents (.bool value) (.bool value)

inductive BinaryOperation : Core.BinaryOp → Syntax.BinaryOp → Prop where
  | add : BinaryOperation .integerAdd .add
  | subtract : BinaryOperation .integerSub .subtract
  | multiply : BinaryOperation .integerMul .multiply
  | divide : BinaryOperation .integerDiv .divide
  | modulo : BinaryOperation .integerMod .modulo
  | bitAnd : BinaryOperation .integerAnd .bitAnd
  | bitOr : BinaryOperation .integerOr .bitOr
  | bitXor : BinaryOperation .integerXor .bitXor
  | equal : BinaryOperation .integerEq .equal
  | less : BinaryOperation .integerLt .less

private theorem equal_source (left right : Int) :
    BinaryPrimitiveApplies .equal (.integer left) (.integer right)
      (.bool (left == right)) := by
  by_cases same : left = right
  · subst right
    simpa using BinaryPrimitiveApplies.equalTrue
      (ValueEquivalent.refl (ValueComparable.integer left))
  · have different : ¬ ValueEquivalent (.integer left) (.integer right) := by
      intro equivalent
      exact same (Dynamic.Value.integer.inj equivalent.1)
    rw [beq_eq_false_iff_ne.mpr same]
    exact BinaryPrimitiveApplies.equalFalse different

theorem BinaryOperation.preserves {core : Core.BinaryOp} {source : Syntax.BinaryOp}
    (operation : BinaryOperation core source) (left right : Int) :
    ∃ sourceResult coreResult, ResultRepresents sourceResult coreResult ∧
      BinaryPrimitiveApplies source (.integer left) (.integer right) sourceResult ∧
      core.apply (.integer left) (.integer right) = some coreResult := by
  cases operation with
  | add => exact ⟨_, _, .integer _, .integerAdd left right, rfl⟩
  | subtract => exact ⟨_, _, .integer _, .integerSubtract left right, rfl⟩
  | multiply => exact ⟨_, _, .integer _, .integerMultiply left right, rfl⟩
  | divide => exact ⟨_, _, .integer _, divide_source left right, rfl⟩
  | modulo => exact ⟨_, _, .integer _, modulo_source left right, rfl⟩
  | bitAnd => exact ⟨_, _, .integer _, bitAnd_source left right, rfl⟩
  | bitOr => exact ⟨_, _, .integer _, bitOr_source left right, rfl⟩
  | bitXor => exact ⟨_, _, .integer _, bitXor_source left right, rfl⟩
  | equal => exact ⟨_, _, .bool _, equal_source left right, rfl⟩
  | less => exact ⟨_, _, .bool _, .integerLess left right, rfl⟩

/-- Native primitive evaluation preserves the source result while retaining
left-to-right operand effects and the exact final store. -/
theorem BinaryOperation.evaluates {core : Core.BinaryOp} {source : Syntax.BinaryOp}
    (operation : BinaryOperation core source)
    {environment : Core.Environment} {initialStore middleStore finalStore : Core.Store}
    {leftExpr rightExpr : Core.Expr} {left right : Int}
    (leftEvaluated : Core.Evaluates environment initialStore leftExpr (.integer left) middleStore)
    (rightEvaluated : Core.Evaluates environment middleStore rightExpr (.integer right) finalStore) :
    ∃ sourceResult coreResult, ResultRepresents sourceResult coreResult ∧
      BinaryPrimitiveApplies source (.integer left) (.integer right) sourceResult ∧
      Core.Evaluates environment initialStore (.binary core leftExpr rightExpr) coreResult finalStore := by
  obtain ⟨sourceResult, coreResult, represents, meaning, applied⟩ := operation.preserves left right
  exact ⟨sourceResult, coreResult, represents, meaning, .binary leftEvaluated rightEvaluated applied⟩

theorem bitNot_preserves (value : Int) :
    UnaryPrimitiveApplies .bitNot (.integer value) (.integer (~~~value)) ∧
      Core.UnaryOp.integerNot.apply (.integer value) = some (.integer (~~~value)) :=
  ⟨.integerBitNot value, rfl⟩

theorem integerToWord_preserves (value : Int) :
    BuiltinApplies .wordFromInteger [.integer value] (.word (Core.Word.ofIntModulo value)) ∧
      Core.UnaryOp.integerToWord.apply (.integer value) = some (.word (Core.Word.ofIntModulo value)) :=
  ⟨.wordFromInteger value, rfl⟩

theorem wordToInteger_preserves (value : Core.Word) :
    BuiltinApplies .wordToInteger [.word value] (.integer (Int.ofNat value.val)) ∧
      Core.UnaryOp.wordToInteger.apply (.word value) = some (.integer (Int.ofNat value.val)) :=
  ⟨.wordToInteger value, rfl⟩

end Solcore.SourceSemantics.CoreLowering.IntegerPrimitives
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.EmptySourceSubstitution
/-! The empty flexible substitution preserves the complete retained source
carrier, including staging flags and evidence metadata. This is a syntactic
identity law; it does not assert substitution correctness for execution. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.EmptySourceSubstitution
open Frontend Frontend.SourceInference TypeSystem

@[simp] theorem without (variables : List TypeVarId) :
    Substitution.without [] variables = [] := by
  induction variables with
  | nil => rfl
  | cons head rest ih => simpa [Substitution.without, Substitution.erase] using ih

@[simp] theorem type (value : Ty) : Substitution.apply [] value = value :=
  Substitution.empty_apply value

@[simp] theorem type_function : Substitution.apply [] = (id : Ty → Ty) := funext type

@[simp] theorem predicate (value : ProgramPredicate) :
    TypedTraitResolution.applySubstitution [] value = value := by
  simp [TypedTraitResolution.applySubstitution]

@[simp] theorem predicate_function : TypedTraitResolution.applySubstitution [] = (id : ProgramPredicate → ProgramPredicate) := funext predicate

@[simp] theorem scheme (value : Scheme) : Scheme.apply [] value = value := by
  simp [Scheme.apply]

@[simp] theorem requirement (value : LocalSchemeRequirement) :
    value.applySubstitution [] = value := by simp [LocalSchemeRequirement.applySubstitution]

@[simp] theorem requirement_function : LocalSchemeRequirement.applySubstitution [] = (id : LocalSchemeRequirement → LocalSchemeRequirement) := funext requirement

@[simp] theorem binder (value : TypedBinder) : value.applySubstitution [] = value := by
  simp [TypedBinder.applySubstitution]

@[simp] theorem binder_function : TypedBinder.applySubstitution [] = (id : TypedBinder → TypedBinder) := funext binder

@[simp] theorem integerResolution (value : IntegerLiteralResolution) :
    value.applySubstitution [] = value := by simp [IntegerLiteralResolution.applySubstitution]

@[simp] theorem declaration (value : DeclarationInstantiation) :
    value.applySubstitution [] = value := by
  unfold DeclarationInstantiation.applySubstitution
  change { value with
    parameterSubstitution := value.parameterSubstitution.map (fun p => (p.1, Substitution.apply [] p.2))
    type := Substitution.apply [] value.type
    predicates := value.predicates.map (TypedTraitResolution.applySubstitution []) } = value
  simp

@[simp] theorem constructor (value : DataConstructorInstantiation) :
    value.applySubstitution [] = value := by
  unfold DataConstructorInstantiation.applySubstitution
  change { value with
    parameterSubstitution := value.parameterSubstitution.map (fun p => (p.1, Substitution.apply [] p.2))
    payloadTypes := value.payloadTypes.map (Substitution.apply [])
    resultType := Substitution.apply [] value.resultType } = value
  simp

@[simp] theorem coercion (value : CoercionStep) : value.applySubstitution [] = value := by
  simp [CoercionStep.applySubstitution]

@[simp] theorem coercion_function : CoercionStep.applySubstitution [] = (id : CoercionStep → CoercionStep) := funext coercion

@[simp] theorem indirect (value : IndirectCallResolution) : value.applySubstitution [] = value := by
  cases value
  simp [IndirectCallResolution.applySubstitution]

@[simp] theorem reference (value : ReferenceResolution) : value.applySubstitution [] = value := by
  cases value <;> simp [ReferenceResolution.applySubstitution]

@[simp] theorem call (value : CallResolution) : value.applySubstitution [] = value := by
  cases value <;> simp [CallResolution.applySubstitution]

@[simp] theorem expressionForm (value : ExpressionForm) : value.applySubstitution [] = value := by
  cases value <;> simp [ExpressionForm.applySubstitution]

@[simp] theorem expression (value : ExpressionNode) : value.applySubstitution [] = value := by
  simp [ExpressionNode.applySubstitution]

@[simp] theorem instruction (value : MatchPatternInstruction) : value.applySubstitution [] = value := by
  cases value <;> simp [MatchPatternInstruction.applySubstitution]

@[simp] theorem instruction_function : MatchPatternInstruction.applySubstitution [] = (id : MatchPatternInstruction → MatchPatternInstruction) := funext instruction

@[simp] theorem resolution (value : MatchPatternResolution) : value.applySubstitution [] = value := by
  cases value <;> simp [MatchPatternResolution.applySubstitution]

@[simp] theorem pattern (value : TypedMatchPattern) : value.applySubstitution [] = value := by
  simp [TypedMatchPattern.applySubstitution]

@[simp] theorem matchCase (value : TypedMatchCase) : value.applySubstitution [] = value := by
  simp [TypedMatchCase.applySubstitution]

@[simp] theorem matchCase_function : TypedMatchCase.applySubstitution [] = (id : TypedMatchCase → TypedMatchCase) := funext matchCase

@[simp] theorem matchResolution (value : MatchResolution) : value.applySubstitution [] = value := by
  simp [MatchResolution.applySubstitution]

@[simp] theorem place (value : PlaceResolution) : value.applySubstitution [] = value := by
  simp [PlaceResolution.applySubstitution]

@[simp] theorem assignment (value : AssignmentResolution) : value.applySubstitution [] = value := by
  simp [AssignmentResolution.applySubstitution]

@[simp] theorem forItem (value : ForItemForm) : value.applySubstitution [] = value := by
  cases value <;> simp [ForItemForm.applySubstitution]

@[simp] theorem forItem_function : ForItemForm.applySubstitution [] = (id : ForItemForm → ForItemForm) := funext forItem

@[simp] theorem statementForm (value : StatementForm) : value.applySubstitution [] = value := by
  cases value <;> simp [StatementForm.applySubstitution]

@[simp] theorem statement (value : StatementNode) : value.applySubstitution [] = value := by
  simp [StatementNode.applySubstitution]

@[simp] theorem node (value : Node) : value.applySubstitution [] = value := by
  cases value <;> simp [Node.applySubstitution]

@[simp] theorem node_function : Node.applySubstitution [] = (id : Node → Node) := funext node

@[simp] theorem source (value : TypedSource) : value.applySubstitution [] = value := by
  simp [TypedSource.applySubstitution]

end Solcore.SourceSemantics.CoreLowering.EmptySourceSubstitution
end
