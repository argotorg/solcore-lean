import Solcore.SourceSemantics.Staging.RecursiveTraceSize
import Solcore.SourceSemantics.Staging.RecursiveBodyErasure
import Solcore.SourceSemantics.Dynamic.WholeLanguagePreservation

/-! Source heap preservation interfaces for faulting recursive staged traces.
Successful prefixes use the independent whole-language preservation theorem;
these interfaces retain the exact failure heap and original invocation scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.FaultPreservation
open Frontend SourceInference Solcore.SourceSemantics.Dynamic

variable (program : Program) (registry : Registry)

def ExpressionAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context : Context} {environment : Environment}
    {before after : Heap} {id : ExpressionId} {failure : Failure} {type : TypeSystem.Ty},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    ExpressionHasType scope.source context id type →
    Size.Expression program registry size scope context environment before id (.fault failure) after →
    HeapWellTyped context after ∧ HeapTypesExtend before after

def ExpressionsAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context : Context} {environment : Environment}
    {before after : Heap} {ids : List ExpressionId} {failure : Failure} {types : List TypeSystem.Ty},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    ExpressionsHaveTypes scope.source context ids types →
    Size.Expressions program registry size scope context environment before ids (.fault failure) after →
    HeapWellTyped context after ∧ HeapTypesExtend before after

def AppliesAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context : Context} {source : TypedSource}
    {before after : Heap} {callable : Value} {arguments : List Value} {packed : Value}
    {failure : Failure} {parameter result : TypeSystem.Ty},
    SourceRuntimeValid program context source → HeapWellTyped context before →
    ValueHasType context before callable (.function parameter result) →
    ValuesPack arguments packed → ValueHasType context before packed parameter →
    Size.Applies program registry size scope context before callable arguments (.fault failure) after →
    HeapWellTyped context after ∧ HeapTypesExtend before after

def StatementsAt (size : Nat) : Prop :=
  ∀ {mode : Bool} {scope : Scope} {context staticFinal runtimeFinal : Context} {environment : Environment}
    {before after : Heap} {statements : List StatementId} {failure : Failure}
    {control : ControlContext} {facts : BodyFacts},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    StatementsHaveType scope.source control context statements staticFinal facts →
    Size.StatementsIn program registry mode size scope context environment before statements runtimeFinal (.fault failure) after →
    HeapWellTyped context after ∧ HeapTypesExtend before after

/-- A faulting finite loop restores the original typing context after every
successful body prefix, including any cells allocated inside the iteration. -/
def WhileAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context bodyFinal : Context} {environment : Environment}
    {before after : Heap} {condition : ExpressionId} {statements : List StatementId}
    {failure : Failure} {control : ControlContext} {facts : BodyFacts},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    ExpressionHasType scope.source context condition .bool →
    StatementsHaveType scope.source control.enterLoop context statements bodyFinal facts →
    Size.While program registry size scope context environment before condition statements (.fault failure) after →
    HeapWellTyped context after ∧ HeapTypesExtend before after

/-- Match faults retain the actual hidden and pattern-binder allocations. -/
def MatchAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context : Context} {environment : Environment}
    {before after : Heap} {resolution : MatchResolution} {outcome : BodyOutcome}
    {failure : Failure} {control : ControlContext} {type : TypeSystem.Ty} {caseFacts : List BodyFacts},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    ExpressionHasType scope.source context resolution.scrutinee type →
    MatchCasesHaveType scope.source control context type resolution.cases caseFacts →
    (∀ statements, resolution.defaultBody = some statements →
      ∃ final facts, StatementsHaveType scope.source control context statements final facts) →
    Size.Match program registry size scope context environment before resolution outcome after →
    outcome = .fault failure → HeapWellTyped context after ∧ HeapTypesExtend before after

/-- Header faults retain all effects before the failing item, even when earlier
items introduced a new lexical context. -/
def ForItemsAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context staticFinal runtimeFinal : Context} {environment : Environment}
    {before after : Heap} {items : List ForItemForm} {failure : Failure} {control : ControlContext},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    ForItemsHaveType scope.source control context items staticFinal →
    Size.ForItems program registry size scope context environment before items runtimeFinal (.fault failure) after →
    HeapWellTyped context after ∧ HeapTypesExtend before after

/-- Each finite for iteration restores the loop context before its post items
and following test, without discarding any heap effects. -/
def ForLoopAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context bodyFinal postFinal : Context} {environment : Environment}
    {before after : Heap} {condition : ExpressionId} {post : List ForItemForm} {body : List StatementId}
    {failure : Failure} {control : ControlContext} {facts : BodyFacts},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    ExpressionHasType scope.source context condition .bool →
    StatementsHaveType scope.source control.enterLoop context body bodyFinal facts →
    ForItemsHaveType scope.source control.enterLoop context post postFinal →
    Size.ForLoop program registry size scope context environment before condition post body (.fault failure) after →
    HeapWellTyped context after ∧ HeapTypesExtend before after

variable {program registry}

/-- A typed successful prefix uses its actual erasure; no completion is added
or replaced when proving a later fault. -/
theorem expression_value (wellFormed : ProgramWellFormed program)
    {size : Nat} {scope : Scope} {context : Context} {environment : Environment}
    {before after : Heap} {id : ExpressionId} {value : Value} {type : TypeSystem.Ty}
    (runtime : SourceRuntimeValid program context scope.source) (covers : scope.evidence.Covers context)
    (locals : EnvironmentAgrees before context.locals environment) (heap : HeapWellTyped context before)
    (typed : ExpressionHasType scope.source context id type)
    (trace : Size.Expression program registry size scope context environment before id (.value value) after) :
    ExpressionEvaluationPreserved context before after value type :=
  wellFormed.wholeLanguagePreservation.expression _ _ _ _ _ _ _ _ _
    runtime covers locals heap typed trace.sound.value_plain

theorem expressions_values (wellFormed : ProgramWellFormed program)
    {size : Nat} {scope : Scope} {context : Context} {environment : Environment}
    {before after : Heap} {ids : List ExpressionId} {values : List Value} {types : List TypeSystem.Ty}
    (runtime : SourceRuntimeValid program context scope.source) (covers : scope.evidence.Covers context)
    (locals : EnvironmentAgrees before context.locals environment) (heap : HeapWellTyped context before)
    (typed : ExpressionsHaveTypes scope.source context ids types)
    (trace : Size.Expressions program registry size scope context environment before ids (.values values) after) :
    ValuesHaveTypes context after values types ∧ HeapWellTyped context after ∧ HeapTypesExtend before after :=
  match trace with
  | .nil => by cases typed; exact ⟨.nil, heap, .refl _⟩
  | .cons head tail => by
    cases typed with
    | cons headType tailType =>
      obtain ⟨headTyped, middleTyped, headExtends⟩ :=
        expression_value wellFormed runtime covers locals heap headType head
      obtain ⟨tailTyped, afterTyped, tailExtends⟩ := expressions_values wellFormed
        runtime covers (locals.mono headExtends) middleTyped tailType tail
      exact ⟨.cons (headTyped.mono tailExtends) tailTyped, afterTyped, headExtends.trans tailExtends⟩
  termination_by size
  decreasing_by exact Size.child_lt_stepSize (by simp)

/-- The used occurrence and source typing identify one actual raw form. -/
theorem expression_form {scope : Scope} {context : Context} {id : ExpressionId}
    {form : ExpressionForm} {type : TypeSystem.Ty} {requirements : List RequirementId}
    (unique : NodeOccurrencesUnique scope.source)
    (typed : ExpressionHasType scope.source context id type) (occurrence : Occurrence scope id form requirements) :
    ∃ raw plan, ExpressionFormHasRawType scope.source context form raw plan := by
  obtain ⟨node, contains, shape, _, _⟩ := occurrence
  cases typed with
  | @intro _ _ actual raw plan typedContains typedForm _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique typedContains).symm.trans
      (lookupExpression?_complete unique contains))
    cases same
    exact ⟨raw, plan, shape ▸ typedForm⟩

/-- The original uncoerced occurrence also retains the exact typing plan. -/
theorem expression_form_plan {scope : Scope} {context : Context} {id : ExpressionId}
    {form : ExpressionForm} {type : TypeSystem.Ty} {requirements : List RequirementId}
    (unique : NodeOccurrencesUnique scope.source)
    (typed : ExpressionHasType scope.source context id type) (occurrence : Occurrence scope id form requirements) :
    ∃ raw plan, ExpressionFormHasRawType scope.source context form raw plan ∧
      ExpressionRequirementPlan.Valid context raw type plan requirements [] := by
  obtain ⟨node, contains, shape, requirementsEq, coercionsEq⟩ := occurrence
  cases typed with
  | @intro _ _ actual raw plan typedContains typedForm _ _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique typedContains).symm.trans
      (lookupExpression?_complete unique contains))
    cases same
    exact ⟨raw, plan, shape ▸ typedForm, by simpa only [requirementsEq, coercionsEq] using valid⟩

/-- Atomic failures cannot execute a child or change the source heap. -/
theorem atomic_fault_heap {scope : Scope} {context : Context} {environment : Environment}
    {before after : Heap} {form : ExpressionForm} {requirements : List RequirementId} {reason : SemanticFault}
    (atomic : AtomicForm form)
    (trace : ExpressionFormFaults program context scope.evidence scope.source environment before
      form requirements [] reason after) : after = before := by
  cases atomic <;> cases trace <;> try rfl
  case unit.tuple children => cases children

end Solcore.SourceSemantics.Staging.Recursive.FaultPreservation
