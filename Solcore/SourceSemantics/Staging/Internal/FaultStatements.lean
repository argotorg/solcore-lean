import Solcore.SourceSemantics.Staging.Internal.TraceSize
import Solcore.SourceSemantics.Staging.Erasure
import Solcore.SourceSemantics.Dynamic.WholeLanguagePreservation
import Solcore.SourceSemantics.Staging.Internal.SelectedContracts

/-!
# Faulting statement sequences

Faulting statements preserve the heap of every executed prefix.
-/

section
-- leanmerge: from Solcore.SourceSemantics.Staging.RecursiveFaultPreservationSupport
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

def RawFormAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context : Context} {environment : Environment}
    {before after : Heap} {form : ExpressionForm} {requirements : List RequirementId}
    {coercions : List SourceInference.CoercionStep} {failure : Failure}
    {rawType finalType : TypeSystem.Ty} {plan : ExpressionRequirementPlan},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    (∃ id node, ContainsExpression scope.source id node ∧ node.form = form ∧ node.rawType = rawType) →
    ExpressionFormHasRawType scope.source context form rawType plan →
    ExpressionRequirementPlan.Valid context rawType finalType plan requirements coercions →
    Size.RawForm program registry size scope context environment before form requirements coercions (.fault failure) after →
    HeapWellTyped context after ∧ HeapTypesExtend before after

def CoercionStepAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context : Context} {before after : Heap} {step : SourceInference.CoercionStep}
    {input : Value} {failure : Failure},
    SourceRuntimeValid program context scope.source → HeapWellTyped context before →
    ValueHasType context before input step.source → CoercionStepValid context step →
    Size.CoercionStep program registry size scope context before step input (.fault failure) after →
    HeapWellTyped context after ∧ HeapTypesExtend before after

def CoercionPathAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context : Context} {before after : Heap} {steps : List SourceInference.CoercionStep}
    {input : Value} {failure : Failure} {sourceType targetType : TypeSystem.Ty},
    SourceRuntimeValid program context scope.source → HeapWellTyped context before →
    ValueHasType context before input sourceType → CoercionPathValid context sourceType targetType steps →
    Size.CoercionPath program registry size scope context before steps input (.fault failure) after →
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

theorem raw_form_value (wellFormed : ProgramWellFormed program)
    {size : Nat} {scope : Scope} {context : Context} {environment : Environment}
    {before after : Heap} {form : ExpressionForm} {requirements : List RequirementId}
    {coercions : List SourceInference.CoercionStep} {value : Value}
    {rawType finalType : TypeSystem.Ty} {plan : ExpressionRequirementPlan}
    (runtime : SourceRuntimeValid program context scope.source) (covers : scope.evidence.Covers context)
    (locals : EnvironmentAgrees before context.locals environment) (heap : HeapWellTyped context before)
    (occurrence : ∃ id node, ContainsExpression scope.source id node ∧ node.form = form ∧ node.rawType = rawType)
    (typed : ExpressionFormHasRawType scope.source context form rawType plan)
    (valid : ExpressionRequirementPlan.Valid context rawType finalType plan requirements coercions)
    (trace : Size.RawForm program registry size scope context environment before form requirements coercions (.value value) after) :
    ValueHasType context after value rawType ∧ HeapWellTyped context after ∧ HeapTypesExtend before after :=
  trace.sound.value_plain.preserved wellFormed runtime covers locals heap occurrence typed valid

theorem coercion_step_value (wellFormed : ProgramWellFormed program)
    {size : Nat} {scope : Scope} {context : Context} {before after : Heap}
    {step : SourceInference.CoercionStep} {input value : Value}
    (runtime : SourceRuntimeValid program context scope.source) (heap : HeapWellTyped context before)
    (typed : ValueHasType context before input step.source) (valid : CoercionStepValid context step)
    (trace : Size.CoercionStep program registry size scope context before step input (.value value) after) :
    ValueHasType context after value step.target ∧ HeapWellTyped context after ∧ HeapTypesExtend before after :=
  trace.sound.value_plain.preserved wellFormed runtime heap typed valid

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
    {coercions : List SourceInference.CoercionStep}
    (atomic : AtomicForm form)
    (trace : ExpressionFormFaults program context scope.evidence scope.source environment before
      form requirements coercions reason after) : after = before := by
  cases atomic <;> cases trace <;> try rfl
  case unit.tuple children => cases children

end Solcore.SourceSemantics.Staging.Recursive.FaultPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.RecursiveFaultPreservationStatements
/-! Faulting statement sequences preserve the heap of every executed prefix.
Typed successful initializers and real allocations precede the strict faulting
child. Lexical context transport returns heap typing to the original caller. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.Staging.Recursive.FaultPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic

variable {program : Program} {registry : Registry}

private theorem expressions_fault_below (wellFormed : ProgramWellFormed program) (budget : Nat)
    (expressionIH : ∀ smaller, smaller < budget → ExpressionAt program registry smaller)
    {size : Nat} (smaller : size < budget) : ExpressionsAt program registry size := by
  intro scope context environment before after ids failure types runtime covers locals heap typed trace
  cases trace with
  | @headFault headSize scope context environment before after id ids failure head =>
      cases typed with
      | cons headTyped _ =>
          exact expressionIH headSize (Nat.lt_trans (Size.child_lt_stepSize (by simp)) smaller)
            runtime covers locals heap headTyped head
  | @tailFault headSize tailSize scope context environment before middle after id ids value failure head tail =>
      cases typed with
      | cons headTyped tailTyped =>
          obtain ⟨_valueTyped, middleTyped, headExtends⟩ := expression_value wellFormed
            runtime covers locals heap headTyped head
          obtain ⟨afterTyped, tailExtends⟩ := expressions_fault_below wellFormed budget expressionIH
            (Nat.lt_trans (Size.child_lt_stepSize (by simp)) smaller)
            runtime covers (locals.mono headExtends) middleTyped tailTyped tail
          exact ⟨afterTyped, headExtends.trans tailExtends⟩
  termination_by size
  decreasing_by simp_all [Size.stepSize] <;> omega

private theorem statement_head_tail
    {source : TypedSource} {control : ControlContext} {context final : Context}
    {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts,
      StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

private theorem statement_form
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

/-- A faulting sequence uses its actual source occurrence, initializer effects
and binder allocation, and the strictly smaller faulting child exactly once. -/
theorem statements_step (wellFormed : ProgramWellFormed program) (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller)
    (whileIH : ∀ smaller, smaller < size → WhileAt program registry smaller)
    (matchIH : ∀ smaller, smaller < size → MatchAt program registry smaller)
    (itemsIH : ∀ smaller, smaller < size → ForItemsAt program registry smaller)
    (loopIH : ∀ smaller, smaller < size → ForLoopAt program registry smaller) :
    StatementsAt program registry size := by
  intro mode scope context staticFinal runtimeFinal environment before after statements failure control facts
    runtime covers locals heap typed trace
  cases trace with
  | @returnFault childSize mode scope context environment before after id rest node expression failure contains form child =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | returnValue expressionTyped =>
          exact expressionIH childSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap expressionTyped child
  | @expressionFault childSize mode scope context environment before after id rest node expression semicolon failure
      contains form child =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | expressionValue expressionTyped | expressionDiscard expressionTyped =>
          exact expressionIH childSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap expressionTyped child
  | @assignBareFault childSize mode scope context environment before after id rest node assignment operator rhs target failure
      contains form _snapshot child =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal _ rhsTyped _ =>
              exact expressionIH childSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap rhsTyped child
          | wordCompound _ _ rhsTyped _ =>
              exact expressionIH childSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap rhsTyped child
  | @assignBareOperands childSize mode scope context environment before after id rest node assignment operator rhs
      target right currentCell initial currentSelected contains form _snapshot child _currentRead _rootType _initialValue _pathRead _invalid =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal _ rhsTyped _ | wordCompound _ _ rhsTyped _ =>
              have post := expression_value wellFormed runtime covers locals heap rhsTyped child
              exact ⟨post.heap_typed, post.heap_extends⟩
  | bitNotBareFault => exact ⟨heap, .refl _⟩
  | @bitNotBare nextSize mode scope context finalContext environment before written after
      id rest node assignment target updated outcome contains form snapshot write next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped⟩ := statement_head_tail typed
      have execution : StatementExecutes program context scope.evidence scope.source environment before id
          context (.fallthrough environment) written :=
        .assignBitNot contains form (.intro (snapshot.resolves _ _ _ _) write)
      have sameContext := execution.final_context_of_typing runtime.graph headTyped
      subst staticMiddle
      have preserved := wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment before written [id]
        (.fallthrough environment) control context context _ runtime covers locals heap
        (.singleton headTyped) (.cons execution .nil)
      obtain ⟨afterTyped, tailExtends⟩ := statementsIH nextSize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono preserved.heap_extends) preserved.heap_typed tailTyped next
      exact ⟨afterTyped, preserved.heap_extends.trans tailExtends⟩
  | assignBareUnbound | assignBareDangling => exact ⟨heap, .refl _⟩
  | @assignBare childSize nextSize mode scope context finalContext environment before middle written after
      id rest node assignment operator rhs value target updated outcome contains form snapshot child write next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped⟩ := statement_head_tail typed
      have execution : StatementExecutes program context scope.evidence scope.source environment before id
          context (.fallthrough environment) written :=
        .assignValue contains form (.intro (snapshot.resolves _ _ _ _) child.sound.value_plain write)
      have sameContext := execution.final_context_of_typing runtime.graph headTyped
      subst staticMiddle
      have preserved :=  wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment before written [id]
        (.fallthrough environment) control context context _ runtime covers locals heap
        (.singleton headTyped) (.cons execution .nil)
      obtain ⟨afterTyped, tailExtends⟩ := statementsIH nextSize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono preserved.heap_extends) preserved.heap_typed tailTyped next
      exact ⟨afterTyped, preserved.heap_extends.trans tailExtends⟩
  | @bitNotProjected keysSize nextSize mode scope context finalContext environment before targetHeap written after assignment values target updated id rest node outcome
      contains form _projected keys snapshot write next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped⟩ := statement_head_tail typed
      have execution : StatementExecutes program context scope.evidence scope.source environment before id
          context (.fallthrough environment) written :=
        .assignBitNot contains form (.intro (snapshot.resolves keys.sound.values_plain) write)
      have sameContext := execution.final_context_of_typing runtime.graph headTyped
      subst staticMiddle
      have preserved := wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment before written [id]
        (.fallthrough environment) control context context _ runtime covers locals heap
        (.singleton headTyped) (.cons execution .nil)
      obtain ⟨afterTyped, tailExtends⟩ := statementsIH nextSize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono preserved.heap_extends) preserved.heap_typed tailTyped next
      exact ⟨afterTyped, preserved.heap_extends.trans tailExtends⟩
  | bitNotProjectedRootFault => exact ⟨heap, .refl _⟩
  | @bitNotProjectedKeysFault keysSize mode scope context environment before after assignment id rest node failure
      contains form _projected _ready keys =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignBitNot assignmentTyped =>
          cases assignmentTyped with
          | intro targetTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := SelectedPreservation.projected_place_keys_typed targetTyped
              exact expressions_fault_below wellFormed _ expressionIH (Size.child_lt_stepSize (by simp))
                runtime covers locals heap keyTyped keys
  | @bitNotProjectedGetterFault keysSize mode scope context environment before after assignment values id rest node reason
      contains form _projected keys _failed =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignBitNot assignmentTyped =>
          cases assignmentTyped with
          | intro targetTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := SelectedPreservation.projected_place_keys_typed targetTyped
              obtain ⟨_keyValues, keyHeap, keyExtends⟩ := expressions_values wellFormed
                runtime covers locals heap keyTyped keys
              exact ⟨keyHeap, keyExtends⟩
  | @assignProjected keysSize childSize nextSize mode scope context finalContext environment before targetHeap middle written after assignment operator rhs values target value updated id rest node outcome
      contains form _projected keys snapshot child write next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped⟩ := statement_head_tail typed
      have execution : StatementExecutes program context scope.evidence scope.source environment before id
          context (.fallthrough environment) written :=
        .assignValue contains form (.intro (snapshot.resolves keys.sound.values_plain) child.sound.value_plain write)
      have sameContext := execution.final_context_of_typing runtime.graph headTyped
      subst staticMiddle
      have preserved := wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment before written [id]
        (.fallthrough environment) control context context _ runtime covers locals heap
        (.singleton headTyped) (.cons execution .nil)
      obtain ⟨afterTyped, tailExtends⟩ := statementsIH nextSize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono preserved.heap_extends) preserved.heap_typed tailTyped next
      exact ⟨afterTyped, preserved.heap_extends.trans tailExtends⟩
  | assignProjectedRootFault => exact ⟨heap, .refl _⟩
  | @assignProjectedKeysFault keysSize mode scope context environment before after assignment operator rhs id rest node failure
      contains form _projected _ready keys =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal targetTyped rhsTyped _ | wordCompound _ targetTyped rhsTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := SelectedPreservation.projected_place_keys_typed targetTyped
              exact expressions_fault_below wellFormed _ expressionIH (Size.child_lt_stepSize (by simp))
                runtime covers locals heap keyTyped keys
  | @assignProjectedGetterFault keysSize mode scope context environment before after assignment operator rhs values id rest node reason
      contains form _projected keys _failed =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal targetTyped rhsTyped _ | wordCompound _ targetTyped rhsTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := SelectedPreservation.projected_place_keys_typed targetTyped
              obtain ⟨_keyValues, keyHeap, keyExtends⟩ := expressions_values wellFormed
                runtime covers locals heap keyTyped keys
              exact ⟨keyHeap, keyExtends⟩
  | @assignProjectedRhsFault keysSize childSize mode scope context environment before targetHeap after assignment operator rhs values target id rest node failure
      contains form _projected keys _snapshot child =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal targetTyped rhsTyped _ | wordCompound _ targetTyped rhsTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := SelectedPreservation.projected_place_keys_typed targetTyped
              obtain ⟨_keyValues, keyHeap, keyExtends⟩ := expressions_values wellFormed
                runtime covers locals heap keyTyped keys
              obtain ⟨afterTyped, rhsExtends⟩ := expressionIH childSize (Size.child_lt_stepSize (by simp))
                runtime covers (locals.mono keyExtends) keyHeap rhsTyped child
              exact ⟨afterTyped, keyExtends.trans rhsExtends⟩
  | @assignProjectedWriteFault keysSize childSize mode scope context environment before targetHeap after assignment operator rhs values target right id rest node reason
      contains form _projected keys _snapshot child _failed =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal targetTyped rhsTyped _ | wordCompound _ targetTyped rhsTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := SelectedPreservation.projected_place_keys_typed targetTyped
              obtain ⟨_keyValues, keyHeap, keyExtends⟩ := expressions_values wellFormed
                runtime covers locals heap keyTyped keys
              have post := expression_value wellFormed runtime covers (locals.mono keyExtends) keyHeap rhsTyped child
              exact ⟨post.heap_typed, keyExtends.trans post.heap_extends⟩
  | @letFault childSize mode scope context environment before after id rest node binder expression failure
      contains form monomorphic child =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | letInitialized expressionTyped _ _ =>
          exact expressionIH childSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap expressionTyped child
      | letInitializedGeneralized polymorphic _ _ _ _ => exact (polymorphic monomorphic).elim
  | @discard childSize nextSize mode scope context finalContext environment before middle after id rest node expression
      value outcome contains form child next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | expressionDiscard expressionTyped =>
          obtain ⟨_valueTyped, middleTyped, headExtends⟩ := expression_value wellFormed
            runtime covers locals heap expressionTyped child
          obtain ⟨afterTyped, tailExtends⟩ := statementsIH nextSize (Size.child_lt_stepSize (by simp))
            runtime covers (locals.mono headExtends) middleTyped tailTyped next
          exact ⟨afterTyped, headExtends.trans tailExtends⟩
  | @discardValue childSize nextSize scope context finalContext environment before middle after id rest node expression
      value outcome contains form child next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | expressionValue expressionTyped =>
          obtain ⟨_valueTyped, middleTyped, headExtends⟩ := expression_value wellFormed
            runtime covers locals heap expressionTyped child
          obtain ⟨afterTyped, tailExtends⟩ := statementsIH nextSize (Size.child_lt_stepSize (by simp))
            runtime covers (locals.mono headExtends) middleTyped tailTyped next
          exact ⟨afterTyped, headExtends.trans tailExtends⟩
  | @ifConditionFault testSize mode scope context environment before after id rest node condition thenBody elseBody failure
      contains form test =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | ifWithoutElse conditionTyped _ | ifWithElse conditionTyped _ _ =>
          exact expressionIH testSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap conditionTyped test
  | @ifFault testSize branchSize mode scope context innerContext environment before middle after
      id rest node condition thenBody elseBody truth failure contains form test branch =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      have conditionTyped : ExpressionHasType scope.source context condition .bool := by
        cases formTyped <;> assumption
      have branchTyped : ∃ final facts, StatementsHaveType scope.source control context
          (if truth then thenBody else elseBody.getD []) final facts := by
        cases formTyped with
        | ifWithoutElse _ yes =>
            cases truth with
            | true => exact ⟨_, _, yes⟩
            | false => exact ⟨_, _, .nil _ _⟩
        | ifWithElse _ yes no =>
            cases truth with
            | true => exact ⟨_, _, yes⟩
            | false => exact ⟨_, _, no⟩
      obtain ⟨branchFinal, branchFacts, branchTyped⟩ := branchTyped
      obtain ⟨_truthTyped, middleTyped, testExtends⟩ := expression_value wellFormed
        runtime covers locals heap conditionTyped test
      obtain ⟨afterTyped, branchExtends⟩ := statementsIH branchSize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono testExtends) middleTyped branchTyped branch
      exact ⟨afterTyped, testExtends.trans branchExtends⟩
  | @ifFallthrough testSize branchSize nextSize mode scope context innerContext finalContext environment innerEnvironment
      before middle branchHeap after id rest node condition thenBody elseBody truth outcome contains form test branch next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped⟩ := statement_head_tail typed
      have execution : StatementExecutes program context scope.evidence scope.source environment before id
          context (.fallthrough environment) branchHeap :=
        StatementsPlain.if_execute contains form test.sound.value_plain branch.sound.fallthrough_scoped
      have sameContext := execution.final_context_of_typing runtime.graph headTyped
      subst staticMiddle
      have preserved := wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment before branchHeap [id]
        (.fallthrough environment) control context context _ runtime covers locals heap
        (.singleton headTyped) (.cons execution .nil)
      obtain ⟨afterTyped, tailExtends⟩ := statementsIH nextSize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono preserved.heap_extends) preserved.heap_typed tailTyped next
      exact ⟨afterTyped, preserved.heap_extends.trans tailExtends⟩
  | @blockFault innerSize mode scope context innerContext environment before after
      id rest node statements failure contains form inner =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | block innerTyped =>
          exact statementsIH innerSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap innerTyped inner
  | @blockFallthrough innerSize nextSize mode scope context innerContext finalContext environment innerEnvironment
      before middle after id rest node statements outcome contains form inner next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped⟩ := statement_head_tail typed
      have execution : StatementExecutes program context scope.evidence scope.source environment before id
          context (.fallthrough environment) middle := .block contains form inner.sound.fallthrough_scoped
      have sameContext := execution.final_context_of_typing runtime.graph headTyped
      subst staticMiddle
      have preserved := wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment before middle [id]
        (.fallthrough environment) control context context _ runtime covers locals heap
        (.singleton headTyped) (.cons execution .nil)
      obtain ⟨afterTyped, tailExtends⟩ := statementsIH nextSize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono preserved.heap_extends) preserved.heap_typed tailTyped next
      exact ⟨afterTyped, preserved.heap_extends.trans tailExtends⟩
  | @matchFault matchSize mode scope context environment before after id rest node resolution failure
      contains form matched =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
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
      exact matchIH matchSize (Size.child_lt_stepSize (by simp))
        runtime covers locals heap scrutineeTyped casesTyped defaults matched rfl
  | @matchFallthrough matchSize nextSize mode scope context finalContext environment before middle after
      id rest node resolution outcome contains form matched next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped⟩ := statement_head_tail typed
      have execution : StatementExecutes program context scope.evidence scope.source environment before id
          context (.fallthrough environment) middle := matched.sound.plain _ _ contains form
      have sameContext := execution.final_context_of_typing runtime.graph headTyped
      subst staticMiddle
      have preserved := wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment before middle [id]
        (.fallthrough environment) control context context _ runtime covers locals heap
        (.singleton headTyped) (.cons execution .nil)
      obtain ⟨afterTyped, tailExtends⟩ := statementsIH nextSize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono preserved.heap_extends) preserved.heap_typed tailTyped next
      exact ⟨afterTyped, preserved.heap_extends.trans tailExtends⟩
  | @whileFault loopSize mode scope context environment before after id rest node condition statements failure
      contains form loop =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | whileLoop conditionTyped bodyTyped =>
          exact whileIH loopSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap conditionTyped bodyTyped loop
  | @whileFallthrough loopSize nextSize mode scope context finalContext environment before middle after
      id rest node condition statements outcome contains form loop next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped⟩ := statement_head_tail typed
      have execution : StatementExecutes program context scope.evidence scope.source environment before id
          context (.fallthrough environment) middle := .whileLoop contains form loop.sound.plain
      have sameContext := execution.final_context_of_typing runtime.graph headTyped
      subst staticMiddle
      have preserved := wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment before middle [id]
        (.fallthrough environment) control context context _ runtime covers locals heap
        (.singleton headTyped) (.cons execution .nil)
      obtain ⟨afterTyped, tailExtends⟩ := statementsIH nextSize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono preserved.heap_extends) preserved.heap_typed tailTyped next
      exact ⟨afterTyped, preserved.heap_extends.trans tailExtends⟩
  | @letUninitialized nextSize mode scope context middleContext finalContext environment before bound after id rest node
      binder location outcome contains form monomorphic extension allocate next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped⟩ := statement_head_tail typed
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
          obtain ⟨afterTyped, tailExtends⟩ := statementsIH nextSize (Size.child_lt_stepSize (by simp))
            (runtime.transport fields) (fields.covers covers) boundEnvironment boundAtMiddle tailTyped next
          exact ⟨afterTyped.transportClosed fields.signatures.symm middleClosed runtime.closed
            (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
            allocationExtends.trans tailExtends⟩
  | @letGeneralized nextSize mode scope context middleContext finalContext environment before snapshotHeap bound
      after id rest node binder initializer captured function location outcome contains form snapshot captures
      polymorphic extension allocated next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | letInitialized _ monomorphic _ => exact (polymorphic monomorphic).elim
      | letInitializedGeneralized _ requirements generalizes initializerTyped staticExtension =>
          have sameContext := Solcore.SourceSemantics.Dynamic.BinderExtends.functional extension staticExtension
          subst staticMiddle
          have functionTyped := captures.wellTyped runtime (snapshot.agrees locals) polymorphic requirements
            generalizes initializerTyped extension
          have allocationExtends :=
            snapshot.metadata_extends.trans (HeapTypesExtend.of_generalized_allocation allocated)
          have boundTyped := (heap.copy snapshot).allocateGeneralized functionTyped allocated
          have boundEnvironment : EnvironmentAgrees bound middleContext.locals ((binder.id, location) :: environment) := by
            cases extension
            exact .cons allocated.reads_new (congrArg (fun retained : TypedBinder => retained.scheme.body) captures.binder_eq)
              (.generalized rfl (congrArg TypedBinder.id captures.binder_eq) (congrArg TypedBinder.scheme captures.binder_eq))
              (locals.mono allocationExtends)
          have fields := RuntimeContextFields.ofBinderExtends extension
          have middleClosed := fields.targetClosed runtime.closed
          have boundAtMiddle := boundTyped.transportClosed fields.signatures runtime.closed middleClosed
            runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)
          obtain ⟨afterTyped, tailExtends⟩ := statementsIH nextSize (Size.child_lt_stepSize (by simp))
            (runtime.transport fields) (fields.covers covers) boundEnvironment boundAtMiddle tailTyped next
          exact ⟨afterTyped.transportClosed fields.signatures.symm middleClosed runtime.closed
            (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
            allocationExtends.trans tailExtends⟩
  | @letInitialized childSize nextSize mode scope context middleContext finalContext environment before middle bound after
      id rest node binder expression value location outcome contains form child monomorphic extension allocate next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | letInitialized expressionTyped _ staticExtension =>
          have sameContext := Solcore.SourceSemantics.Dynamic.BinderExtends.functional extension staticExtension
          subst staticMiddle
          obtain ⟨valueTyped, middleTyped, headExtends⟩ := expression_value wellFormed
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
          obtain ⟨afterTyped, tailExtends⟩ := statementsIH nextSize (Size.child_lt_stepSize (by simp))
            (runtime.transport fields) (fields.covers covers) boundEnvironment boundAtMiddle tailTyped next
          exact ⟨afterTyped.transportClosed fields.signatures.symm middleClosed runtime.closed
            (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
            headExtends.trans (allocationExtends.trans tailExtends)⟩
      | letInitializedGeneralized polymorphic _ _ _ _ => exact (polymorphic monomorphic).elim

  | @forInitializerFault initialSize mode scope context failedContext environment before after id rest node initial condition post body
      failure contains form initialTrace =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | forLoop initialTyped _ _ _ =>
          exact itemsIH initialSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap initialTyped initialTrace
  | @forFault initialSize loopSize mode scope context loopContext environment loopEnvironment before initialized after
      id rest node initial condition post body failure contains form initialTrace loop =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | forLoop initialTyped conditionTyped bodyTyped postTyped =>
          obtain ⟨same, initialHeap, initialExtends, initialLocals⟩ :=
            ForItemsExecute.preserved wellFormed runtime covers locals heap initialTyped initialTrace.sound.plain
          subst loopContext
          have fields := ForItemsHaveType.runtimeContextFields initialTyped
          have loopClosed := fields.targetClosed runtime.closed
          have initialAtLoop := initialHeap.transportClosed fields.signatures runtime.closed loopClosed
            runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)
          obtain ⟨afterTyped, loopExtends⟩ := loopIH loopSize (Size.child_lt_stepSize (by simp))
            (runtime.transport fields) (fields.covers covers) initialLocals initialAtLoop
            conditionTyped bodyTyped postTyped loop
          exact ⟨afterTyped.transportClosed fields.signatures.symm loopClosed runtime.closed
            (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
            initialExtends.trans loopExtends⟩
  | @forFallthrough initialSize loopSize nextSize mode scope context loopContext finalContext environment loopEnvironment
      before initialized middle after id rest node initial condition post body outcome contains form initialTrace loop next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped⟩ := statement_head_tail typed
      have execution : StatementExecutes program context scope.evidence scope.source environment before id
          context (.fallthrough environment) middle := .forLoop contains form initialTrace.sound.plain loop.sound.plain
      have sameContext := execution.final_context_of_typing runtime.graph headTyped
      subst staticMiddle
      have preserved := wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment before middle [id]
        (.fallthrough environment) control context context _ runtime covers locals heap
        (.singleton headTyped) (.cons execution .nil)
      obtain ⟨afterTyped, tailExtends⟩ := statementsIH nextSize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono preserved.heap_extends) preserved.heap_typed tailTyped next
      exact ⟨afterTyped, preserved.heap_extends.trans tailExtends⟩

/-- Each repeated iteration is strictly smaller, and a successful scoped body
returns its actual heap to the original loop context before the next test. -/
theorem while_step (wellFormed : ProgramWellFormed program) (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller)
    (whileIH : ∀ smaller, smaller < size → WhileAt program registry smaller) :
    WhileAt program registry size := by
  intro scope context bodyFinal environment before after condition statements failure control facts
    runtime covers locals heap conditionTyped bodyTyped trace
  cases trace with
  | @conditionFault testSize scope context environment before after condition statements failure test =>
      exact expressionIH testSize (Size.child_lt_stepSize (by simp))
        runtime covers locals heap conditionTyped test
  | @bodyFault testSize bodySize scope context innerContext environment before middle after condition statements failure
      test body =>
      obtain ⟨_truthTyped, middleTyped, testExtends⟩ := expression_value wellFormed
        runtime covers locals heap conditionTyped test
      obtain ⟨afterTyped, bodyExtends⟩ := statementsIH bodySize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono testExtends) middleTyped bodyTyped body
      exact ⟨afterTyped, testExtends.trans bodyExtends⟩
  | @next testSize bodySize nextSize scope context innerContext environment innerEnvironment before middle bodyHeap after
      condition statements outcome test body next =>
      obtain ⟨_truthTyped, middleTyped, testExtends⟩ := expression_value wellFormed
        runtime covers locals heap conditionTyped test
      have preserved := wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment middle bodyHeap statements
        (.fallthrough innerEnvironment) control.enterLoop bodyFinal innerContext _ runtime covers
        (locals.mono testExtends) middleTyped bodyTyped body.sound.fallthrough_scoped
      obtain ⟨afterTyped, nextExtends⟩ := whileIH nextSize (Size.child_lt_stepSize (by simp))
        runtime covers ((locals.mono testExtends).mono preserved.heap_extends) preserved.heap_typed
        conditionTyped bodyTyped next
      exact ⟨afterTyped, testExtends.trans (preserved.heap_extends.trans nextExtends)⟩
  | @continueNext testSize bodySize nextSize scope context innerContext environment innerEnvironment before middle bodyHeap after
      condition statements outcome test body next =>
      obtain ⟨_truthTyped, middleTyped, testExtends⟩ := expression_value wellFormed
        runtime covers locals heap conditionTyped test
      have preserved := wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment middle bodyHeap statements
        (.continuing innerEnvironment) control.enterLoop bodyFinal innerContext _ runtime covers
        (locals.mono testExtends) middleTyped bodyTyped body.sound.continuing_scoped
      obtain ⟨afterTyped, nextExtends⟩ := whileIH nextSize (Size.child_lt_stepSize (by simp))
        runtime covers ((locals.mono testExtends).mono preserved.heap_extends) preserved.heap_typed
        conditionTyped bodyTyped next
      exact ⟨afterTyped, testExtends.trans (preserved.heap_extends.trans nextExtends)⟩

/-- Only the selected arm runs; its real binder frame is restored after a fault. -/
theorem match_step (wellFormed : ProgramWellFormed program) (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller) :
    MatchAt program registry size := by
  intro scope context environment before after resolution outcome failure control type caseFacts
    runtime covers locals heap scrutineeTyped casesTyped defaultTyped trace failed
  cases trace with
  | @scrutineeFault childSize scope context environment before after resolution actualFailure scrutinee =>
      cases BodyOutcome.fault.inj failed
      exact expressionIH childSize (Size.child_lt_stepSize (by simp))
        runtime covers locals heap scrutineeTyped scrutinee
  | @patternFault childSize scope context environment before middle hidden resolution node value location
      contains scrutinee allocated invalid =>
      obtain ⟨valueTyped, middleTyped, firstExtends⟩ := expression_value wellFormed
        runtime covers locals heap scrutineeTyped scrutinee
      obtain ⟨typedNode, typedContains, sameType⟩ := scrutineeTyped.stored_type
      have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
          (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
      subst typedNode
      exact ⟨middleTyped.allocate (.some (sameType ▸ valueTyped)) allocated,
        firstExtends.trans (HeapTypesExtend.of_allocation allocated)⟩
  | @arm childSize bodySize scope context armContext finalContext environment armEnvironment
      before middle hidden bound after resolution node value location statements bindings outcome
      contains scrutinee hiddenAllocated selected extended allocated body =>
      cases outcome with
      | fallthrough => cases failed
      | returned | breaking | continuing => cases failed
      | fault actualFailure =>
        cases BodyOutcome.fault.inj failed
        obtain ⟨valueTyped, middleTyped, firstExtends⟩ := expression_value wellFormed
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
        obtain ⟨afterTyped, bodyExtends⟩ := statementsIH bodySize (Size.child_lt_stepSize (by simp))
          (runtime.transport fields) (fields.covers covers) armLocals boundAtArm armTyped body
        exact ⟨afterTyped.transportClosed fields.signatures.symm armClosed runtime.closed
          (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
          firstExtends.trans (hiddenExtends.trans (boundExtends.trans bodyExtends))⟩
  | @default childSize bodySize scope context finalContext environment before middle hidden after
      resolution node value location statements outcome contains scrutinee hiddenAllocated selected body =>
      cases outcome with
      | fallthrough => cases failed
      | returned | breaking | continuing => cases failed
      | fault actualFailure =>
        cases BodyOutcome.fault.inj failed
        obtain ⟨valueTyped, middleTyped, firstExtends⟩ := expression_value wellFormed
          runtime covers locals heap scrutineeTyped scrutinee
        obtain ⟨typedNode, typedContains, sameType⟩ := scrutineeTyped.stored_type
        have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
          (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
        subst typedNode
        have hiddenTyped := middleTyped.allocate (.some (sameType ▸ valueTyped)) hiddenAllocated
        have hiddenExtends := HeapTypesExtend.of_allocation hiddenAllocated
        obtain ⟨staticFinal, facts, bodyTyped⟩ := defaultTyped statements selected.defaultBody_eq
        obtain ⟨afterTyped, bodyExtends⟩ := statementsIH bodySize (Size.child_lt_stepSize (by simp))
          runtime covers (locals.mono (firstExtends.trans hiddenExtends)) hiddenTyped bodyTyped body
        exact ⟨afterTyped, firstExtends.trans (hiddenExtends.trans bodyExtends)⟩
  | noBranch => cases failed

private theorem for_items_tail (wellFormed : ProgramWellFormed program)
    {size : Nat} (itemsIH : ForItemsAt program registry size)
    {scope : Scope} {control : ControlContext} {context staticMiddle runtimeMiddle staticFinal runtimeFinal : Context}
    {environment middleEnvironment : Dynamic.Environment} {before middle after : Heap}
    {item : ForItemForm} {items : List ForItemForm} {failure : Failure}
    (runtime : SourceRuntimeValid program context scope.source) (covers : scope.evidence.Covers context)
    (locals : EnvironmentAgrees before context.locals environment) (heap : HeapWellTyped context before)
    (headTyped : ForItemHasType scope.source control context item staticMiddle)
    (tailTyped : ForItemsHaveType scope.source control staticMiddle items staticFinal)
    (head : ForItemExecutes program context scope.evidence scope.source environment before item
      runtimeMiddle middleEnvironment middle)
    (next : Size.ForItems program registry size scope runtimeMiddle middleEnvironment middle items runtimeFinal (.fault failure) after) :
    HeapWellTyped context after ∧ HeapTypesExtend before after := by
  obtain ⟨same, middleTyped, headExtends, middleLocals⟩ :=
    ForItemsExecute.preserved wellFormed runtime covers locals heap (.cons headTyped (.nil _ _))
      (.cons head .nil)
  subst runtimeMiddle
  have fields := ForItemHasType.runtimeContextFields headTyped
  have middleClosed := fields.targetClosed runtime.closed
  have heapAtMiddle := middleTyped.transportClosed fields.signatures runtime.closed middleClosed
    runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)
  obtain ⟨afterTyped, tailExtends⟩ := itemsIH (runtime.transport fields) (fields.covers covers)
    middleLocals heapAtMiddle tailTyped next
  exact ⟨afterTyped.transportClosed fields.signatures.symm middleClosed runtime.closed
    (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
    headExtends.trans tailExtends⟩

/-- Successful header effects are erased and preserved independently before
using the strict faulting tail; a failed RHS never invents a write. -/
theorem for_items_step (wellFormed : ProgramWellFormed program) (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (itemsIH : ∀ smaller, smaller < size → ForItemsAt program registry smaller) :
    ForItemsAt program registry size := by
  intro scope context staticFinal runtimeFinal environment before after items failure control
    runtime covers locals heap typed trace
  cases trace with
  | @absent nextSize scope context middleContext finalContext environment before bound after binder rest location outcome
      mono extended allocated next =>
      cases typed with
      | cons headTyped tailTyped =>
        exact for_items_tail wellFormed (itemsIH nextSize (Size.child_lt_stepSize (by simp)))
          runtime covers locals heap headTyped tailTyped (.letUninitialized mono extended allocated) next
  | @initializedGeneralized nextSize scope context middleContext finalContext environment before snapshotHeap
      bound after binder initializer rest captured function location outcome snapshot captures polymorphic extended
      allocated next =>
      cases typed with
      | cons headTyped tailTyped =>
        exact for_items_tail wellFormed (itemsIH nextSize (Size.child_lt_stepSize (by simp)))
          runtime covers locals heap headTyped tailTyped
          (.letInitializedGeneralized snapshot captures polymorphic extended allocated) next
  | @initialized childSize nextSize scope context middleContext finalContext environment before middle bound after
      binder initializer rest value location outcome mono extended child allocated next =>
      cases typed with
      | cons headTyped tailTyped =>
        exact for_items_tail wellFormed (itemsIH nextSize (Size.child_lt_stepSize (by simp)))
          runtime covers locals heap headTyped tailTyped
          (.letInitialized child.sound.value_plain mono extended allocated) next
  | @initializerFault childSize scope context environment before after binder initializer rest failure mono child =>
      cases typed with
      | cons headTyped _ =>
        cases headTyped with
        | letInitialized initializerTyped _ _ _ =>
          exact expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap initializerTyped child
        | letInitializedGeneralized poly _ _ _ _ => exact (poly mono).elim
  | @expression childSize nextSize scope context finalContext environment before middle after expression rest value outcome child next =>
      cases typed with
      | cons headTyped tailTyped =>
        exact for_items_tail wellFormed (itemsIH nextSize (Size.child_lt_stepSize (by simp)))
          runtime covers locals heap headTyped tailTyped (.expression child.sound.value_plain) next
  | @expressionFailure childSize scope context environment before after expression rest failure child =>
      cases typed with
      | cons headTyped _ =>
        cases headTyped with
        | expression expressionTyped =>
          exact expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap expressionTyped child
  | @assignment childSize nextSize scope context finalContext environment before middle written after
      assignment operator rhs value target updated rest outcome snapshot child write next =>
      cases typed with
      | cons headTyped tailTyped =>
        exact for_items_tail wellFormed (itemsIH nextSize (Size.child_lt_stepSize (by simp)))
          runtime covers locals heap headTyped tailTyped
          (.assignValue (.intro (snapshot.resolves _ _ _ _) child.sound.value_plain write)) next
  | @assignmentFailure childSize scope context environment before after assignment operator rhs target rest failure snapshot child =>
      cases typed with
      | cons headTyped _ =>
        cases headTyped with
        | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal _ rhsTyped _ =>
            exact expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap rhsTyped child
          | wordCompound _ _ rhsTyped _ =>
            exact expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap rhsTyped child
  | @assignmentOperands childSize scope context environment before after assignment operator rhs target right
      currentCell initial currentSelected rest _snapshot child _currentRead _rootType _initialValue _pathRead _invalid =>
      cases typed with
      | cons headTyped _ =>
        cases headTyped with
        | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal _ rhsTyped _ | wordCompound _ _ rhsTyped _ =>
            have post := expression_value wellFormed runtime covers locals heap rhsTyped child
            exact ⟨post.heap_typed, post.heap_extends⟩
  | @projectedBitNot keysSize nextSize scope context finalContext environment before targetHeap written after assignment values target updated rest outcome
      _projected keys snapshot write next =>
      cases typed with
      | cons headTyped tailTyped =>
        exact for_items_tail wellFormed (itemsIH nextSize (Size.child_lt_stepSize (by simp)))
          runtime covers locals heap headTyped tailTyped
          (.assignBitNot (.intro (snapshot.resolves keys.sound.values_plain) write)) next
  | projectedBitNotRootFault => exact ⟨heap, .refl _⟩
  | @projectedBitNotKeysFault keysSize scope context environment before after assignment rest failure
      _projected _ready keys =>
      cases typed with
      | cons headTyped _ =>
        cases headTyped with
        | assignBitNot assignmentTyped =>
          cases assignmentTyped with
          | intro targetTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := SelectedPreservation.projected_place_keys_typed targetTyped
              exact expressions_fault_below wellFormed _ expressionIH (Size.child_lt_stepSize (by simp))
                runtime covers locals heap keyTyped keys
  | @projectedBitNotGetterFault keysSize scope context environment before after assignment values rest reason
      _projected keys _failed =>
      cases typed with
      | cons headTyped _ =>
        cases headTyped with
        | assignBitNot assignmentTyped =>
          cases assignmentTyped with
          | intro targetTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := SelectedPreservation.projected_place_keys_typed targetTyped
              obtain ⟨_keyValues, keyHeap, keyExtends⟩ := expressions_values wellFormed
                runtime covers locals heap keyTyped keys
              exact ⟨keyHeap, keyExtends⟩
  | @projectedAssignment keysSize childSize nextSize scope context finalContext environment before targetHeap middle written after assignment operator rhs values target value updated rest outcome
      _projected keys snapshot child write next =>
      cases typed with
      | cons headTyped tailTyped =>
        exact for_items_tail wellFormed (itemsIH nextSize (Size.child_lt_stepSize (by simp)))
          runtime covers locals heap headTyped tailTyped
          (.assignValue (.intro (snapshot.resolves keys.sound.values_plain) child.sound.value_plain write)) next
  | projectedAssignmentRootFault => exact ⟨heap, .refl _⟩
  | @projectedAssignmentKeysFault keysSize scope context environment before after assignment operator rhs rest failure
      _projected _ready keys =>
      cases typed with
      | cons headTyped _ =>
        cases headTyped with
        | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal targetTyped rhsTyped _ | wordCompound _ targetTyped rhsTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := SelectedPreservation.projected_place_keys_typed targetTyped
              exact expressions_fault_below wellFormed _ expressionIH (Size.child_lt_stepSize (by simp))
                runtime covers locals heap keyTyped keys
  | @projectedAssignmentGetterFault keysSize scope context environment before after assignment operator rhs values rest reason
      _projected keys _failed =>
      cases typed with
      | cons headTyped _ =>
        cases headTyped with
        | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal targetTyped rhsTyped _ | wordCompound _ targetTyped rhsTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := SelectedPreservation.projected_place_keys_typed targetTyped
              obtain ⟨_keyValues, keyHeap, keyExtends⟩ := expressions_values wellFormed
                runtime covers locals heap keyTyped keys
              exact ⟨keyHeap, keyExtends⟩
  | @projectedAssignmentRhsFault keysSize childSize scope context environment before targetHeap after assignment operator rhs values target rest failure
      _projected keys _snapshot child =>
      cases typed with
      | cons headTyped _ =>
        cases headTyped with
        | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal targetTyped rhsTyped _ | wordCompound _ targetTyped rhsTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := SelectedPreservation.projected_place_keys_typed targetTyped
              obtain ⟨_keyValues, keyHeap, keyExtends⟩ := expressions_values wellFormed
                runtime covers locals heap keyTyped keys
              obtain ⟨afterTyped, rhsExtends⟩ := expressionIH childSize (Size.child_lt_stepSize (by simp))
                runtime covers (locals.mono keyExtends) keyHeap rhsTyped child
              exact ⟨afterTyped, keyExtends.trans rhsExtends⟩
  | @projectedAssignmentWriteFault keysSize childSize scope context environment before targetHeap after assignment operator rhs values target right rest reason
      _projected keys _snapshot child _failed =>
      cases typed with
      | cons headTyped _ =>
        cases headTyped with
        | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal targetTyped rhsTyped _ | wordCompound _ targetTyped rhsTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := SelectedPreservation.projected_place_keys_typed targetTyped
              obtain ⟨_keyValues, keyHeap, keyExtends⟩ := expressions_values wellFormed
                runtime covers locals heap keyTyped keys
              have post := expression_value wellFormed runtime covers (locals.mono keyExtends) keyHeap rhsTyped child
              exact ⟨post.heap_typed, keyExtends.trans post.heap_extends⟩
  | bitNotFault => exact ⟨heap, .refl _⟩
  | @bitNot nextSize scope context finalContext environment before written after assignment target updated rest outcome
      snapshot write next =>
      cases typed with
      | cons headTyped tailTyped =>
        exact for_items_tail wellFormed (itemsIH nextSize (Size.child_lt_stepSize (by simp)))
          runtime covers locals heap headTyped tailTyped
          (.assignBitNot (.intro (snapshot.resolves _ _ _ _) write)) next
  | unbound | dangling => exact ⟨heap, .refl _⟩

/-- Finite for faults keep every condition, body, and post-header prefix. -/
theorem for_loop_step (wellFormed : ProgramWellFormed program) (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller)
    (itemsIH : ∀ smaller, smaller < size → ForItemsAt program registry smaller)
    (loopIH : ∀ smaller, smaller < size → ForLoopAt program registry smaller) :
    ForLoopAt program registry size := by
  intro scope context bodyFinal postFinal environment before after condition post body failure control facts
    runtime covers locals heap conditionTyped bodyTyped postTyped trace
  cases trace with
  | @testFault testSize scope context environment before after condition post body failure test =>
      exact expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
  | @bodyFailure testSize branchSize scope context innerContext environment before middle after condition post body failure
      test branch =>
      obtain ⟨_truthTyped, middleTyped, testExtends⟩ := expression_value wellFormed
        runtime covers locals heap conditionTyped test
      obtain ⟨afterTyped, branchExtends⟩ := statementsIH branchSize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono testExtends) middleTyped bodyTyped branch
      exact ⟨afterTyped, testExtends.trans branchExtends⟩
  | @postFailure testSize branchSize postTraceSize scope context innerContext postContext environment innerEnvironment
      before middle bodyHeap after condition post body failure test branch postTrace =>
      obtain ⟨_truthTyped, middleTyped, testExtends⟩ := expression_value wellFormed
        runtime covers locals heap conditionTyped test
      have preserved := wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment middle bodyHeap body
        (.fallthrough innerEnvironment) control.enterLoop bodyFinal innerContext _ runtime covers
        (locals.mono testExtends) middleTyped bodyTyped branch.sound.fallthrough_scoped
      obtain ⟨afterTyped, postExtends⟩ := itemsIH postTraceSize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono (testExtends.trans preserved.heap_extends)) preserved.heap_typed postTyped postTrace
      exact ⟨afterTyped, testExtends.trans (preserved.heap_extends.trans postExtends)⟩
  | @continuePostFailure testSize branchSize postTraceSize scope context innerContext postContext environment innerEnvironment
      before middle bodyHeap after condition post body failure test branch postTrace =>
      obtain ⟨_truthTyped, middleTyped, testExtends⟩ := expression_value wellFormed
        runtime covers locals heap conditionTyped test
      have preserved := wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment middle bodyHeap body
        (.continuing innerEnvironment) control.enterLoop bodyFinal innerContext _ runtime covers
        (locals.mono testExtends) middleTyped bodyTyped branch.sound.continuing_scoped
      obtain ⟨afterTyped, postExtends⟩ := itemsIH postTraceSize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono (testExtends.trans preserved.heap_extends)) preserved.heap_typed postTyped postTrace
      exact ⟨afterTyped, testExtends.trans (preserved.heap_extends.trans postExtends)⟩
  | @iterate testSize branchSize postTraceSize nextSize scope context innerContext postContext environment innerEnvironment postEnvironment
      before middle bodyHeap postHeap after condition post body outcome test branch postTrace next =>
      obtain ⟨_truthTyped, middleTyped, testExtends⟩ := expression_value wellFormed
        runtime covers locals heap conditionTyped test
      have preserved := wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment middle bodyHeap body
        (.fallthrough innerEnvironment) control.enterLoop bodyFinal innerContext _ runtime covers
        (locals.mono testExtends) middleTyped bodyTyped branch.sound.fallthrough_scoped
      obtain ⟨_postContext, postHeapTyped, postExtends, _postLocals⟩ :=
        ForItemsExecute.preserved wellFormed runtime covers
          (locals.mono (testExtends.trans preserved.heap_extends)) preserved.heap_typed postTyped postTrace.sound.plain
      obtain ⟨afterTyped, nextExtends⟩ := loopIH nextSize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono (testExtends.trans (preserved.heap_extends.trans postExtends)))
        postHeapTyped conditionTyped bodyTyped postTyped next
      exact ⟨afterTyped, testExtends.trans (preserved.heap_extends.trans (postExtends.trans nextExtends))⟩
  | @continueIterate testSize branchSize postTraceSize nextSize scope context innerContext postContext environment innerEnvironment postEnvironment
      before middle bodyHeap postHeap after condition post body outcome test branch postTrace next =>
      obtain ⟨_truthTyped, middleTyped, testExtends⟩ := expression_value wellFormed
        runtime covers locals heap conditionTyped test
      have preserved := wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment middle bodyHeap body
        (.continuing innerEnvironment) control.enterLoop bodyFinal innerContext _ runtime covers
        (locals.mono testExtends) middleTyped bodyTyped branch.sound.continuing_scoped
      obtain ⟨_postContext, postHeapTyped, postExtends, _postLocals⟩ :=
        ForItemsExecute.preserved wellFormed runtime covers
          (locals.mono (testExtends.trans preserved.heap_extends)) preserved.heap_typed postTyped postTrace.sound.plain
      obtain ⟨afterTyped, nextExtends⟩ := loopIH nextSize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono (testExtends.trans (preserved.heap_extends.trans postExtends)))
        postHeapTyped conditionTyped bodyTyped postTyped next
      exact ⟨afterTyped, testExtends.trans (preserved.heap_extends.trans (postExtends.trans nextExtends))⟩

end Solcore.SourceSemantics.Staging.Recursive.FaultPreservation
end
