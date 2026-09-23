import Solcore.SourceSemantics.Dynamic.PatternCompletenessProperties
import Solcore.SourceSemantics.Dynamic.StaticControlProperties

/-!
Typing-sensitive control facts for source dynamics.

This module keeps branch-selection and control-summary reasoning below the
whole-language preservation proof.  It provides the exact bridges needed to
relate an executed match arm to its static body facts and to transport an
ordinary path through merged branch summaries.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Dynamic

open Frontend
open Frontend.SourceInference
open TypeSystem

namespace ControlSummary

theorem sequence_canFallthrough
    {head tail : ControlSummary}
    (head_falls : head.canFallthrough = true)
    (tail_falls : tail.canFallthrough = true) :
    (head.sequence tail).canFallthrough = true := by
  have head_some : head.fallthrough.isSome = true := by
    simpa [ControlSummary.canFallthrough] using head_falls
  simpa [ControlSummary.sequence, ControlSummary.canFallthrough, head_some]
    using tail_falls

theorem branches_canFallthrough_left
    {left right : ControlSummary}
    (falls : left.canFallthrough = true) :
    (left.branches right).canFallthrough = true := by
  have some : left.fallthrough.isSome = true := by
    simpa [ControlSummary.canFallthrough] using falls
  simp [ControlSummary.branches, ControlSummary.canFallthrough, some]

theorem branches_canFallthrough_right
    {left right : ControlSummary}
    (falls : right.canFallthrough = true) :
    (left.branches right).canFallthrough = true := by
  have some : right.fallthrough.isSome = true := by
    simpa [ControlSummary.canFallthrough] using falls
  simp [ControlSummary.branches, ControlSummary.canFallthrough, some]

theorem eraseValue_canFallthrough
    {summary : ControlSummary}
    (falls : summary.canFallthrough = true) :
    summary.eraseValue.canFallthrough = true := by
  cases summary with
  | mk fallthrough mayReturn mayBreak mayContinue =>
      cases fallthrough <;>
        simp_all [ControlSummary.canFallthrough, ControlSummary.eraseValue]

end ControlSummary

namespace MergeBodyControls

private theorem some_of_mem
    {facts : List BodyFacts} {fallback : Option BodyFacts}
    {selected : BodyFacts} (member : selected ∈ facts) :
    ∃ summary, mergeBodyControls facts fallback = some summary := by
  induction facts with
  | nil => simp at member
  | cons head tail induction =>
      cases tail_merged : mergeBodyControls tail fallback with
      | none => exact ⟨head.control, by simp [mergeBodyControls, tail_merged]⟩
      | some tailSummary =>
          exact ⟨head.control.branches tailSummary,
            by simp [mergeBodyControls, tail_merged]⟩

/-- Any branch which can complete ordinarily makes a successful merged match
summary ordinarily completable as well. -/
theorem canFallthrough_of_mem
    {facts : List BodyFacts} {fallback : Option BodyFacts}
    {summary : ControlSummary} {selected : BodyFacts}
    (merged : mergeBodyControls facts fallback = some summary)
    (member : selected ∈ facts)
    (falls : selected.control.canFallthrough = true) :
    summary.canFallthrough = true := by
  induction facts generalizing summary with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.mem_cons] at member
      cases tail_merged : mergeBodyControls tail fallback with
      | none =>
          simp only [mergeBodyControls, tail_merged, Option.some.injEq] at merged
          subst summary
          rcases member with rfl | member
          · exact falls
          · rcases some_of_mem member with ⟨tailSummary, tail_eq⟩
            rw [tail_eq] at tail_merged
            contradiction
      | some tailSummary =>
          simp only [mergeBodyControls, tail_merged, Option.some.injEq] at merged
          subst summary
          rcases member with rfl | member
          · exact ControlSummary.branches_canFallthrough_left falls
          · exact ControlSummary.branches_canFallthrough_right
              (induction tail_merged member)

theorem canFallthrough_of_fallback
    {facts : List BodyFacts} {summary : ControlSummary}
    {fallbackFacts : BodyFacts}
    (merged : mergeBodyControls facts (some fallbackFacts) = some summary)
    (falls : fallbackFacts.control.canFallthrough = true) :
    summary.canFallthrough = true := by
  have merge_some : ∀ bodies : List BodyFacts,
      ∃ merged,
        mergeBodyControls bodies (some fallbackFacts) = some merged := by
    intro bodies
    induction bodies with
    | nil => exact ⟨fallbackFacts.control, rfl⟩
    | cons head tail induction =>
        rcases induction with ⟨tailSummary, tail_eq⟩
        exact ⟨head.control.branches tailSummary, by
          simp [mergeBodyControls, tail_eq]⟩
  induction facts generalizing summary with
  | nil =>
      simp only [mergeBodyControls, Option.some.injEq] at merged
      subst summary
      exact falls
  | cons head tail induction =>
      cases tail_merged : mergeBodyControls tail (some fallbackFacts) with
      | none =>
          rcases merge_some tail with ⟨tailSummary, tail_eq⟩
          rw [tail_eq] at tail_merged
          contradiction
      | some tailSummary =>
          simp only [mergeBodyControls, tail_merged, Option.some.injEq] at merged
          subst summary
          exact ControlSummary.branches_canFallthrough_right
            (induction tail_merged)

end MergeBodyControls

namespace MatchCasesSelect

theorem defaultBody_eq
    {context : Context} {value : Value} {cases : List TypedMatchCase}
    {fallback : Option (List StatementId)} {body : List StatementId}
    (selected : MatchCasesSelect context value cases fallback (.default body)) :
    fallback = some body := by
  induction cases generalizing fallback with
  | nil =>
      cases selected
      rfl
  | cons head tail induction =>
      cases selected with
      | tail does_not_match tail_selected => exact induction tail_selected

theorem noBranch_defaultBody_eq
    {context : Context} {value : Value} {cases : List TypedMatchCase}
    {fallback : Option (List StatementId)}
    (selected : MatchCasesSelect context value cases fallback .noBranch) :
    fallback = none := by
  induction cases generalizing fallback with
  | nil =>
      cases selected
      rfl
  | cons head tail induction =>
      cases selected with
      | tail does_not_match tail_selected => exact induction tail_selected

/-- Selection of an explicit arm identifies its static body facts at the same
source-list position. -/
theorem arm_body_typed
    {source : TypedSource} {control : ControlContext} {context : Context}
    {scrutineeType : Ty} {cases : List TypedMatchCase}
    {caseFacts : List BodyFacts} {fallback : Option (List StatementId)}
    {value : Value} {body : List StatementId}
    {bindings : List (TypedBinder × Value)}
    (cases_typed : MatchCasesHaveType source control context scrutineeType cases
      caseFacts)
    (selected : MatchCasesSelect context value cases fallback
      (.arm body bindings)) :
    ∃ facts armContext finalContext,
      facts ∈ caseFacts ∧
      StatementsHaveType source control armContext body finalContext facts := by
  cases selected with
  | head matched =>
      cases cases_typed with
      | cons head_type tail_type =>
          cases head_type with
          | intro pattern_type binders_extend body_type =>
              exact ⟨_, _, _, by simp, body_type⟩
  | tail does_not_match tail_selected =>
      cases cases_typed with
      | cons head_type tail_type =>
          rcases MatchCasesSelect.arm_body_typed tail_type tail_selected with
            ⟨facts, armContext, finalContext, member, body_type⟩
          exact ⟨facts, armContext, finalContext,
            List.mem_cons_of_mem _ member, body_type⟩
termination_by cases.length
decreasing_by simp_all

end MatchCasesSelect

namespace ControlOutcome

/-- Positive evidence that a dynamic control result is ordinary.  Keeping
this as an indexed proposition makes it possible to invert scoped
`restoreControl` results without dependent-elimination problems. -/
inductive IsFallthrough : ControlOutcome → Prop where
  | intro (environment : Environment) : IsFallthrough (.fallthrough environment)

namespace IsFallthrough

theorem of_restore {outer : Environment} {outcome : ControlOutcome}
    (falls : IsFallthrough (restoreControl outer outcome)) :
    IsFallthrough outcome := by
  cases outcome <;> cases falls
  exact .intro _

theorem of_eq {outcome : ControlOutcome} {environment : Environment}
    (equal : outcome = .fallthrough environment) : IsFallthrough outcome := by
  subst outcome
  exact .intro _

theorem exists_eq {outcome : ControlOutcome}
    (falls : IsFallthrough outcome) :
    ∃ environment, outcome = .fallthrough environment := by
  cases falls with
  | intro environment => exact ⟨environment, rfl⟩

end IsFallthrough

/-- Inverting ordinary completion through a scoped statement recovers an
ordinary completion of the nested execution. -/
theorem fallthrough_of_restore_eq
    {outer : Environment} {outcome : ControlOutcome}
    {finalEnvironment : Environment}
    (equal : restoreControl outer outcome =
      .fallthrough finalEnvironment) :
    ∃ innerEnvironment, outcome = .fallthrough innerEnvironment := by
  cases outcome <;> simp [restoreControl] at equal
  exact ⟨_, rfl⟩

end ControlOutcome

namespace TerminalControl

/-- A terminal result can never be an ordinary fallthrough. -/
theorem not_fallthrough
    {outcome : ControlOutcome} {environment : Environment}
    (terminal : TerminalControl outcome)
    (equal : outcome = .fallthrough environment) : False := by
  subst outcome
  cases terminal

end TerminalControl

/-- The static data needed by control soundness, separated from the stronger
whole-program runtime certificate to avoid a preservation-module cycle. -/
structure ControlRuntimeValid (context : Context) (source : TypedSource) : Prop where
  catalog : SignatureCatalogWellFormed context.signatures
  graph : OccurrenceGraphWellFormed source
  owner : context.currentDeclaration = some source.owner
  closed : context.typeParameters = []

/-- Expression preservation callback used only to type a selected match
scrutinee and to carry the heap invariant across condition evaluation. -/
def ExpressionControlPreserves
    (program : Program) (evidence : EvidenceEnvironment)
    (source : TypedSource) : Prop :=
  ∀ context environment before after expression value type,
    ControlRuntimeValid context source →
    evidence.Covers context →
    EnvironmentAgrees before context.locals environment →
    HeapWellTyped context before →
    ExpressionHasType source context expression type →
    ExpressionEvaluates program context evidence source environment before
      expression value after →
    ValueHasType context after value type ∧
      HeapWellTyped context after ∧ HeapTypesExtend before after

/-- State component of statement preservation needed while the separate
control proof advances through an ordinary statement sequence. -/
def StatementFallthroughStatePreserves
    (program : Program) (evidence : EvidenceEnvironment)
    (source : TypedSource) : Prop :=
  ∀ control context environment before statement staticFinalContext
      runtimeFinalContext finalEnvironment after facts,
    ControlRuntimeValid context source →
    evidence.Covers context →
    EnvironmentAgrees before context.locals environment →
    HeapWellTyped context before →
    StatementHasType source control context statement staticFinalContext facts →
    StatementExecutes program context evidence source environment before
      statement runtimeFinalContext (.fallthrough finalEnvironment) after →
    runtimeFinalContext = staticFinalContext ∧
      HeapWellTyped context after ∧ HeapTypesExtend before after ∧
      EnvironmentAgrees after staticFinalContext.locals finalEnvironment

/-- Form-indexed static control information, retaining exactly the nested
typing data needed to justify a dynamically observed fallthrough. -/
inductive StatementControlFormTyping
    (source : TypedSource) (control : ControlContext) (context : Context) :
    StatementForm → StatementFacts → Prop where
  | letUninitialized {binder} :
      StatementControlFormTyping source control context (.letDecl binder none) {
        type := .unit, hasValue := false, sawReturn := false
        control := .ordinary .unit
      }
  | letInitialized {binder initializer} :
      StatementControlFormTyping source control context
        (.letDecl binder (some initializer)) {
          type := .unit, hasValue := false, sawReturn := false
          control := .ordinary .unit
        }
  | returnUnit :
      StatementControlFormTyping source control context (.returnStmt none) {
        type := control.returnType, hasValue := true, sawReturn := true
        control := .returned
      }
  | returnValue {value} :
      StatementControlFormTyping source control context
        (.returnStmt (some value)) {
          type := control.returnType, hasValue := true, sawReturn := true
          control := .returned
        }
  | expressionValue {expression type}
      (expression_type : ExpressionHasType source context expression type) :
      StatementControlFormTyping source control context
        (.expression expression false) {
          type, hasValue := true, sawReturn := false
          control := .ordinary type
        }
  | expressionDiscard {expression type}
      (expression_type : ExpressionHasType source context expression type) :
      StatementControlFormTyping source control context
        (.expression expression true) {
          type := .unit, hasValue := false, sawReturn := false
          control := .ordinary .unit
        }
  | assignValue {assignment operator value} :
      StatementControlFormTyping source control context
        (.assignValue assignment operator value) {
          type := .unit, hasValue := false, sawReturn := false
          control := .ordinary .unit
        }
  | assignBitNot {assignment} :
      StatementControlFormTyping source control context
        (.assignBitNot assignment) {
          type := .unit, hasValue := false, sawReturn := false
          control := .ordinary .unit
        }
  | ifWithoutElse {condition thenBody thenFinal thenFacts}
      (condition_type : ExpressionHasType source context condition .bool)
      (then_type : StatementsHaveType source control context thenBody thenFinal
        thenFacts) :
      StatementControlFormTyping source control context
        (.ifThen condition thenBody none) {
          type := .unit, hasValue := false, sawReturn := false
          control := thenFacts.control.branches (.ordinary .unit)
        }
  | ifWithElse {condition thenBody elseBody thenFinal elseFinal thenFacts
      elseFacts}
      (condition_type : ExpressionHasType source context condition .bool)
      (then_type : StatementsHaveType source control context thenBody thenFinal
        thenFacts)
      (else_type : StatementsHaveType source control context elseBody elseFinal
        elseFacts) :
      StatementControlFormTyping source control context
        (.ifThen condition thenBody (some elseBody)) {
          type := if thenFacts.sawReturn && elseFacts.sawReturn
            then control.returnType else .unit
          hasValue := thenFacts.sawReturn && elseFacts.sawReturn
          sawReturn := thenFacts.sawReturn && elseFacts.sawReturn
          control := thenFacts.control.branches elseFacts.control
        }
  | block {body innerFinal bodyFacts}
      (body_type : StatementsHaveType source control context body innerFinal
        bodyFacts) :
      StatementControlFormTyping source control context (.block body) {
        type := bodyFacts.type
        hasValue := bodyFacts.sawReturn
        sawReturn := bodyFacts.sawReturn
        control := bodyFacts.control.eraseValue
      }
  | matchWithoutDefault {resolution scrutineeType caseFacts summary}
      (default_eq : resolution.defaultBody = none)
      (scrutinee_type : ExpressionHasType source context resolution.scrutinee
        scrutineeType)
      (cases_type : MatchCasesHaveType source control context scrutineeType
        resolution.cases caseFacts)
      (exhaustive : MatchExhaustive context scrutineeType resolution.cases none)
      (merged : mergeBodyControls caseFacts none = some summary) :
      StatementControlFormTyping source control context (.matchWith resolution) {
        type := if allBodiesSawReturn caseFacts then control.returnType else .unit
        hasValue := allBodiesSawReturn caseFacts
        sawReturn := allBodiesSawReturn caseFacts
        control := summary.eraseValue
      }
  | matchWithDefault {resolution defaultBody scrutineeType caseFacts
      defaultFinal defaultFacts summary}
      (default_eq : resolution.defaultBody = some defaultBody)
      (scrutinee_type : ExpressionHasType source context resolution.scrutinee
        scrutineeType)
      (cases_type : MatchCasesHaveType source control context scrutineeType
        resolution.cases caseFacts)
      (default_type : StatementsHaveType source control context defaultBody
        defaultFinal defaultFacts)
      (merged : mergeBodyControls caseFacts (some defaultFacts) = some summary) :
      StatementControlFormTyping source control context (.matchWith resolution) {
        type := if allBodiesSawReturn caseFacts && defaultFacts.sawReturn
          then control.returnType else .unit
        hasValue := allBodiesSawReturn caseFacts && defaultFacts.sawReturn
        sawReturn := allBodiesSawReturn caseFacts && defaultFacts.sawReturn
        control := summary.eraseValue
      }
  | forLoop {initializer condition post body} {bodyFacts : BodyFacts} :
      StatementControlFormTyping source control context
        (.forLoop initializer condition post body) {
          type := .unit, hasValue := false, sawReturn := false
          control := .loop bodyFacts.control
        }
  | whileLoop {condition body} {bodyFacts : BodyFacts} :
      StatementControlFormTyping source control context
        (.whileLoop condition body) {
          type := .unit, hasValue := false, sawReturn := false
          control := .loop bodyFacts.control
        }
  | breakStmt :
      StatementControlFormTyping source control context .breakStmt {
        type := .unit, hasValue := false, sawReturn := false
        control := .breaking
      }
  | continueStmt :
      StatementControlFormTyping source control context .continueStmt {
        type := .unit, hasValue := false, sawReturn := false
        control := .continuing
      }

namespace StatementHasType

theorem controlFormTyping
    {source : TypedSource} {control : ControlContext}
    {context finalContext : Context} {statement : StatementId}
    {facts : StatementFacts}
    (typing : StatementHasType source control context statement finalContext
      facts) :
    ∃ node, ContainsStatement source statement node ∧
      StatementControlFormTyping source control context node.form facts := by
  cases typing with
  | letUninitialized contains form_eq monomorphic extension type_eq =>
      exact ⟨_, contains, form_eq ▸ .letUninitialized⟩
  | letInitialized contains form_eq initializer_type monomorphic extension type_eq =>
      exact ⟨_, contains, form_eq ▸ .letInitialized⟩
  | returnUnit contains form_eq return_type_eq type_eq =>
      exact ⟨_, contains, form_eq ▸ .returnUnit⟩
  | returnValue contains form_eq value_type type_eq =>
      exact ⟨_, contains, form_eq ▸ .returnValue⟩
  | expressionValue contains form_eq expression_type type_eq =>
      exact ⟨_, contains, form_eq ▸ .expressionValue expression_type⟩
  | expressionDiscard contains form_eq expression_type type_eq =>
      exact ⟨_, contains, form_eq ▸ .expressionDiscard expression_type⟩
  | assignValue contains form_eq assignment_type type_eq =>
      exact ⟨_, contains, form_eq ▸ .assignValue⟩
  | assignBitNot contains form_eq assignment_type type_eq =>
      exact ⟨_, contains, form_eq ▸ .assignBitNot⟩
  | ifWithoutElse contains form_eq condition_type then_type type_eq =>
      exact ⟨_, contains, form_eq ▸ .ifWithoutElse condition_type then_type⟩
  | ifWithElse contains form_eq condition_type then_type else_type type_eq =>
      exact ⟨_, contains,
        form_eq ▸ .ifWithElse condition_type then_type else_type⟩
  | block contains form_eq body_type type_eq =>
      exact ⟨_, contains, form_eq ▸ .block body_type⟩
  | matchWithoutDefault contains form_eq default_eq scrutinee_type cases_type
      requirements_eq exhaustive merged type_eq =>
      exact ⟨_, contains, form_eq ▸ .matchWithoutDefault default_eq
        scrutinee_type cases_type exhaustive merged⟩
  | matchWithDefault contains form_eq default_eq scrutinee_type cases_type
      default_type requirements_eq merged type_eq =>
      exact ⟨_, contains, form_eq ▸ .matchWithDefault default_eq
        scrutinee_type cases_type default_type merged⟩
  | forLoop contains form_eq initializer_type condition_type body_type post_type
      type_eq =>
      exact ⟨_, contains, form_eq ▸ .forLoop⟩
  | whileLoop contains form_eq condition_type body_type type_eq =>
      exact ⟨_, contains, form_eq ▸ .whileLoop⟩
  | breakStmt contains form_eq allowed type_eq =>
      exact ⟨_, contains, form_eq ▸ .breakStmt⟩
  | continueStmt contains form_eq allowed type_eq =>
      exact ⟨_, contains, form_eq ▸ .continueStmt⟩

/-- The only lexical effect of one typed statement is the binder introduced
by a `let`; all other forms leave the context unchanged. -/
theorem controlBindersExtend
    {source : TypedSource} {control : ControlContext}
    {context finalContext : Context} {statement : StatementId}
    {facts : StatementFacts}
    (typing : StatementHasType source control context statement finalContext
      facts) :
    ∃ binders, BindersExtend source.owner context binders finalContext := by
  cases typing with
  | letUninitialized contains form_eq monomorphic extension type_eq =>
      exact ⟨[_], .cons extension (.nil _)⟩
  | letInitialized contains form_eq initializer_type monomorphic extension
      type_eq =>
      exact ⟨[_], .cons extension (.nil _)⟩
  | returnUnit | returnValue | expressionValue | expressionDiscard |
      assignValue | assignBitNot | ifWithoutElse | ifWithElse | block |
      matchWithoutDefault | matchWithDefault | forLoop | whileLoop |
      breakStmt | continueStmt =>
      exact ⟨[], .nil _⟩

end StatementHasType

namespace BindersExtend

theorem control_functional
    {owner : Resolved.DeclarationId} {context left right : Context}
    {binders : List TypedBinder}
    (left_extension : BindersExtend owner context binders left)
    (right_extension : BindersExtend owner context binders right) :
    left = right := by
  induction left_extension generalizing right with
  | nil =>
      cases right_extension
      rfl
  | cons left_head left_tail induction =>
      cases right_extension with
      | cons right_head right_tail =>
          cases left_head
          cases right_head
          exact induction right_tail

theorem control_signatures
    {owner : Resolved.DeclarationId} {source target : Context}
    {binders : List TypedBinder}
    (extension : BindersExtend owner source binders target) :
    target.signatures = source.signatures := by
  induction extension with
  | nil => rfl
  | cons head tail induction =>
      exact induction.trans head.context_fields.1

theorem control_currentDeclaration
    {owner : Resolved.DeclarationId} {source target : Context}
    {binders : List TypedBinder}
    (extension : BindersExtend owner source binders target) :
    target.currentDeclaration = source.currentDeclaration := by
  induction extension with
  | nil => rfl
  | cons head tail induction =>
      exact induction.trans head.context_fields.2.1

theorem control_typeParameters
    {owner : Resolved.DeclarationId} {source target : Context}
    {binders : List TypedBinder}
    (extension : BindersExtend owner source binders target) :
    target.typeParameters = source.typeParameters := by
  induction extension with
  | nil => rfl
  | cons head tail induction =>
      exact induction.trans head.context_fields.2.2.1

theorem control_assumptions
    {owner : Resolved.DeclarationId} {source target : Context}
    {binders : List TypedBinder}
    (extension : BindersExtend owner source binders target) :
    target.assumptions = source.assumptions := by
  induction extension with
  | nil => rfl
  | cons head tail induction =>
      exact induction.trans head.context_fields.2.2.2.1

theorem control_heap_forward
    {owner : Resolved.DeclarationId} {source target : Context}
    {binders : List TypedBinder} {heap : Heap}
    (extension : BindersExtend owner source binders target)
    (typed : HeapWellTyped source heap) : HeapWellTyped target heap := by
  induction extension with
  | nil => exact typed
  | cons head tail induction =>
      exact induction ((HeapWellTyped.iff_of_binderExtends head).mp typed)

theorem control_heap_backward
    {owner : Resolved.DeclarationId} {source target : Context}
    {binders : List TypedBinder} {heap : Heap}
    (extension : BindersExtend owner source binders target)
    (typed : HeapWellTyped target heap) : HeapWellTyped source heap := by
  induction extension with
  | nil => exact typed
  | cons head tail induction =>
      exact (HeapWellTyped.iff_of_binderExtends head).mpr (induction typed)

end BindersExtend

namespace BindingValuesHaveTypes

theorem control_unzip
    {context : Context} {heap : Heap}
    {bindings : List (TypedBinder × Value)}
    (typed : BindingValuesHaveTypes context heap bindings) :
    ValuesHaveTypes context heap (bindings.map Prod.snd)
      (bindings.map fun binding => binding.1.scheme.body) := by
  induction typed with
  | nil => exact .nil
  | cons head tail induction => exact .cons head induction

end BindingValuesHaveTypes

namespace ControlRuntimeValid

theorem transportBinders
    {sourceContext targetContext : Context} {source : TypedSource}
    {binders : List TypedBinder}
    (valid : ControlRuntimeValid sourceContext source)
    (extension : BindersExtend source.owner sourceContext binders targetContext) :
    ControlRuntimeValid targetContext source := {
  catalog := by
    rw [Solcore.SourceSemantics.Dynamic.BindersExtend.control_signatures
      extension]
    exact valid.catalog
  graph := valid.graph
  owner :=
    (Solcore.SourceSemantics.Dynamic.BindersExtend.control_currentDeclaration
      extension).trans valid.owner
  closed :=
    (Solcore.SourceSemantics.Dynamic.BindersExtend.control_typeParameters
      extension).trans valid.closed
}

end ControlRuntimeValid

namespace EvidenceEnvironment.Covers

theorem transportBinders
    {environment : EvidenceEnvironment}
    {owner : Resolved.DeclarationId} {source target : Context}
    {binders : List TypedBinder}
    (covers : environment.Covers source)
    (extension : BindersExtend owner source binders target) :
    environment.Covers target := by
  rcases covers with ⟨valid, supplies⟩
  constructor
  · rw [Solcore.SourceSemantics.Dynamic.BindersExtend.control_signatures
      extension]
    exact valid
  · intro predicate member
    exact supplies predicate (by
      rw [← Solcore.SourceSemantics.Dynamic.BindersExtend.control_assumptions
        extension]
      exact member)

end EvidenceEnvironment.Covers

namespace BindersAllocate

theorem control_extendsHeapTypes
    {environment finalEnvironment : Environment}
    {before after : Heap} {binders : List TypedBinder} {values : List Value}
    (allocated : BindersAllocate environment before binders values
      finalEnvironment after) : HeapTypesExtend before after := by
  induction allocated with
  | nil => exact .refl _
  | cons allocation tail induction =>
      exact (HeapTypesExtend.of_allocation allocation).trans induction

theorem control_preservesHeapTyping
    {context : Context} {environment finalEnvironment : Environment}
    {before after : Heap} {binders : List TypedBinder} {values : List Value}
    (before_typed : HeapWellTyped context before)
    (values_typed : ValuesHaveTypes context before values
      (binders.map fun binder => binder.scheme.body))
    (allocated : BindersAllocate environment before binders values
      finalEnvironment after) : HeapWellTyped context after := by
  induction allocated generalizing context with
  | nil => exact before_typed
  | cons allocation tail induction =>
      cases values_typed with
      | cons value_typed remaining_typed =>
          have middle_typed := before_typed.allocate (.some value_typed) allocation
          have extension := HeapTypesExtend.of_allocation allocation
          exact induction middle_typed (remaining_typed.mono extension)

theorem control_preservesEnvironmentAgreement
    {owner : Resolved.DeclarationId} {context finalContext : Context}
    {environment finalEnvironment : Environment}
    {before after : Heap} {binders : List TypedBinder} {values : List Value}
    (extension : BindersExtend owner context binders finalContext)
    (monomorphic : ∀ binder, binder ∈ binders →
      binder.scheme.quantified = [])
    (agrees : EnvironmentAgrees before context.locals environment)
    (allocated : BindersAllocate environment before binders values
      finalEnvironment after) :
    EnvironmentAgrees after finalContext.locals finalEnvironment := by
  induction allocated generalizing context finalContext with
  | nil =>
      cases extension
      exact agrees
  | cons allocation tail induction =>
      cases extension with
      | cons headExtension tailExtension =>
          cases headExtension
          exact induction tailExtension
            (fun binder member => monomorphic binder (by simp [member]))
            (.cons allocation.reads_new rfl (monomorphic _ (by simp))
              (agrees.mono (HeapTypesExtend.of_allocation allocation)))

end BindersAllocate

end Solcore.SourceSemantics.Dynamic
