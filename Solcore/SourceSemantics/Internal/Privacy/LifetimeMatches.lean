import Solcore.SourceSemantics.Internal.Execution.CallInputs
import Solcore.SourceSemantics.Internal.Privacy.Active
import Solcore.SourceSemantics.Internal.Privacy.SelectedCalls
import Solcore.SourceSemantics.Internal.Selected.State
import Solcore.SourceSemantics.Internal.Inference.StatementDispatch
import Solcore.SourceSemantics.Internal.Privacy.Lifetimes

/-!
# Lifetimes through matches

Scrutinee and match steps, with the raw template witnesses they use.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualTemplateBackingPrimitives
/-! Raw template witnesses follow the actual state operations that precede
recursive checker calls. No source typing or execution law is required. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

theorem LiveTemplatesBacked.allocateExpressionId {state : State}
    (backed : LiveTemplatesBacked state) : LiveTemplatesBacked state.allocateExpressionId.2 :=
  backed.congr rfl rfl rfl

theorem LiveTemplatesBacked.allocateStatementId {state : State}
    (backed : LiveTemplatesBacked state) : LiveTemplatesBacked state.allocateStatementId.2 :=
  backed.congr rfl rfl rfl

theorem LiveTemplatesBacked.fresh {state : State}
    (backed : LiveTemplatesBacked state) : LiveTemplatesBacked state.fresh.2 :=
  backed.congr rfl rfl rfl

theorem LiveTemplatesBacked.allocateHiddenLocal {state : State}
    (backed : LiveTemplatesBacked state) : LiveTemplatesBacked state.allocateHiddenLocal.2 :=
  backed.congr rfl rfl rfl

theorem LiveTemplatesBacked.recordNode {state : State} (backed : LiveTemplatesBacked state)
    (node : Node) : LiveTemplatesBacked (state.recordNode node) := backed.congr rfl rfl rfl

theorem LiveTemplatesBacked.allocateMono {state : State} (backed : LiveTemplatesBacked state)
    (name : String) (type : Ty) (span : Option Syntax.SourceSpan) (comptime : Bool) :
    LiveTemplatesBacked (state.allocateBinder name (.mono type) span comptime []).2 := by
  intro binder member requirement retained
  rcases List.mem_cons.mp member with rfl | member
  · cases retained
  · exact backed binder member requirement retained

theorem LiveTemplatesBacked.unify {state next : State} {left right : Ty}
    (backed : LiveTemplatesBacked state) (solved : state.inference.Solved)
    (accepted : Detail.unify state left right = .ok next) : LiveTemplatesBacked next := by
  unfold Detail.unify at accepted
  cases computation : state.inference.unify left right with
  | error error => simp [liftUnification, computation, bind, Except.bind] at accepted
  | ok inference =>
    simp [liftUnification, computation, bind, Except.bind] at accepted
    cases accepted
    exact backed.transport (by intro _ member; exact member) (by intro _ member; exact member)
      (InferState.Solved.unify_semanticallyExtends solved computation)

theorem LiveTemplatesBacked.restore {before after : State}
    (backed : LiveTemplatesBacked before)
    (rows : before.requirements ⊆ after.requirements)
    (extension : after.inference.substitution.SemanticallyExtends before.inference.substitution) :
    LiveTemplatesBacked (after.restoreLexicalScope before.lexicalScope) :=
  backed.transport (by intro _ member; exact member) rows extension

theorem LiveTemplatesBacked.inferExprsFuel
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Expr}
    {initial : State} {result : List InferredExpression × State}
    (backed : LiveTemplatesBacked initial) (ready : initial.InferenceReady)
    (catalog : LifetimeInferenceContext context)
    (accepted : inferExprsFuel fuel context sources initial = .ok result) :
    LiveTemplatesBacked result.2 := by
  have progress := inferExprsFuel_inferenceProperties ready catalog.formation catalog.canonical accepted
  have same := congrArg LexicalScope.binders (inferExprsFuel_success_lexicalScope_eq accepted)
  exact backed.transport (by intro _ member; simp only [State.lexicalScope] at same; exact same ▸ member)
    (inferExprsFuel_requirements_subset accepted) progress.1.substitution_extends

theorem LiveTemplatesBacked.inferPlaceFuel
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {initial : State} {result : PlaceResolution × State}
    (backed : LiveTemplatesBacked initial) (ready : initial.InferenceReady)
    (catalog : LifetimeInferenceContext context)
    (accepted : inferPlaceFuel fuel context source initial = .ok result) :
    LiveTemplatesBacked result.2 := by
  have progress := inferPlaceFuel_inferenceProperties ready catalog.formation catalog.canonical accepted
  have same := congrArg LexicalScope.binders (inferPlaceFuel_success_lexicalScope_eq accepted)
  exact backed.transport (by intro _ member; simp only [State.lexicalScope] at same; exact same ▸ member)
    (inferPlaceFuel_requirements_subset accepted) progress.1.substitution_extends

theorem LiveTemplatesBacked.inferMatchCasesFuel
    {fuel : Nat} {context : SourceInference.Context} {scrutinee expected : Ty}
    {saved : LexicalScope} {sources : List Syntax.MatchCase} {initial : State}
    {result : MatchCasesResult}
    (backed : LiveTemplatesBacked initial) (ready : initial.InferenceReady)
    (catalog : LifetimeInferenceContext context)
    (scrutineeBelow : scrutinee.VariablesBelow initial.inference.next)
    (expectedBelow : expected.VariablesBelow initial.inference.next)
    (scope : initial.lexicalScope = saved)
    (accepted : inferMatchCasesFuel fuel context scrutinee expected saved sources initial = .ok result) :
    LiveTemplatesBacked result.state := by
  have progress := inferMatchCasesFuel_inferenceProperties ready catalog.formation catalog.canonical
    scrutineeBelow expectedBelow scope accepted
  have same := congrArg LexicalScope.binders
    ((inferMatchCasesFuel_success_lexicalScope_eq scope accepted).trans scope.symm)
  exact backed.transport (by intro _ member; simp only [State.lexicalScope] at same; exact same ▸ member)
    (inferMatchCasesFuel_requirements_subset accepted) progress.1.substitution_extends

theorem LiveTemplatesBacked.bindLambdaParameters
    {context : SourceInference.Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State}
    (backed : LiveTemplatesBacked state)
    (accepted : bindLambdaParameters context parameters index seen state = .ok result) :
    LiveTemplatesBacked result.2.2 := by
  induction parameters generalizing index seen state result with
  | nil =>
    simp only [Detail.bindLambdaParameters, Except.ok.injEq] at accepted
    subst result
    exact backed
  | cons parameter rest ih =>
    cases parameterValue : parameter.value with
    | error => simp [Detail.bindLambdaParameters, parameterValue, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    | inferred name =>
      by_cases duplicate : name.value ∈ seen
      · simp [Detail.bindLambdaParameters, parameterValue, duplicate, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
      · let type := state.fresh.1
        let freshState := state.fresh.2
        let binderState := (freshState.allocateBinder name.value (.mono type) (some parameter.span) false []).2
        cases tailRun : Detail.bindLambdaParameters context rest (index+1) (name.value :: seen) binderState with
        | error error => simp [Detail.bindLambdaParameters, parameterValue, duplicate, type, freshState, binderState, tailRun, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
        | ok tail =>
          rcases tail with ⟨binders, types, finalState⟩
          have same : ((freshState.allocateBinder name.value (.mono type) (some parameter.span) false []).1 :: binders,
              type :: types, finalState) = result := by
            simpa [Detail.bindLambdaParameters, parameterValue, duplicate, type, freshState, binderState, tailRun, bind, Except.bind, pure, Pure.pure, Except.pure] using accepted
          subst result
          exact ih (result := (binders, types, finalState)) (backed.fresh.allocateMono _ _ _ _) tailRun
    | typed marker name sourceType =>
      cases resolved : resolveSourceType context sourceType with
      | error error => simp [Detail.bindLambdaParameters, parameterValue, resolved, bind, Except.bind] at accepted
      | ok type =>
        by_cases duplicate : name.value ∈ seen
        · simp [Detail.bindLambdaParameters, parameterValue, resolved, duplicate, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
        · let binderState := (state.allocateBinder name.value (.mono type) (some parameter.span) marker.isSome []).2
          cases tailRun : Detail.bindLambdaParameters context rest (index+1) (name.value :: seen) binderState with
          | error error => simp [Detail.bindLambdaParameters, parameterValue, resolved, duplicate, binderState, tailRun, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
          | ok tail =>
            rcases tail with ⟨binders, types, finalState⟩
            have same : ((state.allocateBinder name.value (.mono type) (some parameter.span) marker.isSome []).1 :: binders,
                type :: types, finalState) = result := by
              simpa [Detail.bindLambdaParameters, parameterValue, resolved, duplicate, binderState, tailRun, bind, Except.bind, pure, Pure.pure, Except.pure] using accepted
            subst result
            exact ih (result := (binders, types, finalState)) (backed.allocateMono _ _ _ _) tailRun

theorem LiveTemplatesBacked.lambdaPrefix
    {context : SourceInference.Context} {expected : Option Ty} {annotation : Option Syntax.TypeExpr}
    {parameters : List Ty} {state final : State} {type : Ty}
    (backed : LiveTemplatesBacked state) (ready : state.InferenceReady)
    (prefixFacts : LambdaPrefixFacts context expected annotation parameters state type final) :
    LiveTemplatesBacked final := by
  cases prefixFacts with
  | noExpectedPartsAnnotated => exact backed
  | noExpectedPartsFresh _ _ allocation =>
    have same : state.fresh.2 = final := congrArg Prod.snd allocation
    exact same ▸ backed.fresh
  | expectedPartsAnnotated _ unified => exact backed.unify ready.solved unified
  | expectedPartsInferred _ unified => exact backed.unify ready.solved unified

theorem LiveTemplatesBacked.freshConstructor {state : State}
    (backed : LiveTemplatesBacked state) (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) :
    LiveTemplatesBacked (freshDataConstructorInstantiation dataType constructor state).2 := by
  have fold (parameters : List TypeParameterId) (accumulator : List Ty × State)
      (present : LiveTemplatesBacked accumulator.2) :
      LiveTemplatesBacked (parameters.foldl (fun result _ =>
        (result.1 ++ [result.2.fresh.1], result.2.fresh.2)) accumulator).2 := by
    induction parameters generalizing accumulator with
    | nil => exact present
    | cons parameter rest ih => exact ih _ present.fresh
  exact fold dataType.parameters ([], state) backed

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables
namespace ActualTemplateBacking

theorem expression {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {expected : Option Ty} {initial final : State} {value : InferredExpression}
    (inputs : (CallIndex.expression fuel context source expected initial value final).Inputs)
    (backed : LiveTemplatesBacked initial)
    (accepted : inferExprFuel fuel context source expected initial = .ok (value, final)) :
    LiveTemplatesBacked final := backed.inferExprFuel inputs.ready inputs.catalog.formation
      inputs.catalog.canonical inputs.bounds accepted

theorem expressions {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Expr}
    {initial final : State} {values : List InferredExpression}
    (inputs : (CallIndex.expressions fuel context sources initial values final).Inputs)
    (backed : LiveTemplatesBacked initial)
    (accepted : inferExprsFuel fuel context sources initial = .ok (values, final)) :
    LiveTemplatesBacked final := backed.inferExprsFuel inputs.ready inputs.catalog accepted

theorem statement {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expected : Ty} {initial : State} {result : StatementResult}
    (inputs : (CallIndex.statement fuel context source expected initial result).Inputs)
    (backed : LiveTemplatesBacked initial)
    (accepted : inferStatementFuel fuel context source expected initial = .ok result) :
    LiveTemplatesBacked result.state := backed.inferStatementFuel inputs.ready inputs.catalog.formation
      inputs.catalog.canonical inputs.bounds accepted

theorem statements {fuel : Nat} {context : SourceInference.Context} {source : List Syntax.Statement}
    {expected : Ty} {initial : State} {result : BlockResult}
    (inputs : (CallIndex.statements fuel context source expected initial result).Inputs)
    (backed : LiveTemplatesBacked initial)
    (accepted : inferStatementsFuel fuel context source expected initial = .ok result) :
    LiveTemplatesBacked result.state := backed.inferStatementsFuel inputs.ready inputs.catalog.formation
      inputs.catalog.canonical inputs.bounds accepted

theorem forItem {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial final : State} {result : ForItemForm}
    (inputs : (CallIndex.forItem fuel context source initial result final).Inputs)
    (backed : LiveTemplatesBacked initial)
    (accepted : inferForItemFuel fuel context source initial = .ok (result, final)) :
    LiveTemplatesBacked final := backed.inferForItemFuel inputs.ready inputs.catalog.formation
      inputs.catalog.canonical accepted

theorem forItems {fuel : Nat} {context : SourceInference.Context} {source : List Syntax.ForItem}
    {initial : State} {result : InferredForItems}
    (inputs : (CallIndex.forItems fuel context source initial result).Inputs)
    (backed : LiveTemplatesBacked initial)
    (accepted : inferForItemsFuel fuel context source initial = .ok result) :
    LiveTemplatesBacked result.state := backed.inferForItemsFuel inputs.ready inputs.catalog.formation
      inputs.catalog.canonical accepted

theorem place {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {initial final : State} {value : PlaceResolution}
    (inputs : (CallIndex.place fuel context source initial value final).Inputs)
    (backed : LiveTemplatesBacked initial)
    (accepted : inferPlaceFuel fuel context source initial = .ok (value, final)) :
    LiveTemplatesBacked final := backed.inferPlaceFuel inputs.ready inputs.catalog accepted

theorem matchCases {fuel : Nat} {context : SourceInference.Context} {scrutinee expected : Ty}
    {saved : LexicalScope} {sources : List Syntax.MatchCase} {initial : State} {result : MatchCasesResult}
    (inputs : (CallIndex.matchCases fuel context scrutinee expected saved sources initial result).Inputs)
    (backed : LiveTemplatesBacked initial)
    (accepted : inferMatchCasesFuel fuel context scrutinee expected saved sources initial = .ok result) :
    LiveTemplatesBacked result.state := backed.inferMatchCasesFuel inputs.ready inputs.catalog
      inputs.bounds.1 inputs.bounds.2.1 inputs.bounds.2.2 accepted

end ActualTemplateBacking
end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceClosedLeftUnificationPrivacy
/-! Unifying a closed left operand can only remove flexible variables. Bare
returns use this actual update even when a lambda return type is fresh. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem apply_closed (substitution : Substitution) {type : Ty}
    (closed : type.VariablesBelow 0) : substitution.apply type = type :=
  Ty.apply_eq_self_of_domain_disjoint_freeVariables substitution type
    (fun v _ occurs => False.elim (Nat.not_lt_zero _ (closed v occurs)))

private theorem closed_left_range {left right : Ty} {substitution : Substitution}
    (closed : left.VariablesBelow 0)
    (accepted : Unification.unifyTypes left right = .ok substitution) :
    ∀ v replacement, (v,replacement) ∈ substitution → replacement.VariablesBelow 0 := by
  have matched : substitution.apply right = left :=
    (Unification.unifyTypes_sound accepted).symm.trans (apply_closed substitution closed)
  have solved := Unification.unifyTypes_solvedBelow
    ((Ty.variablesBelow_nextVariable left).weaken (Nat.le_max_left _ _))
    ((Ty.variablesBelow_nextVariable right).weaken (Nat.le_max_right _ _)) accepted
  intro v replacement member candidate occurs
  have inDomain : v ∈ substitution.domain := List.mem_map.mpr ⟨(v,replacement),member,rfl⟩
  obtain ⟨constraint,present,origin⟩ := Unification.unify_domain_origin accepted inDomain
  have same : constraint = { left, right } := List.mem_singleton.mp present
  subst constraint
  have rightOrigin : v ∈ right.freeVariables := origin.resolve_left
    (fun occurs => Nat.not_lt_zero _ (closed v occurs))
  have found := StructuralSubstitution.Substitution.lookup?_eq_some_of_mem_of_domain_nodup
    solved.domain_nodup member
  have image : candidate ∈ (substitution.apply (.variable v)).freeVariables := by
    simpa only [Substitution.apply,found,Option.getD_some] using occurs
  have inResult := MonomorphicGeneralization.replacement_occurs substitution right rightOrigin image
  rw [matched] at inResult
  exact closed candidate inResult

/-- Successful unification with a left operand containing no flexible
variables can only remove flexible variables from other live types. -/
theorem unify_closed_left_private {protectedVars : List TypeVarId}
    {before after : State} {left right : Ty}
    (closed : left.VariablesBelow 0)
    (accepted : Detail.unify before left right = .ok after) :
    SafeTransport protectedVars before after := by
  unfold Detail.unify at accepted
  cases unified : before.inference.unify left right with
  | error error => simp [unified,Detail.liftUnification,bind,Except.bind] at accepted
  | ok inference =>
    simp only [unified,Detail.liftUnification,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
    cases accepted
    unfold InferState.unify at unified
    have sameLeft : before.inference.resolve left = left := apply_closed _ closed
    rw [sameLeft] at unified
    cases update : Unification.unifyTypes left (before.inference.resolve right) with
    | error error => simp [update,bind,Except.bind] at unified
    | ok substitution =>
      simp only [update,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at unified
      cases unified
      have range : substitution.RangeAvoidsDomain (guard protectedVars) := by
        intro v replacement member candidate occurs
        exact False.elim (Nat.not_lt_zero _ (closed_left_range closed update v replacement member candidate occurs))
      intro type safe
      simpa only [Safe,State.resolve,InferState.resolve,Substitution.compose_apply] using Avoids.apply safe range

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables

namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

theorem GeneralizedActualStateInvariant.unifyClosedLeft
    {before after : State} {source : TypedSource} {left right : Ty}
    (invariant : GeneralizedActualStateInvariant before source)
    (ready : before.InferenceReady)
    (closed : left.VariablesBelow 0)
    (rightBelow : right.VariablesBelow before.inference.next)
    (accepted : Detail.unify before left right = .ok after) :
    GeneralizedActualStateInvariant after source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have progress := Detail.unify_inferenceProgress ready.solved
    (closed.weaken (Nat.zero_le _)) rightBelow accepted
  have binders : after.localBinders = before.localBinders :=
    congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope accepted)
  refine ⟨⟨pending, ledger.unify accepted⟩, invariant.origins.congr_localBinders binders,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow binders progress.next_le,
    ?_, invariant.backed.transport (fun _ member => binders ▸ member) ?_ progress.substitution_extends⟩
  · intro binder member
    exact (invariant.privacy binder (binders ▸ member)).transport binders
      (unify_closed_left_private closed accepted)
  · rw [Detail.unify_requirements_eq accepted]
    exact List.Subset.refl _

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeMatchSteps
/-! Actual match child calls reach the same enclosing statement result. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail SourceInferenceExecution
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

private theorem hiddenProgress {initial final : State} {hidden : Resolved.LocalId}
    (ready : initial.InferenceReady)
    (allocation : initial.allocateHiddenLocal = (hidden, final)) :
    initial.InferenceProgress final ∧ final.InferenceReady := by
  have same : final = initial.allocateHiddenLocal.2 := (congrArg Prod.snd allocation).symm
  subst final
  exact ⟨.of_inference_eq ready.solved rfl, ready.allocateHiddenLocal⟩

private theorem hiddenLifetime {entryNext : Nat} {state final : State} {hidden : Resolved.LocalId}
    {outputs : List Ty} (allocation : state.allocateHiddenLocal = (hidden, final))
    (lifetime : GeneralizationLifetime event entryNext state outputs) :
    GeneralizationLifetime event entryNext final outputs := by
  have same : final = state.allocateHiddenLocal.2 := (congrArg Prod.snd allocation).symm
  subst final
  exact { lifetime with live := lifetime.live.transport rfl (.of_substitution_eq rfl) }

private theorem statementMatchPrefix
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {initial allocated : State}
    {id : StatementId} {scrutinee : InferredExpression} {scrutineeState hiddenState : State}
    {hidden : Resolved.LocalId}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (allocation : initial.allocateStatementId = (id, allocated))
    (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (scrutinee, scrutineeState))
    (hiddenAllocation : scrutineeState.allocateHiddenLocal = (hidden, hiddenState)) :
    initial.InferenceProgress hiddenState ∧ hiddenState.InferenceReady ∧
      hiddenState.RequirementsWellFormed ∧ scrutinee.type.VariablesBelow hiddenState.inference.next := by
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  have facts := matchScrutinee_properties (same ▸ ready.allocateStatementId) catalog scrutineeAccepted
  have hiddenFacts := hiddenProgress facts.2.1 hiddenAllocation
  have hiddenSame : hiddenState = scrutineeState.allocateHiddenLocal.2 := (congrArg Prod.snd hiddenAllocation).symm
  refine ⟨(State.InferenceProgress.allocateStatementId initial ready.solved).trans (same ▸ facts.1) |>.trans hiddenFacts.1,
    hiddenFacts.2, ?_, facts.2.2.weaken hiddenFacts.1.next_le⟩
  rw [hiddenSame]
  exact matchScrutinee_wellFormed (same ▸ wellFormed) scrutineeAccepted

theorem statement_match_cases
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
    {scrutinee : InferredExpression} {scrutineeState hiddenState : State} {hidden : Resolved.LocalId}
    {checked : MatchCasesResult} {result : StatementResult}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context) (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (form : source.value = .matchWith scrutinees arms)
    (allocation : initial.allocateStatementId = (id, allocated))
    (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (scrutinee, scrutineeState))
    (hiddenAllocation : scrutineeState.allocateHiddenLocal = (hidden, hiddenState))
    (casesAccepted : inferMatchCasesFuel fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState = .ok checked)
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event hiddenState.inference.next checked.state []) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have prefixFacts := statementMatchPrefix ready wellFormed catalog allocation scrutineeAccepted hiddenAllocation
  have completion := matchCompletion_accepted form allocation scrutineeAccepted hiddenAllocation accepted
  exact (lifetime.match_after_cases prefixFacts.2.1 prefixFacts.2.2.1 catalog prefixFacts.2.2.2
    (returnBelow.weaken prefixFacts.1.next_le) (returnBelow.weaken prefixFacts.1.next_le)
    casesAccepted completion).weaken_entry prefixFacts.1.next_le

theorem statement_match_default
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
    {scrutinee : InferredExpression} {scrutineeState hiddenState : State} {hidden : Resolved.LocalId}
    {checked : MatchCasesResult} {body : Syntax.Block} {bodyResult : BlockResult} {result : StatementResult}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context) (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (form : source.value = .matchWith scrutinees arms)
    (allocation : initial.allocateStatementId = (id, allocated))
    (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (scrutinee, scrutineeState))
    (hiddenAllocation : scrutineeState.allocateHiddenLocal = (hidden, hiddenState))
    (casesAccepted : inferMatchCasesFuel fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState = .ok checked)
    (defaultEq : arms.value.defaultBody = some body)
    (bodyAccepted : inferStatementsFuel fuel context body.value expectedReturn checked.state = .ok bodyResult)
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event checked.state.inference.next bodyResult.state [bodyResult.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have prefixFacts := statementMatchPrefix ready wellFormed catalog allocation scrutineeAccepted hiddenAllocation
  have completion := matchCompletion_accepted form allocation scrutineeAccepted hiddenAllocation accepted
  exact (lifetime.match_after_default prefixFacts.2.1 catalog prefixFacts.2.2.2
    (returnBelow.weaken prefixFacts.1.next_le) casesAccepted defaultEq bodyAccepted completion).weaken_entry prefixFacts.1.next_le

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeMatchScrutinee
/-! Scalar and synthetic tuple scrutinees use their real evaluation suffix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail SourceInferenceExecution
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

theorem statement_match_scrutinee
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
    {scrutinee : InferredExpression} {scrutineeState : State} {result : StatementResult}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context) (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (form : source.value = .matchWith scrutinees arms)
    (allocation : initial.allocateStatementId = (id, allocated))
    (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (scrutinee, scrutineeState))
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event allocated.inference.next scrutineeState [scrutinee.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  have sameNext : allocated.inference.next = initial.inference.next := by rw [same]; rfl
  have prefixFacts := matchScrutinee_properties (same ▸ ready.allocateStatementId) catalog scrutineeAccepted
  have prefixWF := matchScrutinee_wellFormed (same ▸ wellFormed) scrutineeAccepted
  let hidden := scrutineeState.allocateHiddenLocal.1
  let hiddenState := scrutineeState.allocateHiddenLocal.2
  have hiddenReady : hiddenState.InferenceReady := prefixFacts.2.1.allocateHiddenLocal
  have hiddenLife : GeneralizationLifetime event allocated.inference.next hiddenState [scrutinee.type] :=
    { lifetime with live := lifetime.live.transport rfl (.of_substitution_eq rfl) }
  have completion := matchCompletion_accepted form allocation scrutineeAccepted (show scrutineeState.allocateHiddenLocal = (hidden, hiddenState) from rfl) accepted
  cases casesAccepted : inferMatchCasesFuel fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState with
  | error error => simp [matchCompletion, casesAccepted, bind, Except.bind] at completion
  | ok checked =>
      have returnAtHidden : expectedReturn.VariablesBelow hiddenState.inference.next :=
        (sameNext ▸ returnBelow).weaken prefixFacts.1.next_le
      have checkedLife := hiddenLife.inferMatchCases hiddenReady prefixWF catalog prefixFacts.2.2
        (hiddenLife.values _ (List.mem_singleton_self _)) returnAtHidden
        (hiddenLife.older _ (sameNext ▸ returnBelow)) rfl casesAccepted
      have finished := checkedLife.match_after_cases hiddenReady prefixWF catalog prefixFacts.2.2
        returnAtHidden (sameNext ▸ returnBelow) casesAccepted completion
      simpa only [sameNext] using finished

theorem statement_match_single
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
    {scrutinee : Syntax.Expr} {value : InferredExpression} {childFinal : State} {result : StatementResult}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context) (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (form : source.value = .matchWith scrutinees arms)
    (allocation : initial.allocateStatementId = (id, allocated))
    (single : scrutinees.elements.toList = [scrutinee])
    (childAccepted : inferExprFuel fuel context scrutinee none allocated = .ok (value, childFinal))
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event allocated.inference.next childFinal [value.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (value, childFinal) := by
    simpa only [matchScrutinee, single] using childAccepted
  exact lifetime.statement_match_scrutinee ready wellFormed catalog returnBelow form allocation scrutineeAccepted accepted

theorem statement_match_many
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
    {values : List InferredExpression} {childFinal : State} {result : StatementResult}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context) (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (form : source.value = .matchWith scrutinees arms)
    (allocation : initial.allocateStatementId = (id, allocated))
    (multiple : ∀ scrutinee, scrutinees.elements.toList ≠ [scrutinee])
    (childAccepted : inferExprsFuel fuel context scrutinees.elements.toList allocated = .ok (values, childFinal))
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event allocated.inference.next childFinal (values.map (·.type))) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  let tuple : InferredExpression := ⟨childFinal.allocateExpressionId.1, Ty.productMany (values.map (·.type))⟩
  let tupleState := childFinal.allocateExpressionId.2.recordNode (.expression {
    id := tuple.id, span := source.span, type := tuple.type, form := .tuple (values.map (·.id)) })
  have scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (tuple, tupleState) := by
    unfold matchScrutinee
    split
    · rename_i sourceEq
      exact False.elim (multiple _ sourceEq)
    · simp only [childAccepted, bind, Except.bind, pure, Pure.pure, Except.pure]
      rfl
  have tupleSafe : Safe binder.scheme.quantified childFinal tuple.type := by
    exact safe_productMany _ _ _ lifetime.values
  have tupleLife : GeneralizationLifetime event allocated.inference.next tupleState [tuple.type] :=
    { lifetime with
      live := lifetime.live.transport rfl (.of_substitution_eq rfl)
      values := fun type member => (List.mem_singleton.mp member) ▸ tupleSafe }
  exact tupleLife.statement_match_scrutinee ready wellFormed catalog returnBelow form allocation scrutineeAccepted accepted

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end
