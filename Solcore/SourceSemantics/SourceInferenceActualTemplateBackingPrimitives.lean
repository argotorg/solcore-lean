import Solcore.SourceSemantics.SourceInferenceActualCallInputTraversal
import Solcore.SourceSemantics.SourceInferenceLiveTemplateHeaderBacking
import Solcore.SourceSemantics.SourceInferencePatternActiveState

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
