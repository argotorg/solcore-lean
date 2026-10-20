import Solcore.SourceSemantics.SourceInferenceNormalizedContracts
import Solcore.SourceSemantics.SourceInferenceNormalizedDeclarationFormation
import Solcore.Frontend.SourceInference.OccurrenceProperties

/-! Actual overload and call recording preserve normalized formation. The
recorded nodes retain the exact initialized-binder inventory. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness SourceInferenceRequirementFormation

private theorem attach_fields (state : State) (entries : List ExpressionCoercions) :
    (attachExpressionCoercions state entries).inference = state.inference ∧
      (attachExpressionCoercions state entries).localBinders = state.localBinders ∧
      (attachExpressionCoercions state entries).requirements = state.requirements := by
  induction entries generalizing state with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons entry rest ih => exact ih (state.modifyExpressionNode entry.expression
      (fun node => appendExpressionCoercions node entry.coercions))

theorem recordSelectedCallResult_normalized_fields
    (source callee : Syntax.Expr) (name : String) (arguments : List InferredExpression)
    (attempt : CandidateAttemptResult) (result : InferredExpression)
    (coercions : List CoercionStep) (state : State) :
    let recorded := recordSelectedCallResult source callee name arguments attempt result coercions state
    recorded.2.inference = state.inference ∧ recorded.2.localBinders = state.localBinders ∧
      recorded.2.requirements = state.requirements ∧ recorded.1.type = result.type ∧
      recorded.2.nodes.flatMap Node.initializedLetBinders = state.nodes.flatMap Node.initializedLetBinders := by
  dsimp only
  have fields := attach_fields state attempt.argumentCoercions
  refine ⟨fields.1,fields.2.1,fields.2.2,rfl,?_⟩
  simp only [recordSelectedCallResult, recordExpression, State.recordNode, State.allocateExpressionId,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, Node.initializedLetBinders,
    List.append_nil]
  exact NoCaptureNodes.attachExpressionCoercions_inventory state attempt.argumentCoercions

theorem recordIndirectCall_normalized_fields
    (source : Syntax.Expr) (callee : InferredExpression) (arguments : List InferredExpression)
    (application : IndirectApplicationResult) :
    let recorded := recordIndirectCall source callee arguments application
    recorded.2.inference = application.state.inference ∧
      recorded.2.localBinders = application.state.localBinders ∧
      recorded.2.requirements = application.state.requirements ∧
      recorded.1.type = application.result.type ∧
      recorded.2.nodes.flatMap Node.initializedLetBinders = application.state.nodes.flatMap Node.initializedLetBinders := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  simp only [recordIndirectCall, recordExpression, State.recordNode, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, Node.initializedLetBinders, List.append_nil]

theorem selectFunctionCandidateFrom_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution} {context : SourceInference.Context}
    {state : State} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {result : CandidateAttemptResult}
    (formation : InferenceFormationContext semantic context outer)
    (formed : NormalizedStateFormation semantic outer state)
    (cataloged : candidates ⊆ context.signatures.functions)
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (argumentsFormed : ∀ argument ∈ arguments, TypeAdmissible semantic (outer.apply argument.type))
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (continuation : outer.SemanticallyExtends result.state.inference.substitution)
    (accepted : selectFunctionCandidateFrom context name candidates arguments integerOrigins call expected state = .ok result) :
    TypeAdmissible semantic (outer.apply result.result.type) ∧
      NormalizedStateFormation semantic outer result.state := by
  obtain ⟨signature,member,tried⟩ := selectFunctionCandidateFrom_success_candidate accepted
  have produced := tryFunctionCandidate_normalized_formation formation.toFormationContext formation.scope.binders
    (formation.signatures.symm ▸ cataloged member) ready argumentsBelow expectedBelow argumentsFormed expectedFormed continuation tried
  exact ⟨produced.1,formed.of_new_rows
    (congrArg LexicalScope.binders (localReadScope_selectFunctionCandidateFrom_lexicalScope accepted)) produced.2⟩

private theorem unify_fields {state result : State} {left right : Ty}
    (accepted : Detail.unify state left right = .ok result) :
    result.localBinders = state.localBinders ∧ result.requirements = state.requirements ∧ result.nodes = state.nodes := by
  unfold Detail.unify at accepted
  cases unified : state.inference.unify left right with
  | error error => simp [unified, liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, liftUnification, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    cases accepted
    exact ⟨rfl,rfl,rfl⟩

private theorem builtin_arguments_fields {arguments : List InferredExpression} {parameters : List Ty}
    {state result : State}
    (accepted : unifyBuiltinFunctionArgumentsEqual arguments parameters state = .ok result) :
    result.localBinders = state.localBinders ∧ result.requirements = state.requirements ∧ result.nodes = state.nodes := by
  induction arguments generalizing parameters state result with
  | nil => cases accepted; exact ⟨rfl,rfl,rfl⟩
  | cons argument arguments ih =>
    cases parameters with
    | nil => cases accepted; exact ⟨rfl,rfl,rfl⟩
    | cons parameter parameters =>
      cases unified : Detail.unify state argument.type parameter with
      | error error => simp [unifyBuiltinFunctionArgumentsEqual,unified,bind,Except.bind] at accepted
      | ok middle =>
        simp only [unifyBuiltinFunctionArgumentsEqual,unified,bind,Except.bind] at accepted
        have child := ih accepted
        have fields := unify_fields unified
        exact ⟨child.1.trans fields.1,child.2.1.trans fields.2.1,child.2.2.trans fields.2.2⟩

theorem recordBuiltinFunctionCall_normalized_fields
    {source callee : Syntax.Expr} {name : String} {function : BuiltinFunctionId}
    {arguments : List InferredExpression} {call : ExpressionId} {expected : Option Ty}
    {state : State} {result : InferredExpression × State}
    (accepted : recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result) :
    result.2.localBinders = state.localBinders ∧ result.2.requirements = state.requirements ∧
      result.2.nodes.flatMap Node.initializedLetBinders = state.nodes.flatMap Node.initializedLetBinders := by
  unfold recordBuiltinFunctionCall at accepted
  by_cases arity : arguments.length = function.parameterTypes.length
  · simp only [if_pos arity,bind,Except.bind,pure,Pure.pure,Except.pure] at accepted
    cases argumentRun : unifyBuiltinFunctionArgumentsEqual arguments function.parameterTypes state with
    | error error => simp [argumentRun] at accepted
    | ok middle =>
      simp only [argumentRun] at accepted
      have fields := builtin_arguments_fields argumentRun
      cases expected with
      | none =>
        cases accepted
        refine ⟨fields.1,fields.2.1,?_⟩
        simp only [recordExpression,State.recordNode,State.allocateExpressionId,List.flatMap_append,
          List.flatMap_cons,List.flatMap_nil,Node.initializedLetBinders,List.append_nil]
        exact congrArg (List.flatMap Node.initializedLetBinders) fields.2.2
      | some expected =>
        cases resultRun : Detail.unify middle function.returnType expected with
        | error error => simp [resultRun] at accepted
        | ok final =>
          simp only [resultRun] at accepted
          cases accepted
          have finalFields := unify_fields resultRun
          refine ⟨finalFields.1.trans fields.1,finalFields.2.1.trans fields.2.1,?_⟩
          simp only [recordExpression,State.recordNode,State.allocateExpressionId,List.flatMap_append,
            List.flatMap_cons,List.flatMap_nil,Node.initializedLetBinders,List.append_nil]
          exact congrArg (List.flatMap Node.initializedLetBinders) (finalFields.2.2.trans fields.2.2)
  · simp [arity,bind,Except.bind] at accepted

theorem recordBuiltinFunctionCall_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution} {context : SourceInference.Context}
    {source callee : Syntax.Expr} {name : String} {function : BuiltinFunctionId}
    {arguments : List InferredExpression} {call : ExpressionId} {expected : Option Ty}
    {state : State} {result : InferredExpression × State}
    (formation : InferenceFormationContext semantic context outer)
    (formed : NormalizedStateFormation semantic outer state)
    (accepted : recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result) :
    TypeAdmissible semantic (outer.apply result.1.type) ∧ NormalizedStateFormation semantic outer result.2 := by
  have fields := recordBuiltinFunctionCall_normalized_fields accepted
  refine ⟨?_,formed.congr fields.1 fields.2.1⟩
  rw [recordBuiltinFunctionCall_success_returnType_eq accepted]
  apply type_applySubstitution_residual formation.residual formation.range
  cases function <;> first | exact .integer formation.scope.binders | exact .word formation.scope.binders | exact .bool formation.scope.binders

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
