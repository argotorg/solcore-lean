import Solcore.SourceSemantics.SourceInferenceNormalizedContracts
import Solcore.Frontend.SourceInference.OccurrenceProperties

/-! Normalized formation follows the actual constructor argument traversal.
The final substitution and capture facts are passed backwards only through
successful child calls and their real node inventories. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness

private theorem unify_fields {before after : State} {left right : Ty}
    (accepted : Detail.unify before left right = .ok after) :
    after.localBinders = before.localBinders ∧ after.requirements = before.requirements := by
  unfold Detail.unify at accepted
  cases unified : before.inference.unify left right with
  | error error => simp [unified, Detail.liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, Detail.liftUnification, bind, Except.bind, pure, Pure.pure, Except.pure,
      Except.ok.injEq] at accepted
    cases accepted
    exact ⟨rfl,rfl⟩

private theorem recording_noCapture
    {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {localSchemeInstantiationStart : Option Nat} {result : InferredExpression × State}
    {outer : Substitution}
    (accepted : recordExpressionWithExpected context source id type form requirements
      expected state localSchemeInstantiationStart = .ok result)
    (capture : NoCaptureNodes outer result.2.nodes) : NoCaptureNodes outer state.nodes := by
  obtain ⟨fitted, fit, _, nodes⟩ := recordExpressionWithExpected_success_nodes accepted
  rw [nodes, (withExpected_occurrenceState_eq fit).1] at capture
  exact capture.of_prefix (List.prefix_append _ _)

private theorem recording_formation
    {semantic : SourceSemantics.Context} {context : SourceInference.Context}
    {source : Syntax.Expr} {id : ExpressionId} {type : Ty} {form : ExpressionForm}
    {requirements : List RequirementId} {expected : Option Ty} {state : State}
    {localSchemeInstantiationStart : Option Nat} {result : InferredExpression × State}
    {outer : Substitution}
    (formation : InferenceFormationContext semantic context outer)
    (stateFormed : NormalizedStateFormation semantic outer state)
    (continuation : outer.SemanticallyExtends result.2.inference.substitution)
    (typeFormed : TypeAdmissible semantic (outer.apply type))
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (accepted : recordExpressionWithExpected context source id type form requirements
      expected state localSchemeInstantiationStart = .ok result) :
    TypeAdmissible semantic (outer.apply result.1.type) ∧
      NormalizedStateFormation semantic outer result.2 := by
  have produced := recordExpressionWithExpected_normalized_formation formation.toFormationContext
    continuation typeFormed expectedFormed accepted
  exact ⟨produced.1,stateFormed.of_new_rows
    (congrArg LexicalScope.binders (localReadScope_recordExpressionWithExpected_lexicalScope accepted)) produced.2⟩

/-- The accepted cons branch exposes its actual head and tail. The final
capture checks for the head are recovered from the tail's retained prefix. -/
theorem inferConstructorArgumentsFuel_cons_formation
    {semantic : SourceSemantics.Context} {outer : Substitution} {fuel : Nat}
    {context : SourceInference.Context} {source : Syntax.Expr} {sources : List Syntax.Expr}
    {expected : Ty} {expectedTypes : List Ty} {initial : State}
    (sourceIH : InferExprFuelFormation semantic outer fuel context source
      (some (initial.resolve expected)) initial)
    (tailIH : ∀ state, InferConstructorArgumentsFuelFormation semantic outer fuel
      context sources expectedTypes state) :
    InferConstructorArgumentsFuelFormation semantic outer fuel context
      (source :: sources) (expected :: expectedTypes) initial := by
  intro ready nodes formed formation expectedBelow expectedFormed result success continuation capture
  unfold inferConstructorArgumentsFuel at success
  cases sourceRun : inferExprFuel fuel context source (some (initial.resolve expected)) initial with
  | error error => simp [sourceRun, bind, Except.bind] at success
  | ok pair =>
    rcases pair with ⟨inferred,sourceState⟩
    simp only [sourceRun,bind,Except.bind] at success
    cases tailRun : inferConstructorArgumentsFuel fuel context sources expectedTypes sourceState with
    | error error => simp [tailRun] at success
    | ok pair =>
      rcases pair with ⟨tail,finalState⟩
      simp only [tailRun] at success
      cases success
      have expectedTypeBelow := expectedBelow expected (by simp)
      have fitBelow : ∀ type ∈ some (initial.resolve expected), type.VariablesBelow initial.inference.next := by
        intro type member
        cases Option.mem_def.mp member
        exact ready.solved.variablesBelow_apply expectedTypeBelow
      have sourceProperties := inferExprFuel_inferenceProperties ready formation.validated formation.functionShapes fitBelow sourceRun
      have tailBelow : ∀ type ∈ expectedTypes, type.VariablesBelow sourceState.inference.next := by
        intro type member
        exact (expectedBelow type (by simp [member])).weaken sourceProperties.1.next_le
      have tailProperties := inferConstructorArgumentsFuel_inferenceProperties sourceProperties.2.1
        formation.validated formation.functionShapes tailBelow tailRun
      have sourceContinuation := continuation.trans tailProperties.1.substitution_extends
      have initialContinuation := sourceContinuation.trans sourceProperties.1.substitution_extends
      have fitFormed : ∀ type ∈ some (initial.resolve expected), TypeAdmissible semantic (outer.apply type) := by
        intro type member
        cases Option.mem_def.mp member
        exact (initialContinuation expected).symm ▸ expectedFormed expected (by simp)
      have sourceNodes := (inferExprFuel_occurrenceBoundExtends sourceRun).nodesBelowNextOccurrence nodes
      have retained : sourceState.nodes <+: finalState.nodes :=
        inferConstructorArgumentsFuel_preserves_nodesPrefix tailRun
          (List.prefix_refl _) sourceNodes (Nat.le_refl _)
      have sourceCapture := capture.of_prefix retained
      have headFormation := sourceIH ready nodes formed formation fitBelow fitFormed
        _ sourceRun sourceContinuation sourceCapture
      have tailFormation := tailIH sourceState sourceProperties.2.1 sourceNodes headFormation.2 formation
        tailBelow (fun type member => expectedFormed type (by simp [member])) _ tailRun continuation capture
      refine ⟨?_,tailFormation.2⟩
      intro element member
      rcases List.mem_cons.mp member with rfl | member
      · exact headFormation.1
      · exact tailFormation.1 element member

/-- Actual result fitting precedes the ordered constructor argument traversal;
recording uses the final continuation of the same successful execution. -/
theorem inferConstructorApplicationFuel_formation
    {semantic : SourceSemantics.Context} {outer : Substitution} {fuel : Nat}
    {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {instantiation : DataConstructorInstantiation} {arguments : List Syntax.Expr}
    {expected : Option Ty} {initial : State}
    (argumentsIH : ∀ state, InferConstructorArgumentsFuelFormation semantic outer fuel
      context arguments instantiation.payloadTypes state) :
    InferConstructorApplicationFuelFormation semantic outer fuel context source id
      instantiation arguments expected initial := by
  intro ready nodes formed formation payloadBelow payloadFormed resultBelow resultFormed
    expectedBelow expectedFormed result success continuation capture
  unfold inferConstructorApplicationFuel at success
  by_cases arity : arguments.length = instantiation.payloadTypes.length
  · simp only [arity,bind,Except.bind] at success
    cases expected with
    | none =>
      simp only [pure,Pure.pure,Except.pure] at success
      cases argumentsRun : inferConstructorArgumentsFuel fuel context arguments instantiation.payloadTypes initial with
      | error error => simp [argumentsRun] at success
      | ok pair =>
        rcases pair with ⟨inferredArguments,argumentsState⟩
        simp only [argumentsRun] at success
        have properties := inferConstructorArgumentsFuel_inferenceProperties ready
          formation.validated formation.functionShapes payloadBelow argumentsRun
        have recordProperties := recordExpressionWithExpected_inferenceProperties properties.2.1
          (properties.1.resolve_variablesBelow resultBelow) (by simp) success
        have argumentsContinuation := continuation.trans recordProperties.1.substitution_extends
        have argumentsFormation := argumentsIH initial ready nodes formed formation payloadBelow payloadFormed
          _ argumentsRun argumentsContinuation (recording_noCapture success capture)
        apply recording_formation formation argumentsFormation.2 continuation _ (by simp) success
        exact (argumentsContinuation instantiation.resultType).symm ▸ resultFormed
    | some expectedType =>
      cases fittedRun : Detail.unify initial instantiation.resultType expectedType with
      | error error => simp [fittedRun] at success
      | ok fittedState =>
        simp only [fittedRun] at success
        have fittedProperties := unify_inferenceProgress ready.solved resultBelow
          (expectedBelow expectedType (by simp)) fittedRun
        have fittedReady := unify_preserves_inferenceReady ready resultBelow
          (expectedBelow expectedType (by simp)) fittedRun
        have fittedNodes := (unify_occurrenceBoundExtends fittedRun).nodesBelowNextOccurrence nodes
        have fittedFields := unify_fields fittedRun
        have fittedFormed := formed.congr fittedFields.1 fittedFields.2
        have payloadAtFitted : ∀ type ∈ instantiation.payloadTypes, type.VariablesBelow fittedState.inference.next :=
          fun type member => (payloadBelow type member).weaken fittedProperties.next_le
        cases argumentsRun : inferConstructorArgumentsFuel fuel context arguments instantiation.payloadTypes fittedState with
        | error error => simp [argumentsRun] at success
        | ok pair =>
          rcases pair with ⟨inferredArguments,argumentsState⟩
          simp only [argumentsRun] at success
          have properties := inferConstructorArgumentsFuel_inferenceProperties fittedReady
            formation.validated formation.functionShapes payloadAtFitted argumentsRun
          have throughArguments := fittedProperties.trans properties.1
          have expectedAtArguments : ∀ type ∈ some expectedType, type.VariablesBelow argumentsState.inference.next :=
            fun type member => (expectedBelow type member).weaken throughArguments.next_le
          have recordProperties := recordExpressionWithExpected_inferenceProperties properties.2.1
            (throughArguments.resolve_variablesBelow resultBelow) expectedAtArguments success
          have argumentsContinuation := continuation.trans recordProperties.1.substitution_extends
          have argumentsFormation := argumentsIH fittedState fittedReady fittedNodes fittedFormed formation
            payloadAtFitted payloadFormed _ argumentsRun argumentsContinuation (recording_noCapture success capture)
          apply recording_formation formation argumentsFormation.2 continuation _ expectedFormed success
          exact (argumentsContinuation instantiation.resultType).symm ▸ resultFormed
  · simp [arity,bind,Except.bind] at success

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
