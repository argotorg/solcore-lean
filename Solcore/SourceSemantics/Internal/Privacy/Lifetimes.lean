import Solcore.SourceSemantics.Internal.Privacy.LifetimeContinuations
import Solcore.SourceSemantics.Internal.Privacy.Active
import Solcore.SourceSemantics.Internal.Inference.RootedContracts
import Solcore.SourceSemantics.Internal.Inference.ExpressionRetained
import Solcore.SourceSemantics.Internal.Execution.CallGraph
import Solcore.SourceSemantics.Internal.Inference.StatementDispatch

/-!
# Steps of generalization lifetimes

One lifetime step for each statement, branch, loop and operand form.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeStatementSteps
/-! Actual statement completion, saved-scope restoration and ordered block
suffixes preserve the lifetime of an event produced by a nested child. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

theorem recordNode {entryNext : Nat} {state : State} {outputs : List Ty}
    (lifetime : GeneralizationLifetime event entryNext state outputs) (node : Node) :
    GeneralizationLifetime event entryNext (state.recordNode node) outputs :=
  { lifetime with live := lifetime.live.transport rfl (.of_substitution_eq rfl) }

theorem restoreScope {entryNext : Nat} {state : State} {outputs : List Ty}
    (lifetime : GeneralizationLifetime event entryNext state outputs) (saved : LexicalScope)
    (subset : saved.binders ⊆ state.localBinders) :
    GeneralizationLifetime event entryNext (state.restoreLexicalScope saved) outputs := by
  refine { lifetime with live := ?_ }
  intro liveBinder member
  exact (lifetime.live liveBinder (subset member)).transport (.of_substitution_eq rfl)

theorem statement_expression
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expression : Syntax.Expr} {semicolon : Bool} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {child : InferredExpression × State} {result : StatementResult}
    (form : source.value = .expression expression semicolon)
    (allocation : initial.allocateStatementId = (id, allocated))
    (childAccepted : inferExprFuel fuel context expression none allocated = .ok child)
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event allocated.inference.next child.2 [child.1.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have sameNext : allocated.inference.next = initial.inference.next := by
    have pair := congrArg Prod.snd allocation
    change initial.allocateStatementId.2 = allocated at pair
    rw [← pair]; rfl
  unfold inferStatementFuel at accepted
  simp only [allocation, form, childAccepted, bind, Except.bind, pure, Pure.pure,
    Except.pure, Except.ok.injEq] at accepted
  cases accepted
  have recorded := lifetime.recordNode (.statement {
    id, span := source.span, type := if semicolon then .unit else child.1.type,
    form := .expression child.1.id semicolon })
  rw [sameNext] at recorded
  refine { recorded with values := ?_ }
  intro type member
  cases List.mem_singleton.mp member
  split
  · exact safe_closed _ _ (Ty.variablesBelow_constructor 0 _)
  · exact recorded.values _ (List.mem_singleton_self _)

theorem statement_return
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expression : Syntax.Expr} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {child : InferredExpression × State} {result : StatementResult}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (form : source.value = .returnStmt (some expression))
    (allocation : initial.allocateStatementId = (id, allocated))
    (childAccepted : inferExprFuel fuel context expression (some expectedReturn) allocated = .ok child)
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event allocated.inference.next child.2 [child.1.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have allocatedEq : allocated = initial.allocateStatementId.2 :=
    (congrArg Prod.snd allocation).symm
  have sameNext : allocated.inference.next = initial.inference.next := by
    rw [allocatedEq]; rfl
  have properties := inferExprFuel_inferenceProperties
    (allocatedEq ▸ ready.allocateStatementId) catalog.formation catalog.canonical
    (by intro type member; cases member; exact sameNext ▸ returnBelow) childAccepted
  have returnSafe := safe_resolved properties.2.1
    (lifetime.older expectedReturn (sameNext ▸ returnBelow))
  unfold inferStatementFuel at accepted
  simp only [allocation, form, childAccepted, bind, Except.bind, pure, Pure.pure,
    Except.pure, Except.ok.injEq] at accepted
  cases accepted
  have recorded := lifetime.recordNode (.statement {
    id, span := source.span, type := child.2.resolve expectedReturn,
    form := .returnStmt (some child.1.id) })
  rw [sameNext] at recorded
  exact { recorded with values := fun type member => (List.mem_singleton.mp member) ▸ returnSafe }

theorem statement_block
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {body : List Syntax.Statement} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {child : BlockResult} {result : StatementResult}
    (form : source.value = .block body)
    (allocation : initial.allocateStatementId = (id, allocated))
    (childAccepted : inferStatementsFuel fuel context body expectedReturn allocated = .ok child)
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event allocated.inference.next child.state [child.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have sameNext : allocated.inference.next = initial.inference.next := by
    have pair := congrArg Prod.snd allocation
    change initial.allocateStatementId.2 = allocated at pair
    rw [← pair]; rfl
  have restored := lifetime.restoreScope allocated.lexicalScope
    (inferStatementsFuel_binders_subset childAccepted)
  unfold inferStatementFuel at accepted
  simp only [allocation, form, childAccepted, bind, Except.bind, pure, Pure.pure,
    Except.pure, Except.ok.injEq] at accepted
  cases accepted
  have recorded := restored.recordNode (.statement {
    id, span := source.span, type := child.type, form := .block child.statements })
  simpa only [sameNext] using recorded

theorem statements_single
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {head : StatementResult} {result : BlockResult}
    (headAccepted : inferStatementFuel fuel context source expectedReturn initial = .ok head)
    (accepted : inferStatementsFuel (fuel + 1) context [source] expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event initial.inference.next head.state [head.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  unfold inferStatementsFuel at accepted
  simp only [headAccepted, bind, Except.bind, pure, Pure.pure, Except.pure,
    Except.ok.injEq] at accepted
  cases accepted
  refine { lifetime with values := ?_ }
  intro type member
  cases List.mem_singleton.mp member
  split
  · exact lifetime.values _ (List.mem_singleton_self _)
  · exact safe_closed _ _ (Ty.variablesBelow_constructor 0 _)

theorem statements_head
    {fuel : Nat} {context : SourceInference.Context} {source next : Syntax.Statement}
    {sources : List Syntax.Statement} {expectedReturn : Ty} {initial : State}
    {head : StatementResult} {tail result : BlockResult}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (headAccepted : inferStatementFuel fuel context source expectedReturn initial = .ok head)
    (tailAccepted : inferStatementsFuel fuel context (next :: sources) expectedReturn head.state = .ok tail)
    (accepted : inferStatementsFuel (fuel + 1) context (source :: next :: sources)
      expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event initial.inference.next head.state [head.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have properties := inferStatementFuel_inferenceProperties ready catalog.formation
    catalog.canonical returnBelow headAccepted
  have after := lifetime.inferStatements properties.2.1
    ((inferStatementFuel_direct_progress headAccepted).wellFormed wellFormed) catalog
    (returnBelow.weaken properties.1.next_le) (lifetime.older _ returnBelow) tailAccepted
  unfold inferStatementsFuel at accepted
  simp only [headAccepted, tailAccepted, bind, Except.bind, pure, Pure.pure,
    Except.pure, Except.ok.injEq] at accepted
  cases accepted
  refine { after with values := ?_ }
  intro type member
  cases List.mem_singleton.mp member
  split
  · exact after.values _ (by simp)
  · split
    · exact after.values _ (by simp)
    · exact after.values _ (by simp)

theorem statements_tail
    {fuel : Nat} {context : SourceInference.Context} {source next : Syntax.Statement}
    {sources : List Syntax.Statement} {expectedReturn : Ty} {initial : State}
    {head : StatementResult} {tail result : BlockResult}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (headAccepted : inferStatementFuel fuel context source expectedReturn initial = .ok head)
    (tailAccepted : inferStatementsFuel fuel context (next :: sources) expectedReturn head.state = .ok tail)
    (accepted : inferStatementsFuel (fuel + 1) context (source :: next :: sources)
      expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event head.state.inference.next tail.state [tail.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have properties := inferStatementFuel_inferenceProperties ready catalog.formation
    catalog.canonical returnBelow headAccepted
  have headSafe := lifetime.older head.type properties.2.2
  have atEntry := lifetime.weaken_entry properties.1.next_le
  unfold inferStatementsFuel at accepted
  simp only [headAccepted, tailAccepted, bind, Except.bind, pure, Pure.pure,
    Except.pure, Except.ok.injEq] at accepted
  cases accepted
  refine { atEntry with values := ?_ }
  intro type member
  cases List.mem_singleton.mp member
  split
  · exact atEntry.values _ (List.mem_singleton_self _)
  · split
    · exact headSafe
    · exact atEntry.values _ (List.mem_singleton_self _)

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeStateSteps
/-! Actual allocator and unifier steps used after a nested event. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}
    {entryNext : Nat} {state : State} {outputs : List Ty}

theorem replaceOutputs
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    {values : List Ty}
    (safe : ∀ type ∈ values, Safe binder.scheme.quantified state type) :
    GeneralizationLifetime event entryNext state values :=
  { lifetime with values := safe }

theorem unify
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    {left right : Ty} {after : State}
    (ready : state.InferenceReady)
    (leftBelow : left.VariablesBelow state.inference.next)
    (rightBelow : right.VariablesBelow state.inference.next)
    (leftSafe : Safe binder.scheme.quantified state left)
    (rightSafe : Safe binder.scheme.quantified state right)
    (accepted : Detail.unify state left right = .ok after) :
    GeneralizationLifetime event entryNext after outputs := by
  have progress := unify_inferenceProgress ready.solved leftBelow rightBelow accepted
  have transport := ProtectedVariables.unify leftSafe rightSafe accepted
  have live := lifetime.live.unify leftSafe rightSafe accepted
  have result := lifetime.append (newOutputs := []) progress.next_le transport live
    (by simp) (by
      intro row present fresh
      exact False.elim (fresh ((unify_requirements_eq accepted) ▸ present)))
  simpa only [List.append_nil] using result

theorem fresh
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    (ready : state.InferenceReady) :
    GeneralizationLifetime event entryNext state.fresh.2 (outputs ++ [state.fresh.1]) := by
  have transport : SafeTransport binder.scheme.quantified state state.fresh.2 :=
    ProtectedVariables.fresh
  exact lifetime.append (Nat.le_succ _) transport
    (lifetime.live.transport rfl transport)
    (fun type member => (List.mem_singleton.mp member) ▸ fresh_type ready lifetime.bound)
    (by intro row present fresh; exact False.elim (fresh present))

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeArgumentContinuation
/-! Actual argument and match suffix inference for events already created. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}
    {entryNext : Nat} {state : State} {outputs : List Ty}
    {fuel : Nat} {context : SourceInference.Context}

theorem inferConstructorArguments
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    (ready : state.InferenceReady) (wellFormed : state.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    {sources : List Syntax.Expr} {expectedTypes : List Ty} {result : List InferredExpression × State}
    (expectedBelow : ∀ type ∈ expectedTypes, type.VariablesBelow state.inference.next)
    (expectedSafe : ∀ type ∈ expectedTypes, Safe binder.scheme.quantified state type)
    (accepted : inferConstructorArgumentsFuel fuel context sources expectedTypes state = .ok result) :
    GeneralizationLifetime event entryNext result.2 (outputs ++ result.1.map (·.type)) := by
  have privacy := inferConstructorArgumentsFuel_private binder.scheme.quantified fuel context sources expectedTypes state
    ready wellFormed lifetime.bound lifetime.live catalog.catalog catalog.formation catalog.canonical
    expectedBelow expectedSafe result accepted
  have progress := inferConstructorArgumentsFuel_inferenceProperties ready catalog.formation catalog.canonical
    expectedBelow accepted
  refine lifetime.append progress.1.next_le privacy.1 privacy.2.2.1 ?_ privacy.2.2.2
  intro type member
  obtain ⟨expression, present, rfl⟩ := List.mem_map.mp member
  exact privacy.2.1 expression present

theorem inferMatchCases
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    (ready : state.InferenceReady) (wellFormed : state.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    {scrutinee expectedReturn : Ty} {saved : LexicalScope}
    {cases : List Syntax.MatchCase} {result : MatchCasesResult}
    (scrutineeBelow : scrutinee.VariablesBelow state.inference.next)
    (scrutineeSafe : Safe binder.scheme.quantified state scrutinee)
    (returnBelow : expectedReturn.VariablesBelow state.inference.next)
    (returnSafe : Safe binder.scheme.quantified state expectedReturn)
    (scope : state.lexicalScope = saved)
    (accepted : inferMatchCasesFuel fuel context scrutinee expectedReturn saved cases state = .ok result) :
    GeneralizationLifetime event entryNext result.state outputs := by
  have privacy := inferMatchCasesFuel_private binder.scheme.quantified fuel context scrutinee expectedReturn saved cases state
    ready wellFormed lifetime.bound lifetime.live catalog.catalog catalog.formation catalog.canonical
    scrutineeBelow scrutineeSafe returnBelow returnSafe scope result accepted
  have progress := inferMatchCasesFuel_inferenceProperties ready catalog.formation catalog.canonical
    scrutineeBelow returnBelow scope accepted
  simpa only [List.append_nil] using lifetime.append (newOutputs := [])
    progress.1.next_le privacy.1 privacy.2.1 (by simp) privacy.2.2

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeAssignedValue
/-! Actual assignment places and values retain events across the operator fit. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail SourceInferenceExecution
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}


theorem assignedValue_place
    {fuel : Nat} {context : SourceInference.Context} {target value : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {initial final targetState : State}
    {assignment : AssignmentResolution} {inferred : InferredExpression} {place : PlaceResolution}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (placeAccepted : inferPlaceFuel fuel context target initial = .ok (place, targetState))
    (accepted : inferAssignedValueFuel fuel context target operator value initial = .ok (assignment, inferred, final))
    (lifetime : GeneralizationLifetime event initial.inference.next targetState [place.type]) :
    GeneralizationLifetime event initial.inference.next final [assignment.target.type, inferred.type] := by
  obtain ⟨actualPlace, actualState, fitted, actualPlaceAccepted, fitting, valueAccepted, targetEq⟩ :=
    assignedValue_actual_prefix accepted
  cases Except.ok.inj (actualPlaceAccepted.symm.trans placeAccepted)
  have fitting : assignmentFit operator targetState place.type =
      (Except.ok fitted : Except Error State) := by cases operator <;> exact fitting
  have placeProperties := inferPlaceFuel_inferenceProperties ready catalog.formation catalog.canonical placeAccepted
  have fitProperties := assignmentFit_properties placeProperties.2.1 placeProperties.2.2 fitting
  have fittedLife : GeneralizationLifetime event initial.inference.next fitted [place.type] := by
    cases operator <;> simp only [assignmentFit] at fitting
    all_goals first
    | (change Except.ok targetState = Except.ok fitted at fitting
       cases Except.ok.inj fitting
       exact lifetime)
    | exact lifetime.unify placeProperties.2.1 placeProperties.2.2 (Ty.variablesBelow_constructor _ _)
        (lifetime.values _ (by simp)) (safe_closed _ _ (Ty.variablesBelow_constructor _ _)) fitting
  have fittedWF : fitted.RequirementsWellFormed := by
    have placeWF := (inferPlaceFuel_direct_progress placeAccepted).wellFormed wellFormed
    cases operator <;> simp only [assignmentFit] at fitting
    all_goals first
    | (change Except.ok targetState = Except.ok fitted at fitting
       cases Except.ok.inj fitting
       exact placeWF)
    | exact unify_preserves_requirementsWellFormed fitting placeWF
  have expectedSafe : Safe binder.scheme.quantified fitted (assignmentExpected operator fitted place.type) := by
    cases operator <;> simp only [assignmentFit] at fitting
    all_goals first
    | exact safe_resolved fitProperties.2.1 (fittedLife.values _ (by simp))
    | exact safe_closed _ _ (Ty.variablesBelow_constructor _ _)
  have valueProperties := inferExprFuel_inferenceProperties fitProperties.2.1 catalog.formation catalog.canonical
    (by intro type member; cases member; exact fitProperties.2.2) valueAccepted
  have after := fittedLife.inferExpr fitProperties.2.1 fittedWF catalog
    (by intro type member; cases member; exact fitProperties.2.2)
    (by intro type member; cases member; exact expectedSafe) valueAccepted
  apply after.replaceOutputs
  intro type member
  rcases List.mem_cons.mp member with rfl | member
  · rw [targetEq]
    exact safe_resolved valueProperties.2.1 (after.values _ (by simp))
  · exact after.values _ (List.mem_append_right _ member)

theorem assignedValue_value
    {fuel : Nat} {context : SourceInference.Context} {target value : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {initial final targetState fitted childFinal : State}
    {assignment : AssignmentResolution} {inferred childValue : InferredExpression} {place : PlaceResolution}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (placeAccepted : inferPlaceFuel fuel context target initial = .ok (place, targetState))
    (fitting : assignmentFit operator targetState place.type =
      (Except.ok fitted : Except Error State))
    (valueAccepted : inferExprFuel fuel context value (some (assignmentExpected operator fitted place.type)) fitted = .ok (childValue, childFinal))
    (accepted : inferAssignedValueFuel fuel context target operator value initial = .ok (assignment, inferred, final))
    (lifetime : GeneralizationLifetime event fitted.inference.next childFinal [childValue.type]) :
    GeneralizationLifetime event initial.inference.next final [assignment.target.type, inferred.type] := by
  obtain ⟨actualPlace, actualState, actualFitted, actualPlaceAccepted, actualFitting, actualValueAccepted, targetEq⟩ :=
    assignedValue_actual_prefix accepted
  cases Except.ok.inj (actualPlaceAccepted.symm.trans placeAccepted)
  have actualFitting : assignmentFit operator targetState place.type =
      (Except.ok actualFitted : Except Error State) := by cases operator <;> exact actualFitting
  cases Except.ok.inj (actualFitting.symm.trans fitting)
  cases Except.ok.inj (actualValueAccepted.symm.trans valueAccepted)
  have placeProperties := inferPlaceFuel_inferenceProperties ready catalog.formation catalog.canonical placeAccepted
  have fitProperties := assignmentFit_properties placeProperties.2.1 placeProperties.2.2 fitting
  have valueProperties := inferExprFuel_inferenceProperties fitProperties.2.1 catalog.formation catalog.canonical
    (by intro type member; cases member; exact fitProperties.2.2) valueAccepted
  have after := lifetime.weaken_entry (placeProperties.1.trans fitProperties.1).next_le
  apply after.replaceOutputs
  intro type member
  rcases List.mem_cons.mp member with rfl | member
  · rw [targetEq]
    exact safe_resolved valueProperties.2.1 (lifetime.older _ (placeProperties.2.2.weaken fitProperties.1.next_le))
  · exact lifetime.values _ member

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeBinary
/-! Binary operands retain a created generalization through the other operand,
the actual selected operator, expected-type fitting and result recording. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

theorem binary_suffix
    {entryNext : Nat} {context : SourceInference.Context}
    {source : Syntax.Expr} {operator : Syntax.Located Syntax.BinaryOp} {id : ExpressionId}
    {left right : InferredExpression} {expected : Option Ty}
    {integerLiterals : List IntegerLiteralOrigin} {state : State}
    {final : InferredExpression × State}
    (ready : state.InferenceReady) (catalog : LifetimeInferenceContext context)
    (leftBelow : left.type.VariablesBelow state.inference.next)
    (rightBelow : right.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (expectedBefore : ∀ type ∈ expected, type.VariablesBelow entryNext)
    (lifetime : GeneralizationLifetime event entryNext state [left.type, right.type])
    (dispatch : BinaryExpressionDispatchFacts context source id operator left right
      expected integerLiterals state final) :
    GeneralizationLifetime event entryNext final.2 [final.1.type] := by
  have leftSafe := lifetime.values left.type (by simp)
  have rightSafe := lifetime.values right.type (by simp)
  have expectedSafe : ∀ type ∈ expected, Safe binder.scheme.quantified state type :=
    fun type member => lifetime.older type (expectedBefore type member)
  have finish (result : OperatorInferenceResult)
      (operatorAccepted : inferBinaryOperator context operator.value left.type right.type
        expected integerLiterals state = .ok result)
      (recorded : recordExpressionWithExpected context source id result.type
        (.binary left.id operator.value right.id) result.requirements expected result.state = .ok final) :
      GeneralizationLifetime event entryNext final.2 [final.1.type] := by
    have operatorLife := lifetime.binaryOperator catalog.catalog ready leftBelow rightBelow
      expectedBelow leftSafe rightSafe expectedSafe operatorAccepted
    have properties := inferBinaryOperator_inferenceProperties ready leftBelow rightBelow
      expectedBelow operatorAccepted
    have recordedLife := operatorLife.recordExpression catalog.catalog properties.2.1 properties.2.2
      (fun type member => (expectedBelow type member).weaken properties.1.next_le)
      (operatorLife.values _ (List.mem_append_right _ (List.mem_singleton_self _)))
      (fun type member => operatorLife.older type (expectedBefore type member)) recorded
    exact recordedLife.restrict_outputs (by intro type member; exact List.mem_append_right _ member)
  cases dispatch with
  | directFunction _ _ operatorAccepted recorded => exact finish _ operatorAccepted recorded
  | traitMethod _ operatorAccepted recorded => exact finish _ operatorAccepted recorded
  | @selectedFunction name head tail attempt fitted _ lookup selected fitting recorded =>
      have cataloged := functionsNamed_success_subset_catalog lookup
      have argumentsBelow : ∀ argument ∈ [left, right], argument.type.VariablesBelow state.inference.next := by
        intro argument member
        rcases List.mem_cons.mp member with rfl | member
        · exact leftBelow
        · cases List.mem_singleton.mp member
          exact rightBelow
      have argumentsSafe : ∀ argument ∈ [left, right], Safe binder.scheme.quantified state argument.type := by
        intro argument member
        rcases List.mem_cons.mp member with rfl | member
        · exact leftSafe
        · cases List.mem_singleton.mp member
          exact rightSafe
      have boolBelow : ∀ type ∈ (some Ty.bool : Option Ty), type.VariablesBelow state.inference.next := by
        intro type member
        simp only [Option.mem_def, Option.some.injEq] at member
        subst type
        exact Ty.variablesBelow_constructor _ _
      have boolSafe : ∀ type ∈ (some Ty.bool : Option Ty), Safe binder.scheme.quantified state type := by
        intro type member
        simp only [Option.mem_def, Option.some.injEq] at member
        subst type
        exact safe_closed _ _ (Ty.variablesBelow_constructor _ _)
      have selectedLife := lifetime.selectCandidate catalog cataloged ready argumentsBelow boolBelow
        argumentsSafe boolSafe selected
      have selectedProperties := selectFunctionCandidateFrom_inferenceProperties ready argumentsBelow
        (fun signature member => catalog.formation.function_scheme_body_variablesBelow
          (cataloged member) (catalog.canonical signature (cataloged member)) _) boolBelow selected
      have expectedAtSelection : ∀ type ∈ expected, type.VariablesBelow attempt.state.inference.next :=
        fun type member => (expectedBelow type member).weaken selectedProperties.1.next_le
      have fittedLife := selectedLife.fitExpected catalog.catalog selectedProperties.2.1
        selectedProperties.2.2 expectedAtSelection
        (selectedLife.values _ (List.mem_append_right _ (List.mem_singleton_self _)))
        (fun type member => selectedLife.older type (expectedBefore type member)) fitting
      have fittedProperties := withExpected_inferenceProperties selectedProperties.2.1
        selectedProperties.2.2 expectedAtSelection fitting
      let callee : Syntax.Expr := {
        span := operator.span
        value := .identifier {span := operator.span, value := name} }
      have recordedLife := fittedLife.recordSelectedResult source callee name [left, right] attempt
        fitted.expression fitted.coercions fittedProperties.2.1 fittedProperties.2.2
        (fittedLife.values _ (List.mem_append_right _ (List.mem_singleton_self _)))
      change recordSelectedCallResult source callee name [left, right] attempt
        fitted.expression fitted.coercions fitted.state = final at recorded
      rw [recorded] at recordedLife
      exact recordedLife.restrict_outputs (by intro type member; exact List.mem_append_right _ member)

theorem binary_left
    {fuel : Nat} {context : SourceInference.Context}
    {source left right : Syntax.Expr} {operator : Syntax.Located Syntax.BinaryOp}
    {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {leftResult rightResult final : InferredExpression × State}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (form : source.value = .binary left operator right)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (leftAccepted : inferExprFuel fuel context left none allocated = .ok leftResult)
    (rightAccepted : inferExprFuel fuel context right none leftResult.2 = .ok rightResult)
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok final)
    (lifetime : GeneralizationLifetime event allocated.inference.next leftResult.2 [leftResult.1.type]) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  have allocatedEq : allocated = initial.allocateExpressionId.2 :=
    (congrArg Prod.snd allocation).symm
  have sameNext : allocated.inference.next = initial.inference.next := by
    rw [allocatedEq]; rfl
  have lifetime : GeneralizationLifetime event initial.inference.next leftResult.2 [leftResult.1.type] := by
    simpa only [sameNext] using lifetime
  have leftProperties := inferExprFuel_inferenceProperties
    (allocatedEq ▸ ready.allocateExpressionId) catalog.formation catalog.canonical (by simp) leftAccepted
  have rightProperties := inferExprFuel_inferenceProperties leftProperties.2.1
    catalog.formation catalog.canonical (by simp) rightAccepted
  have allocatedWellFormed : allocated.RequirementsWellFormed := by
    rw [allocatedEq]
    exact wellFormed
  have leftWellFormed := (inferExprFuel_direct_progress leftAccepted).wellFormed allocatedWellFormed
  have afterRight := lifetime.inferExpr leftProperties.2.1 leftWellFormed catalog
    (by simp) (by simp) rightAccepted
  obtain ⟨actualLeft, leftState, actualRight, rightState, actualLeftAccepted, actualRightAccepted, dispatch⟩ :=
    inferExprFuel_success_binary_facts form allocation accepted
  have sameLeft := Except.ok.inj (actualLeftAccepted.symm.trans leftAccepted)
  cases sameLeft
  have sameRight := Except.ok.inj (actualRightAccepted.symm.trans rightAccepted)
  cases sameRight
  exact binary_suffix rightProperties.2.1 catalog
    (leftProperties.2.2.weaken rightProperties.1.next_le) rightProperties.2.2
    (fun type member => (sameNext ▸ expectedBelow type member).weaken
      (Nat.le_trans leftProperties.1.next_le rightProperties.1.next_le))
    expectedBelow afterRight dispatch

theorem binary_right
    {fuel : Nat} {context : SourceInference.Context}
    {source left right : Syntax.Expr} {operator : Syntax.Located Syntax.BinaryOp}
    {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {leftResult rightResult final : InferredExpression × State}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (form : source.value = .binary left operator right)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (leftAccepted : inferExprFuel fuel context left none allocated = .ok leftResult)
    (rightAccepted : inferExprFuel fuel context right none leftResult.2 = .ok rightResult)
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok final)
    (lifetime : GeneralizationLifetime event leftResult.2.inference.next rightResult.2 [rightResult.1.type]) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  have allocatedEq : allocated = initial.allocateExpressionId.2 :=
    (congrArg Prod.snd allocation).symm
  have sameNext : allocated.inference.next = initial.inference.next := by
    rw [allocatedEq]; rfl
  have leftProperties := inferExprFuel_inferenceProperties
    (allocatedEq ▸ ready.allocateExpressionId) catalog.formation catalog.canonical (by simp) leftAccepted
  have rightProperties := inferExprFuel_inferenceProperties leftProperties.2.1
    catalog.formation catalog.canonical (by simp) rightAccepted
  have both := lifetime.replaceOutputs (values := [leftResult.1.type, rightResult.1.type]) (by
    intro type member
    rcases List.mem_cons.mp member with rfl | member
    · exact lifetime.older _ leftProperties.2.2
    · exact lifetime.values _ member)
  have afterRight := both.weaken_entry (sameNext ▸ leftProperties.1.next_le)
  obtain ⟨actualLeft, leftState, actualRight, rightState, actualLeftAccepted, actualRightAccepted, dispatch⟩ :=
    inferExprFuel_success_binary_facts form allocation accepted
  have sameLeft := Except.ok.inj (actualLeftAccepted.symm.trans leftAccepted)
  cases sameLeft
  have sameRight := Except.ok.inj (actualRightAccepted.symm.trans rightAccepted)
  cases sameRight
  exact binary_suffix rightProperties.2.1 catalog
    (leftProperties.2.2.weaken rightProperties.1.next_le) rightProperties.2.2
    (fun type member => (sameNext ▸ expectedBelow type member).weaken
      (Nat.le_trans leftProperties.1.next_le rightProperties.1.next_le))
    expectedBelow afterRight dispatch

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeForSteps
/-! Actual non-declaration header completion and ordered header suffixes. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

theorem forItems_head
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {sources : List Syntax.ForItem} {initial : State}
    {head : ForItemForm × State} {tail result : InferredForItems}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (headAccepted : inferForItemFuel fuel context source initial = .ok head)
    (tailAccepted : inferForItemsFuel fuel context sources head.2 = .ok tail)
    (accepted : inferForItemsFuel fuel context (source :: sources) initial = .ok result)
    (lifetime : GeneralizationLifetime event initial.inference.next head.2 []) :
    GeneralizationLifetime event initial.inference.next result.state [] := by
  have properties := inferForItemFuel_inferenceProperties ready catalog.formation
    catalog.canonical headAccepted
  have after := lifetime.inferForItems properties.2
    ((inferForItemFuel_direct_progress headAccepted).wellFormed wellFormed) catalog tailAccepted
  have resultEq : ({ items := head.1 :: tail.items, state := tail.state } : InferredForItems) = result := by
    simpa only [inferForItemsFuel, headAccepted, tailAccepted, bind, Except.bind,
      pure, Pure.pure, Except.pure, Except.ok.injEq] using accepted
  cases resultEq
  exact after

theorem forItems_tail
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {sources : List Syntax.ForItem} {initial : State}
    {head : ForItemForm × State} {tail result : InferredForItems}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (headAccepted : inferForItemFuel fuel context source initial = .ok head)
    (tailAccepted : inferForItemsFuel fuel context sources head.2 = .ok tail)
    (accepted : inferForItemsFuel fuel context (source :: sources) initial = .ok result)
    (lifetime : GeneralizationLifetime event head.2.inference.next tail.state []) :
    GeneralizationLifetime event initial.inference.next result.state [] := by
  have properties := inferForItemFuel_inferenceProperties ready catalog.formation
    catalog.canonical headAccepted
  have resultEq : ({ items := head.1 :: tail.items, state := tail.state } : InferredForItems) = result := by
    simpa only [inferForItemsFuel, headAccepted, tailAccepted, bind, Except.bind,
      pure, Pure.pure, Except.pure, Except.ok.injEq] using accepted
  cases resultEq
  exact lifetime.weaken_entry properties.1.next_le

theorem forItem_expression
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {expression : Syntax.Expr} {initial : State}
    {child : InferredExpression × State} {result : ForItemForm × State}
    (form : source.value = .expression expression)
    (childAccepted : inferExprFuel fuel context expression none initial = .ok child)
    (accepted : inferForItemFuel (fuel + 1) context source initial = .ok result)
    (lifetime : GeneralizationLifetime event initial.inference.next child.2 [child.1.type]) :
    GeneralizationLifetime event initial.inference.next result.2 [] := by
  have resultEq : (.expression child.1.id, child.2) = result := by
    simpa only [inferForItemFuel, form, childAccepted, bind, Except.bind,
      pure, Pure.pure, Except.pure, Except.ok.injEq] using accepted
  cases resultEq
  exact lifetime.restrict_outputs (by simp)

theorem forItem_assignment
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {target value : Syntax.Expr} {operator : Syntax.Located Syntax.ValueAssignOp}
    {initial : State} {child : AssignmentResolution × InferredExpression × State}
    {result : ForItemForm × State}
    (form : source.value = .assignValue target operator value)
    (childAccepted : inferAssignedValueFuel fuel context target operator.value value initial = .ok child)
    (accepted : inferForItemFuel (fuel + 1) context source initial = .ok result)
    (lifetime : GeneralizationLifetime event initial.inference.next child.2.2
      [child.1.target.type, child.2.1.type]) :
    GeneralizationLifetime event initial.inference.next result.2 [] := by
  have resultEq : (.assignValue child.1 operator.value child.2.1.id, child.2.2) = result := by
    simpa only [inferForItemFuel, form, childAccepted, bind, Except.bind,
      pure, Pure.pure, Except.pure, Except.ok.injEq] using accepted
  cases resultEq
  exact lifetime.restrict_outputs (by simp)

theorem forItem_bitnot
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {target : Syntax.Expr} {operator : Syntax.SourceSpan} {initial fitted : State}
    {child : PlaceResolution × State} {result : ForItemForm × State}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (form : source.value = .assignBitNot target operator)
    (childAccepted : inferPlaceFuel fuel context target initial = .ok child)
    (fitting : Detail.unify child.2 child.1.type .word = .ok fitted)
    (accepted : inferForItemFuel (fuel + 1) context source initial = .ok result)
    (lifetime : GeneralizationLifetime event initial.inference.next child.2 [child.1.type]) :
    GeneralizationLifetime event initial.inference.next result.2 [] := by
  have properties := inferPlaceFuel_inferenceProperties ready catalog.formation catalog.canonical childAccepted
  have after := lifetime.unify properties.2.1 properties.2.2
    (Ty.variablesBelow_constructor _ _) (lifetime.values _ (List.mem_singleton_self _))
    (safe_closed _ _ (Ty.variablesBelow_constructor 0 _)) fitting
  have resultEq :
      (.assignBitNot { target := { child.1 with type := fitted.resolve child.1.type } }, fitted) = result := by
    simpa only [inferForItemFuel, form, childAccepted, fitting, bind, Except.bind,
      pure, Pure.pure, Except.pure, Except.ok.injEq] using accepted
  cases resultEq
  exact after.restrict_outputs (by simp)

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeBranchSteps
/-! Branch and loop continuations restore the actual saved lexical scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

theorem LifetimeInferenceContext.withLoopDepth {context : SourceInference.Context}
    (catalog : LifetimeInferenceContext context) (depth : Nat) :
    LifetimeInferenceContext {context with loopDepth := depth} :=
  ⟨catalog.catalog, catalog.formation, catalog.canonical⟩

private theorem allocatedStatement_properties
    {initial next : State} {id : StatementId}
    (ready : initial.InferenceReady)
    (allocation : initial.allocateStatementId = (id, next)) :
    initial.InferenceProgress next ∧ next.InferenceReady := by
  have progress := State.InferenceProgress.allocateStatementId initial ready.solved
  have nextReady := ready.allocateStatementId
  rw [allocation] at progress nextReady
  exact ⟨progress, nextReady⟩

namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

theorem recordUnit {entryNext : Nat} {state : State} {outputs : List Ty}
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    (id : StatementId) (span : Syntax.SourceSpan) (form : StatementForm) :
    GeneralizationLifetime event entryNext
      (state.recordNode (.statement {id, span, type := .unit, form})) [.unit] :=
  (lifetime.recordNode _).replaceOutputs
    (by
      intro type member
      cases List.mem_singleton.mp member
      exact safe_closed _ _ (Ty.variablesBelow_constructor 0 _))

theorem while_body
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {condition : Syntax.Expr} {body : Syntax.Block} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {conditionResult : InferredExpression × State} {bodyResult : BlockResult}
    {result : StatementResult}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (form : source.value = .whileLoop condition body)
    (allocation : initial.allocateStatementId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (bodyAccepted : inferStatementsFuel fuel {context with loopDepth := context.loopDepth + 1}
      body.value expectedReturn conditionResult.2 = .ok bodyResult)
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event conditionResult.2.inference.next bodyResult.state [bodyResult.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have allocatedProperties := allocatedStatement_properties ready allocation
  have conditionProperties := inferExprFuel_inferenceProperties allocatedProperties.2
    catalog.formation catalog.canonical (by
      intro type member; cases member; exact Ty.variablesBelow_constructor _ _) conditionAccepted
  have restored := lifetime.restoreScope conditionResult.2.lexicalScope
    (inferStatementsFuel_binders_subset bodyAccepted)
  have recorded := restored.recordUnit id source.span
    (.whileLoop conditionResult.1.id bodyResult.statements)
  have atEntry := recorded.weaken_entry
    (allocatedProperties.1.trans conditionProperties.1).next_le
  unfold inferStatementFuel at accepted
  simp only [allocation, form, conditionAccepted, bodyAccepted, bind, Except.bind,
    pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  exact atEntry

theorem while_condition
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {condition : Syntax.Expr} {body : Syntax.Block} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {conditionResult : InferredExpression × State} {bodyResult : BlockResult}
    {result : StatementResult}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (form : source.value = .whileLoop condition body)
    (allocation : initial.allocateStatementId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (bodyAccepted : inferStatementsFuel fuel {context with loopDepth := context.loopDepth + 1}
      body.value expectedReturn conditionResult.2 = .ok bodyResult)
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event allocated.inference.next conditionResult.2 [conditionResult.1.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have allocatedEq : allocated = initial.allocateStatementId.2 :=
    (congrArg Prod.snd allocation).symm
  have allocatedProperties := allocatedStatement_properties ready allocation
  have conditionProperties := inferExprFuel_inferenceProperties allocatedProperties.2
    catalog.formation catalog.canonical (by
      intro type member; cases member; exact Ty.variablesBelow_constructor _ _) conditionAccepted
  have conditionWF := (inferExprFuel_direct_progress conditionAccepted).wellFormed
    (show allocated.RequirementsWellFormed by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed)
  have after := lifetime.inferStatements conditionProperties.2.1 conditionWF
    (catalog.withLoopDepth (context.loopDepth + 1))
    (returnBelow.weaken (allocatedProperties.1.trans conditionProperties.1).next_le)
    (lifetime.older _ (returnBelow.weaken allocatedProperties.1.next_le)) bodyAccepted
  have restored := after.restoreScope conditionResult.2.lexicalScope
    (inferStatementsFuel_binders_subset bodyAccepted)
  have recorded := restored.recordUnit id source.span
    (.whileLoop conditionResult.1.id bodyResult.statements)
  have atEntry := recorded.weaken_entry allocatedProperties.1.next_le
  unfold inferStatementFuel at accepted
  simp only [allocation, form, conditionAccepted, bodyAccepted, bind, Except.bind,
    pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  exact atEntry

theorem if_without_else_body
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {condition : Syntax.Expr} {body : Syntax.Block} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {conditionResult : InferredExpression × State} {bodyResult : BlockResult}
    {result : StatementResult}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (form : source.value = .ifThen condition body none)
    (allocation : initial.allocateStatementId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (bodyAccepted : inferStatementsFuel fuel context body.value expectedReturn conditionResult.2 = .ok bodyResult)
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event conditionResult.2.inference.next bodyResult.state [bodyResult.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have allocatedProperties := allocatedStatement_properties ready allocation
  have conditionProperties := inferExprFuel_inferenceProperties allocatedProperties.2
    catalog.formation catalog.canonical (by
      intro type member; cases member; exact Ty.variablesBelow_constructor _ _) conditionAccepted
  have restored := lifetime.restoreScope conditionResult.2.lexicalScope
    (inferStatementsFuel_binders_subset bodyAccepted)
  have recorded := restored.recordUnit id source.span
    (.ifThen conditionResult.1.id bodyResult.statements none)
  have atEntry := recorded.weaken_entry
    (allocatedProperties.1.trans conditionProperties.1).next_le
  unfold inferStatementFuel at accepted
  simp only [allocation, form, conditionAccepted, bodyAccepted, bind, Except.bind,
    pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  exact atEntry

theorem if_without_else_condition
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {condition : Syntax.Expr} {body : Syntax.Block} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {conditionResult : InferredExpression × State} {bodyResult : BlockResult}
    {result : StatementResult}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (form : source.value = .ifThen condition body none)
    (allocation : initial.allocateStatementId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (bodyAccepted : inferStatementsFuel fuel context body.value expectedReturn conditionResult.2 = .ok bodyResult)
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event allocated.inference.next conditionResult.2 [conditionResult.1.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have allocatedEq : allocated = initial.allocateStatementId.2 :=
    (congrArg Prod.snd allocation).symm
  have allocatedProperties := allocatedStatement_properties ready allocation
  have conditionProperties := inferExprFuel_inferenceProperties allocatedProperties.2
    catalog.formation catalog.canonical (by
      intro type member; cases member; exact Ty.variablesBelow_constructor _ _) conditionAccepted
  have conditionWF := (inferExprFuel_direct_progress conditionAccepted).wellFormed
    (show allocated.RequirementsWellFormed by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed)
  have after := lifetime.inferStatements conditionProperties.2.1 conditionWF catalog
    (returnBelow.weaken (allocatedProperties.1.trans conditionProperties.1).next_le)
    (lifetime.older _ (returnBelow.weaken allocatedProperties.1.next_le)) bodyAccepted
  have restored := after.restoreScope conditionResult.2.lexicalScope
    (inferStatementsFuel_binders_subset bodyAccepted)
  have recorded := restored.recordUnit id source.span
    (.ifThen conditionResult.1.id bodyResult.statements none)
  have atEntry := recorded.weaken_entry allocatedProperties.1.next_le
  unfold inferStatementFuel at accepted
  simp only [allocation, form, conditionAccepted, bodyAccepted, bind, Except.bind,
    pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  exact atEntry

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeCallSteps
/-! The actual dispatch after a call's arguments preserves generalizations
created in those arguments or in its indirect callee. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

theorem indirect_callee_suffix
    {entryNext : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {id : ExpressionId} {arguments : List InferredExpression} {expected : Option Ty}
    {callee : InferredExpression} {state : State} {application : IndirectApplicationResult}
    {result : InferredExpression × State}
    (ready : state.InferenceReady) (catalog : LifetimeInferenceContext context)
    (calleeBelow : callee.type.VariablesBelow state.inference.next)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (argumentsBefore : ∀ argument ∈ arguments, argument.type.VariablesBelow entryNext)
    (expectedBefore : ∀ type ∈ expected, type.VariablesBelow entryNext)
    (applicationAccepted : applyFunctionType context id callee.type arguments expected state = .ok application)
    (recorded : recordIndirectCall source callee arguments application = result)
    (lifetime : GeneralizationLifetime event entryNext state [callee.type]) :
    GeneralizationLifetime event entryNext result.2 [result.1.type] := by
  have after := lifetime.applyIndirect catalog.catalog ready calleeBelow argumentsBelow expectedBelow
    (lifetime.values _ (by simp))
    (fun argument member => lifetime.older _ (argumentsBefore argument member))
    (fun type member => lifetime.older _ (expectedBefore type member)) applicationAccepted
  have properties := applyFunctionType_inferenceProperties ready calleeBelow argumentsBelow expectedBelow applicationAccepted
  have completed := after.recordIndirect source callee arguments properties.2.1 properties.2.2
    (after.values _ (List.mem_append_right _ (List.mem_singleton_self _)))
  rw [recorded] at completed
  exact completed.restrict_outputs (by intro type member; exact List.mem_append_right _ member)

theorem call_arguments_suffix
    {fuel : Nat} {context : SourceInference.Context} {source callee : Syntax.Expr}
    {arguments : Syntax.DelimitedList Syntax.Expr} {id : ExpressionId} {expected : Option Ty}
    {initial : State} {child : List InferredExpression × State} {result : InferredExpression × State}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (nonconstructor : constructorCalleeCandidates context initial callee = .ok [])
    (childAccepted : inferExprsFuel fuel context arguments.elements initial = .ok child)
    (dispatch : CallExpressionDispatchProvenanceFacts context source callee arguments id expected fuel initial result)
    (lifetime : GeneralizationLifetime event initial.inference.next child.2 (child.1.map (·.type))) :
    GeneralizationLifetime event initial.inference.next result.2 [result.1.type] := by
  have properties := inferExprsFuel_inferenceProperties ready catalog.formation catalog.canonical childAccepted
  have expectedAfter : ∀ type ∈ expected, type.VariablesBelow child.2.inference.next :=
    fun type member => (expectedBelow type member).weaken properties.1.next_le
  have argumentsSafe : ∀ argument ∈ child.1, Safe binder.scheme.quantified child.2 argument.type :=
    fun argument member => lifetime.values _ (List.mem_map.mpr ⟨argument, member, rfl⟩)
  have expectedSafe : ∀ type ∈ expected, Safe binder.scheme.quantified child.2 type :=
    fun type member => lifetime.older _ (expectedBelow type member)
  cases dispatch with
  | constructor discovery _ _ => simp [nonconstructor] at discovery
  | @selected inferredArguments argumentState name candidates integerLiterals attempt _ actualArguments origin selected recorded =>
      have same := Except.ok.inj (actualArguments.symm.trans childAccepted)
      cases same
      have after := lifetime.selectCandidate catalog origin.candidatesSubset properties.2.1 properties.2.2
        expectedAfter argumentsSafe expectedSafe selected
      have selectedProperties := selectFunctionCandidateFrom_inferenceProperties properties.2.1 properties.2.2
        (fun signature member => catalog.formation.function_scheme_body_variablesBelow
          (origin.candidatesSubset member) (catalog.canonical signature (origin.candidatesSubset member)) _)
        expectedAfter selected
      have completed := after.recordSelected source callee name inferredArguments selectedProperties.2.1 selectedProperties.2.2
        (after.values _ (List.mem_append_right _ (List.mem_singleton_self _)))
      rw [recorded] at completed
      exact completed.restrict_outputs (by intro type member; exact List.mem_append_right _ member)
  | builtin _ actualArguments recorded =>
      have same := Except.ok.inj (actualArguments.symm.trans childAccepted)
      cases same
      have completed := lifetime.recordBuiltin properties.2.1 properties.2.2 expectedAfter argumentsSafe expectedSafe recorded
      exact completed.restrict_outputs (by intro type member; exact List.mem_append_right _ member)
  | @indirect inferredArguments argumentState calleeState inferredCallee application _ actualArguments _ calleeAccepted applicationAccepted recorded =>
      have same := Except.ok.inj (actualArguments.symm.trans childAccepted)
      cases same
      have calleeProperties := inferExprFuel_inferenceProperties properties.2.1 catalog.formation catalog.canonical (by simp) calleeAccepted
      have afterCallee := lifetime.inferExpr properties.2.1
        ((inferExprsFuel_direct_progress childAccepted).wellFormed wellFormed) catalog (by simp) (by simp) calleeAccepted
      have after := afterCallee.applyIndirect catalog.catalog calleeProperties.2.1 calleeProperties.2.2
        (fun argument member => (properties.2.2 argument member).weaken calleeProperties.1.next_le)
        (fun type member => (expectedAfter type member).weaken calleeProperties.1.next_le)
        (afterCallee.values _ (List.mem_append_right _ (List.mem_singleton_self _)))
        (fun argument member => afterCallee.values _ (List.mem_append_left _ (List.mem_map.mpr ⟨argument, member, rfl⟩)))
        (fun type member => afterCallee.older _ (expectedBelow type member)) applicationAccepted
      have applicationProperties := applyFunctionType_inferenceProperties calleeProperties.2.1 calleeProperties.2.2
        (fun argument member => (properties.2.2 argument member).weaken calleeProperties.1.next_le)
        (fun type member => (expectedAfter type member).weaken calleeProperties.1.next_le) applicationAccepted
      have completed := after.recordIndirect source inferredCallee inferredArguments applicationProperties.2.1 applicationProperties.2.2
        (after.values _ (List.mem_append_right _ (List.mem_singleton_self _)))
      rw [recorded] at completed
      exact completed.restrict_outputs (by intro type member; exact List.mem_append_right _ member)

theorem call_arguments
    {fuel : Nat} {context : SourceInference.Context} {source callee : Syntax.Expr}
    {arguments : Syntax.DelimitedList Syntax.Expr} {id : ExpressionId} {expected : Option Ty}
    {initial allocated : State} {child : List InferredExpression × State} {result : InferredExpression × State}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (form : source.value = .call callee arguments)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (nonconstructor : constructorCalleeCandidates context allocated callee = .ok [])
    (childAccepted : inferExprsFuel fuel context arguments.elements allocated = .ok child)
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok result)
    (lifetime : GeneralizationLifetime event allocated.inference.next child.2 (child.1.map (·.type))) :
    GeneralizationLifetime event initial.inference.next result.2 [result.1.type] := by
  have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  have sameNext : allocated.inference.next = initial.inference.next := by rw [allocatedEq]; rfl
  have allocatedWF : allocated.RequirementsWellFormed := by rw [allocatedEq]; exact wellFormed
  have after := lifetime.call_arguments_suffix (allocatedEq ▸ ready.allocateExpressionId) allocatedWF catalog
    (fun type member => sameNext ▸ expectedBelow type member) nonconstructor childAccepted
    (inferExprFuel_success_call_dispatch_provenance_facts form allocation accepted)
  simpa only [sameNext] using after

theorem call_callee
    {fuel : Nat} {context : SourceInference.Context} {source callee : Syntax.Expr}
    {arguments : Syntax.DelimitedList Syntax.Expr} {id : ExpressionId} {expected : Option Ty}
    {initial allocated argumentState calleeState : State}
    {inferredArguments : List InferredExpression} {inferredCallee : InferredExpression}
    {result : InferredExpression × State}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (form : source.value = .call callee arguments)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (nonconstructor : constructorCalleeCandidates context allocated callee = .ok [])
    (argumentsAccepted : inferExprsFuel fuel context arguments.elements allocated = .ok (inferredArguments, argumentState))
    (indirect : SourceInferenceExecution.IndirectCalleeAt context callee argumentState)
    (calleeAccepted : inferExprFuel fuel context callee none argumentState = .ok (inferredCallee, calleeState))
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok result)
    (lifetime : GeneralizationLifetime event argumentState.inference.next calleeState [inferredCallee.type]) :
    GeneralizationLifetime event initial.inference.next result.2 [result.1.type] := by
  have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  have sameNext : allocated.inference.next = initial.inference.next := by rw [allocatedEq]; rfl
  have argumentsProperties := inferExprsFuel_inferenceProperties (allocatedEq ▸ ready.allocateExpressionId)
    catalog.formation catalog.canonical argumentsAccepted
  have calleeProperties := inferExprFuel_inferenceProperties argumentsProperties.2.1
    catalog.formation catalog.canonical (by simp) calleeAccepted
  obtain ⟨application, applicationAccepted, recorded⟩ :=
    SourceInferenceExecution.indirectCall_actual_suffix form allocation nonconstructor argumentsAccepted indirect calleeAccepted accepted
  have before : initial.inference.next ≤ argumentState.inference.next := sameNext ▸ argumentsProperties.1.next_le
  have completed := lifetime.indirect_callee_suffix calleeProperties.2.1 catalog calleeProperties.2.2
    (fun argument member => (argumentsProperties.2.2 argument member).weaken calleeProperties.1.next_le)
    (fun type member => (expectedBelow type member).weaken (Nat.le_trans before calleeProperties.1.next_le))
    argumentsProperties.2.2 (fun type member => (expectedBelow type member).weaken before)
    applicationAccepted recorded
  exact completed.weaken_entry before

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeConditional
/-! Each conditional child is followed by the original remaining calls and unifier. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}
    {fuel : Nat} {context : SourceInference.Context} {source condition thenBranch elseBranch : Syntax.Expr}
    {question colon : Syntax.SourceSpan} {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {conditionResult thenResult elseResult final : InferredExpression × State}

private theorem finishConditional
    {entryNext : Nat}
    (ready : elseResult.2.InferenceReady) (catalog : LifetimeInferenceContext context)
    (thenBelow : thenResult.1.type.VariablesBelow elseResult.2.inference.next)
    (elseBelow : elseResult.1.type.VariablesBelow elseResult.2.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow elseResult.2.inference.next)
    (expectedBefore : ∀ type ∈ expected, type.VariablesBelow entryNext)
    (form : source.value = .conditional condition question thenBranch colon elseBranch)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (thenAccepted : inferExprFuel fuel context thenBranch expected conditionResult.2 = .ok thenResult)
    (elseAccepted : inferExprFuel fuel context elseBranch expected thenResult.2 = .ok elseResult)
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok final)
    (lifetime : GeneralizationLifetime event entryNext elseResult.2 [thenResult.1.type, elseResult.1.type]) :
    GeneralizationLifetime event entryNext final.2 [final.1.type] := by
  unfold inferExprFuel at accepted
  simp only [allocation, form, conditionAccepted, thenAccepted, elseAccepted, bind, Except.bind] at accepted
  cases fitting : Detail.unify elseResult.2 thenResult.1.type elseResult.1.type with
  | error error => simp [fitting] at accepted
  | ok fitted =>
      have properties := unify_inferenceProgress ready.solved thenBelow elseBelow fitting
      have fittedReady := unify_preserves_inferenceReady ready thenBelow elseBelow fitting
      have after := lifetime.unify ready thenBelow elseBelow
        (lifetime.values _ (by simp)) (lifetime.values _ (by simp)) fitting
      have recorded : recordExpressionWithExpected context source id
          (fitted.resolve thenResult.1.type)
          (.conditional conditionResult.1.id thenResult.1.id elseResult.1.id) [] expected fitted = .ok final := by
        simpa only [fitting] using accepted
      have done := after.recordExpression catalog.catalog fittedReady
        (fittedReady.solved.variablesBelow_apply (thenBelow.weaken properties.next_le))
        (fun type member => (expectedBelow type member).weaken properties.next_le)
        (safe_resolved fittedReady (after.values _ (by simp)))
        (fun type member => after.older type (expectedBefore type member)) recorded
      exact done.restrict_outputs (by intro type member; exact List.mem_append_right _ member)

private theorem conditionalPrefix
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (thenAccepted : inferExprFuel fuel context thenBranch expected conditionResult.2 = .ok thenResult)
    (elseAccepted : inferExprFuel fuel context elseBranch expected thenResult.2 = .ok elseResult) :
    initial.InferenceProgress conditionResult.2 ∧ conditionResult.2.InferenceReady ∧
    conditionResult.2.InferenceProgress thenResult.2 ∧ thenResult.2.InferenceReady ∧
    thenResult.1.type.VariablesBelow thenResult.2.inference.next ∧
    thenResult.2.InferenceProgress elseResult.2 ∧ elseResult.2.InferenceReady ∧
    elseResult.1.type.VariablesBelow elseResult.2.inference.next := by
  have allocatedProgress := State.InferenceProgress.allocateExpressionId initial ready.solved
  have allocatedReady := ready.allocateExpressionId
  rw [allocation] at allocatedProgress allocatedReady
  have c := inferExprFuel_inferenceProperties allocatedReady catalog.formation catalog.canonical
    (by intro type member; cases member; exact Ty.variablesBelow_constructor _ _) conditionAccepted
  have first := allocatedProgress.trans c.1
  have t := inferExprFuel_inferenceProperties c.2.1 catalog.formation catalog.canonical
    (fun type member => (expectedBelow type member).weaken first.next_le) thenAccepted
  have e := inferExprFuel_inferenceProperties t.2.1 catalog.formation catalog.canonical
    (fun type member => (expectedBelow type member).weaken (first.trans t.1).next_le) elseAccepted
  exact ⟨first, c.2.1, t.1, t.2.1, t.2.2, e.1, e.2.1, e.2.2⟩

theorem conditional_else
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (form : source.value = .conditional condition question thenBranch colon elseBranch)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (thenAccepted : inferExprFuel fuel context thenBranch expected conditionResult.2 = .ok thenResult)
    (elseAccepted : inferExprFuel fuel context elseBranch expected thenResult.2 = .ok elseResult)
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok final)
    (lifetime : GeneralizationLifetime event thenResult.2.inference.next elseResult.2 [elseResult.1.type]) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  obtain ⟨throughCondition, _, throughThen, _, thenBelow, throughElse, elseReady, elseBelow⟩ :=
    conditionalPrefix ready catalog expectedBelow allocation conditionAccepted thenAccepted elseAccepted
  have both := lifetime.replaceOutputs (values := [thenResult.1.type, elseResult.1.type]) (by
    intro type member
    rcases List.mem_cons.mp member with rfl | member
    · exact lifetime.older _ thenBelow
    · exact lifetime.values _ member)
  have result := finishConditional elseReady catalog (thenBelow.weaken throughElse.next_le) elseBelow
    (fun type member => (expectedBelow type member).weaken ((throughCondition.trans throughThen).trans throughElse).next_le)
    (fun type member => (expectedBelow type member).weaken (throughCondition.trans throughThen).next_le)
    form allocation conditionAccepted thenAccepted elseAccepted accepted both
  exact result.weaken_entry (throughCondition.trans throughThen).next_le

theorem conditional_then
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (form : source.value = .conditional condition question thenBranch colon elseBranch)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (thenAccepted : inferExprFuel fuel context thenBranch expected conditionResult.2 = .ok thenResult)
    (elseAccepted : inferExprFuel fuel context elseBranch expected thenResult.2 = .ok elseResult)
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok final)
    (lifetime : GeneralizationLifetime event conditionResult.2.inference.next thenResult.2 [thenResult.1.type]) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  obtain ⟨throughCondition, _, throughThen, thenReady, thenBelow, throughElse, elseReady, elseBelow⟩ :=
    conditionalPrefix ready catalog expectedBelow allocation conditionAccepted thenAccepted elseAccepted
  have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  have allocatedWF : allocated.RequirementsWellFormed := by rw [allocatedEq]; exact wellFormed
  have thenWF := (inferExprFuel_direct_progress thenAccepted).wellFormed
    ((inferExprFuel_direct_progress conditionAccepted).wellFormed allocatedWF)
  have after := lifetime.inferExpr thenReady thenWF catalog
    (fun type member => (expectedBelow type member).weaken (throughCondition.trans throughThen).next_le)
    (fun type member => lifetime.older _ ((expectedBelow type member).weaken throughCondition.next_le)) elseAccepted
  have result := finishConditional elseReady catalog (thenBelow.weaken throughElse.next_le) elseBelow
    (fun type member => (expectedBelow type member).weaken ((throughCondition.trans throughThen).trans throughElse).next_le)
    (fun type member => (expectedBelow type member).weaken throughCondition.next_le)
    form allocation conditionAccepted thenAccepted elseAccepted accepted after
  exact result.weaken_entry throughCondition.next_le

theorem conditional_condition
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (form : source.value = .conditional condition question thenBranch colon elseBranch)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (thenAccepted : inferExprFuel fuel context thenBranch expected conditionResult.2 = .ok thenResult)
    (elseAccepted : inferExprFuel fuel context elseBranch expected thenResult.2 = .ok elseResult)
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok final)
    (lifetime : GeneralizationLifetime event allocated.inference.next conditionResult.2 [conditionResult.1.type]) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  obtain ⟨throughCondition, conditionReady, throughThen, thenReady, thenBelow, throughElse, elseReady, elseBelow⟩ :=
    conditionalPrefix ready catalog expectedBelow allocation conditionAccepted thenAccepted elseAccepted
  have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  have sameNext : allocated.inference.next = initial.inference.next := by rw [allocatedEq]; rfl
  have allocatedWF : allocated.RequirementsWellFormed := by rw [allocatedEq]; exact wellFormed
  have conditionWF := (inferExprFuel_direct_progress conditionAccepted).wellFormed allocatedWF
  have thenWF := (inferExprFuel_direct_progress thenAccepted).wellFormed conditionWF
  have afterThen := lifetime.inferExpr conditionReady conditionWF catalog
    (fun type member => (expectedBelow type member).weaken throughCondition.next_le)
    (fun type member => lifetime.older _ (sameNext ▸ expectedBelow type member)) thenAccepted
  have afterElse := afterThen.inferExpr thenReady thenWF catalog
    (fun type member => (expectedBelow type member).weaken (throughCondition.trans throughThen).next_le)
    (fun type member => afterThen.older _ (sameNext ▸ expectedBelow type member)) elseAccepted
  have both := afterElse.restrict_outputs (selected := [thenResult.1.type, elseResult.1.type]) (by simp)
  have result := finishConditional elseReady catalog (thenBelow.weaken throughElse.next_le) elseBelow
    (fun type member => (expectedBelow type member).weaken ((throughCondition.trans throughThen).trans throughElse).next_le)
    (fun type member => sameNext ▸ expectedBelow type member)
    form allocation conditionAccepted thenAccepted elseAccepted accepted both
  simpa only [sameNext] using result

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeConstructorSteps
/-! Constructor arguments preserve their actual left-to-right call order. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

theorem constructorArguments_head
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {sources : List Syntax.Expr} {expected : Ty} {expectedTypes : List Ty} {initial : State}
    {head : InferredExpression × State} {tail result : List InferredExpression × State}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected :: expectedTypes, type.VariablesBelow initial.inference.next)
    (headAccepted : inferExprFuel fuel context source (some (initial.resolve expected)) initial = .ok head)
    (tailAccepted : inferConstructorArgumentsFuel fuel context sources expectedTypes head.2 = .ok tail)
    (accepted : inferConstructorArgumentsFuel fuel context (source :: sources) (expected :: expectedTypes) initial = .ok result)
    (lifetime : GeneralizationLifetime event initial.inference.next head.2 [head.1.type]) :
    GeneralizationLifetime event initial.inference.next result.2 (result.1.map (·.type)) := by
  have headProperties := inferExprFuel_inferenceProperties ready catalog.formation catalog.canonical
    (by intro type member; cases member; exact ready.solved.variablesBelow_apply (expectedBelow _ (by simp))) headAccepted
  have after := lifetime.inferConstructorArguments headProperties.2.1
    ((inferExprFuel_direct_progress headAccepted).wellFormed wellFormed) catalog
    (fun type member => (expectedBelow type (List.mem_cons_of_mem _ member)).weaken headProperties.1.next_le)
    (fun type member => lifetime.older type (expectedBelow type (List.mem_cons_of_mem _ member))) tailAccepted
  have resultEq : (head.1 :: tail.1, tail.2) = result := by
    simpa only [inferConstructorArgumentsFuel, headAccepted, tailAccepted, bind, Except.bind,
      pure, Pure.pure, Except.pure, Except.ok.injEq] using accepted
  cases resultEq
  simpa only [List.map_cons, List.singleton_append] using after

theorem constructorArguments_tail
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {sources : List Syntax.Expr} {expected : Ty} {expectedTypes : List Ty} {initial : State}
    {head : InferredExpression × State} {tail result : List InferredExpression × State}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected :: expectedTypes, type.VariablesBelow initial.inference.next)
    (headAccepted : inferExprFuel fuel context source (some (initial.resolve expected)) initial = .ok head)
    (tailAccepted : inferConstructorArgumentsFuel fuel context sources expectedTypes head.2 = .ok tail)
    (accepted : inferConstructorArgumentsFuel fuel context (source :: sources) (expected :: expectedTypes) initial = .ok result)
    (lifetime : GeneralizationLifetime event head.2.inference.next tail.2 (tail.1.map (·.type))) :
    GeneralizationLifetime event initial.inference.next result.2 (result.1.map (·.type)) := by
  have headProperties := inferExprFuel_inferenceProperties ready catalog.formation catalog.canonical
    (by intro type member; cases member; exact ready.solved.variablesBelow_apply (expectedBelow _ (by simp))) headAccepted
  have resultEq : (head.1 :: tail.1, tail.2) = result := by
    simpa only [inferConstructorArgumentsFuel, headAccepted, tailAccepted, bind, Except.bind,
      pure, Pure.pure, Except.pure, Except.ok.injEq] using accepted
  cases resultEq
  have tailLifetime := lifetime.weaken_entry headProperties.1.next_le
  refine {tailLifetime with values := ?_}
  intro type member
  rcases List.mem_cons.mp member with rfl | member
  · exact lifetime.older _ headProperties.2.2
  · exact lifetime.values _ member

theorem constructorApplication_arguments
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {instantiation : DataConstructorInstantiation} {arguments : List Syntax.Expr} {expected : Option Ty}
    {initial fitted : State} {child : List InferredExpression × State} {result : InferredExpression × State}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (payloadBelow : ∀ type ∈ instantiation.payloadTypes, type.VariablesBelow initial.inference.next)
    (resultBelow : instantiation.resultType.VariablesBelow initial.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (fitting : (match expected with
      | none => Except.ok initial
      | some type => Detail.unify initial instantiation.resultType type) = .ok fitted)
    (childAccepted : inferConstructorArgumentsFuel fuel context arguments instantiation.payloadTypes fitted = .ok child)
    (accepted : inferConstructorApplicationFuel fuel context source id instantiation arguments expected initial = .ok result)
    (lifetime : GeneralizationLifetime event fitted.inference.next child.2 (child.1.map (·.type))) :
    GeneralizationLifetime event initial.inference.next result.2 [result.1.type] := by
  have fittingProperties : initial.InferenceProgress fitted ∧ fitted.InferenceReady := by
    cases expected with
    | none =>
        simp only [Except.ok.injEq] at fitting
        cases fitting
        exact ⟨.refl ready.solved, ready⟩
    | some type =>
        exact ⟨unify_inferenceProgress ready.solved resultBelow (expectedBelow _ (by simp)) fitting,
          unify_preserves_inferenceReady ready resultBelow (expectedBelow _ (by simp)) fitting⟩
  have childProperties := inferConstructorArgumentsFuel_inferenceProperties fittingProperties.2
    catalog.formation catalog.canonical
    (fun type member => (payloadBelow type member).weaken fittingProperties.1.next_le) childAccepted
  have recorded : recordExpressionWithExpected context source id
      (child.2.resolve instantiation.resultType) (.constructor instantiation (child.1.map (·.id))) [] expected child.2 = .ok result := by
    unfold inferConstructorApplicationFuel at accepted
    by_cases arity : arguments.length = instantiation.payloadTypes.length
    · cases expected with
      | none =>
          simp only [Except.ok.injEq] at fitting
          cases fitting
          simpa [arity, childAccepted, bind, Except.bind, pure, Pure.pure, Except.pure] using accepted
      | some type =>
          simpa [arity, fitting, childAccepted, bind, Except.bind] using accepted
    · simp [arity, bind, Except.bind] at accepted
  have after := lifetime.recordExpression catalog.catalog childProperties.2.1
    (childProperties.2.1.solved.variablesBelow_apply
      (resultBelow.weaken (fittingProperties.1.trans childProperties.1).next_le))
    (fun type member => (expectedBelow type member).weaken (fittingProperties.1.trans childProperties.1).next_le)
    (safe_resolved childProperties.2.1 (lifetime.older _ (resultBelow.weaken fittingProperties.1.next_le)))
    (fun type member => lifetime.older _ ((expectedBelow type member).weaken fittingProperties.1.next_le)) recorded
  exact (after.restrict_outputs (by intro type member; exact List.mem_append_right _ member)).weaken_entry
    fittingProperties.1.next_le

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeForLoopSteps
/-! An actual for receipt connects all four child calls through both saved scopes. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Block} {expected : Ty} {initial : State} {result : StatementResult}

private structure ForFacts
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt
      fuel context source initializers condition post body expected initial result) : Prop where
  initReady : receipt.initialized.state.InferenceReady
  initWF : receipt.initialized.state.RequirementsWellFormed
  initialToInit : initial.InferenceProgress receipt.initialized.state
  testReady : receipt.testState.InferenceReady
  testWF : receipt.testState.RequirementsWellFormed
  initialToTest : initial.InferenceProgress receipt.testState
  bodyWF : receipt.bodyResult.state.RequirementsWellFormed
  restoredReady : (receipt.bodyResult.state.restoreLexicalScope receipt.initialized.state.lexicalScope).InferenceReady
  initialToRestored : initial.InferenceProgress
    (receipt.bodyResult.state.restoreLexicalScope receipt.initialized.state.lexicalScope)

private theorem forFacts
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt
      fuel context source initializers condition post body expected initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (returnBelow : expected.VariablesBelow initial.inference.next) : ForFacts receipt := by
  have allocated := State.InferenceProgress.allocateStatementId initial ready.solved
  have initialized := inferForItemsFuel_inferenceProperties ready.allocateStatementId
    catalog.formation catalog.canonical receipt.initialization
  have initializedWF := (inferForItemsFuel_direct_progress receipt.initialization).wellFormed
    (show initial.allocateStatementId.2.RequirementsWellFormed from wellFormed)
  have test := inferExprFuel_inferenceProperties initialized.2 catalog.formation catalog.canonical
    (by intro type member; cases member; exact Ty.variablesBelow_constructor _ _) receipt.tested
  have testWF := (inferExprFuel_direct_progress receipt.tested).wellFormed initializedWF
  have throughTest := allocated.trans (initialized.1.trans test.1)
  have bodyProperties := inferStatementsFuel_inferenceProperties
    (context := SourceInference.ForStatementInferenceContinuation.loopContext context)
    test.2.1 catalog.formation catalog.canonical (returnBelow.weaken throughTest.next_le) receipt.bodyAccepted
  have bodyWF := (inferStatementsFuel_direct_progress receipt.bodyAccepted).wellFormed testWF
  have restored := State.restoreLexicalScope_inferenceProperties initialized.2
    (test.1.trans bodyProperties.1)
  exact ⟨initialized.2, initializedWF, allocated.trans initialized.1,
    test.2.1, testWF, throughTest, bodyWF, restored.2,
    allocated.trans (initialized.1.trans restored.1)⟩

theorem forLoop_after_post
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt
      fuel context source initializers condition post body expected initial result)
    {entryNext : Nat} {outputs : List Ty}
    (lifetime : GeneralizationLifetime event entryNext receipt.postResult.state outputs) :
    GeneralizationLifetime event entryNext result.state [result.type] := by
  have privacy := SourceInferenceSoundness.ProtectedVariables.ForStatementInferenceContinuation.Receipt.privacy_after_post
    receipt lifetime.live
  have nextEq := congrArg InferState.next receipt.inference_eq
  have resultType : result.type = .unit := congrArg StatementResult.type receipt.completed
  have atEnd := lifetime.append (newOutputs := [result.type]) (Nat.le_of_eq nextEq.symm)
    privacy.1 privacy.2.1 (by
      intro type member
      cases List.mem_singleton.mp member
      rw [resultType]
      exact safe_closed _ _ (Ty.variablesBelow_constructor 0 _)) privacy.2.2
  exact atEnd.restrict_outputs (by simp)

theorem forLoop_after_body
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt
      fuel context source initializers condition post body expected initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (returnBelow : expected.VariablesBelow initial.inference.next)
    {entryNext : Nat} {outputs : List Ty}
    (lifetime : GeneralizationLifetime event entryNext receipt.bodyResult.state outputs) :
    GeneralizationLifetime event entryNext result.state [result.type] := by
  have facts := forFacts receipt ready wellFormed catalog returnBelow
  have savedSubset : receipt.initialized.state.localBinders ⊆ receipt.bodyResult.state.localBinders := by
    have same := congrArg LexicalScope.binders (inferExprFuel_success_lexicalScope_eq receipt.tested)
    change receipt.testState.localBinders = receipt.initialized.state.localBinders at same
    rw [← same]
    exact inferStatementsFuel_binders_subset receipt.bodyAccepted
  have restored := lifetime.restoreScope receipt.initialized.state.lexicalScope savedSubset
  have after := restored.inferForItems facts.restoredReady facts.bodyWF
    (catalog.withLoopDepth (context.loopDepth + 1)) receipt.postAccepted
  exact forLoop_after_post receipt after

theorem forLoop_post
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt
      fuel context source initializers condition post body expected initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (returnBelow : expected.VariablesBelow initial.inference.next)
    (lifetime : GeneralizationLifetime event receipt.bodyResult.state.inference.next receipt.postResult.state []) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have facts := forFacts receipt ready wellFormed catalog returnBelow
  exact (forLoop_after_post receipt lifetime).weaken_entry facts.initialToRestored.next_le

theorem forLoop_body
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt
      fuel context source initializers condition post body expected initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (returnBelow : expected.VariablesBelow initial.inference.next)
    (lifetime : GeneralizationLifetime event receipt.testState.inference.next receipt.bodyResult.state [receipt.bodyResult.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have facts := forFacts receipt ready wellFormed catalog returnBelow
  exact (forLoop_after_body receipt ready wellFormed catalog returnBelow lifetime).weaken_entry
    facts.initialToTest.next_le

theorem forLoop_condition
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt
      fuel context source initializers condition post body expected initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (returnBelow : expected.VariablesBelow initial.inference.next)
    (lifetime : GeneralizationLifetime event receipt.initialized.state.inference.next receipt.testState [receipt.test.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have facts := forFacts receipt ready wellFormed catalog returnBelow
  have after := lifetime.inferStatements facts.testReady facts.testWF
    (catalog.withLoopDepth (context.loopDepth + 1))
    (returnBelow.weaken facts.initialToTest.next_le)
    (lifetime.older _ (returnBelow.weaken facts.initialToInit.next_le)) receipt.bodyAccepted
  exact (forLoop_after_body receipt ready wellFormed catalog returnBelow after).weaken_entry
    facts.initialToInit.next_le

theorem forLoop_initializer
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt
      fuel context source initializers condition post body expected initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (returnBelow : expected.VariablesBelow initial.inference.next)
    (lifetime : GeneralizationLifetime event initial.inference.next receipt.initialized.state []) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have facts := forFacts receipt ready wellFormed catalog returnBelow
  have tested := lifetime.inferExpr facts.initReady facts.initWF catalog
    (by intro type member; cases member; exact Ty.variablesBelow_constructor _ _)
    (by intro type member; cases member; exact safe_closed _ _ (Ty.variablesBelow_constructor 0 _)) receipt.tested
  have after := tested.inferStatements facts.testReady facts.testWF
    (catalog.withLoopDepth (context.loopDepth + 1))
    (returnBelow.weaken facts.initialToTest.next_le) (tested.older _ returnBelow) receipt.bodyAccepted
  exact forLoop_after_body receipt ready wellFormed catalog returnBelow after

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeIfSteps
/-! The two actual branches are sequenced through their real saved scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

private theorem finishIf
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {condition : Syntax.Expr} {thenBody elseBody : Syntax.Block} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {conditionResult : InferredExpression × State} {thenResult elseResult : BlockResult}
    {result : StatementResult} {entryNext : Nat} {outputs : List Ty}
    (form : source.value = .ifThen condition thenBody (some elseBody))
    (allocation : initial.allocateStatementId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (thenAccepted : inferStatementsFuel fuel context thenBody.value expectedReturn conditionResult.2 = .ok thenResult)
    (elseAccepted : inferStatementsFuel fuel context elseBody.value expectedReturn
      (thenResult.state.restoreLexicalScope conditionResult.2.lexicalScope) = .ok elseResult)
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event entryNext elseResult.state outputs)
    (returnSafe : Safe binder.scheme.quantified elseResult.state (elseResult.state.resolve expectedReturn)) :
    GeneralizationLifetime event entryNext result.state [result.type] := by
  have savedSubset : conditionResult.2.localBinders ⊆ elseResult.state.localBinders :=
    by simpa only [State.restoreLexicalScope, State.lexicalScope] using
      (inferStatementsFuel_binders_subset elseAccepted)
  have restored := lifetime.restoreScope conditionResult.2.lexicalScope savedSubset
  let type := if thenResult.sawReturn && elseResult.sawReturn then
    elseResult.state.resolve expectedReturn else .unit
  have recorded := restored.recordNode (.statement {
    id, span := source.span, type := type,
    form := .ifThen conditionResult.1.id thenResult.statements (some elseResult.statements)})
  have resultSafe : Safe binder.scheme.quantified
      ((elseResult.state.restoreLexicalScope conditionResult.2.lexicalScope).recordNode
        (.statement {
          id, span := source.span, type := type,
          form := .ifThen conditionResult.1.id thenResult.statements (some elseResult.statements)})) type := by
    dsimp only [type]
    split
    · exact returnSafe
    · exact safe_closed _ _ (Ty.variablesBelow_constructor 0 _)
  have final := recorded.replaceOutputs (by
    intro ty member
    cases List.mem_singleton.mp member
    exact resultSafe)
  unfold inferStatementFuel at accepted
  simp only [allocation, form, conditionAccepted, thenAccepted, elseAccepted,
    bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  exact final

private theorem prefixProperties
    {fuel : Nat} {context : SourceInference.Context}
    {condition : Syntax.Expr} {thenBody : Syntax.Block} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {conditionResult : InferredExpression × State} {thenResult : BlockResult}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (allocation : initial.allocateStatementId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (thenAccepted : inferStatementsFuel fuel context thenBody.value expectedReturn conditionResult.2 = .ok thenResult) :
    initial.InferenceProgress conditionResult.2 ∧ conditionResult.2.InferenceReady ∧
      conditionResult.2.InferenceProgress (thenResult.state.restoreLexicalScope conditionResult.2.lexicalScope) ∧
      (thenResult.state.restoreLexicalScope conditionResult.2.lexicalScope).InferenceReady := by
  have allocationProgress := State.InferenceProgress.allocateStatementId initial ready.solved
  have allocationReady := ready.allocateStatementId
  rw [allocation] at allocationProgress allocationReady
  have conditionProperties := inferExprFuel_inferenceProperties allocationReady
    catalog.formation catalog.canonical (by
      intro ty member; cases member; exact Ty.variablesBelow_constructor _ _) conditionAccepted
  have before := allocationProgress.trans conditionProperties.1
  have thenProperties := inferStatementsFuel_inferenceProperties conditionProperties.2.1
    catalog.formation catalog.canonical (returnBelow.weaken before.next_le) thenAccepted
  have restored := State.restoreLexicalScope_inferenceProperties conditionProperties.2.1 thenProperties.1
  exact ⟨before, conditionProperties.2.1, restored.1, restored.2⟩

theorem if_with_else_else
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {condition : Syntax.Expr} {thenBody elseBody : Syntax.Block} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {conditionResult : InferredExpression × State} {thenResult elseResult : BlockResult}
    {result : StatementResult}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (form : source.value = .ifThen condition thenBody (some elseBody))
    (allocation : initial.allocateStatementId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (thenAccepted : inferStatementsFuel fuel context thenBody.value expectedReturn conditionResult.2 = .ok thenResult)
    (elseAccepted : inferStatementsFuel fuel context elseBody.value expectedReturn
      (thenResult.state.restoreLexicalScope conditionResult.2.lexicalScope) = .ok elseResult)
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event thenResult.state.inference.next elseResult.state [elseResult.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have beforeProperties := prefixProperties ready catalog returnBelow allocation conditionAccepted thenAccepted
  have throughThen := beforeProperties.1.trans beforeProperties.2.2.1
  have elseProperties := inferStatementsFuel_inferenceProperties beforeProperties.2.2.2
    catalog.formation catalog.canonical (returnBelow.weaken throughThen.next_le) elseAccepted
  have safe := safe_resolved elseProperties.2.1
    (lifetime.older _ (returnBelow.weaken throughThen.next_le))
  exact (finishIf form allocation conditionAccepted thenAccepted elseAccepted accepted lifetime safe).weaken_entry
    throughThen.next_le

theorem if_with_else_then
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {condition : Syntax.Expr} {thenBody elseBody : Syntax.Block} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {conditionResult : InferredExpression × State} {thenResult elseResult : BlockResult}
    {result : StatementResult}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (form : source.value = .ifThen condition thenBody (some elseBody))
    (allocation : initial.allocateStatementId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (thenAccepted : inferStatementsFuel fuel context thenBody.value expectedReturn conditionResult.2 = .ok thenResult)
    (elseAccepted : inferStatementsFuel fuel context elseBody.value expectedReturn
      (thenResult.state.restoreLexicalScope conditionResult.2.lexicalScope) = .ok elseResult)
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event conditionResult.2.inference.next thenResult.state [thenResult.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have beforeProperties := prefixProperties ready catalog returnBelow allocation conditionAccepted thenAccepted
  have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  have allocatedWF : allocated.RequirementsWellFormed := by
    rw [allocatedEq]; change initial.RequirementsWellFormed; exact wellFormed
  have conditionWF := (inferExprFuel_direct_progress conditionAccepted).wellFormed allocatedWF
  have thenWF := (inferStatementsFuel_direct_progress thenAccepted).wellFormed conditionWF
  have restored := lifetime.restoreScope conditionResult.2.lexicalScope
    (inferStatementsFuel_binders_subset thenAccepted)
  have after := restored.inferStatements beforeProperties.2.2.2 thenWF catalog
    (returnBelow.weaken (beforeProperties.1.trans beforeProperties.2.2.1).next_le)
    (restored.older _ (returnBelow.weaken beforeProperties.1.next_le)) elseAccepted
  have elseProperties := inferStatementsFuel_inferenceProperties beforeProperties.2.2.2
    catalog.formation catalog.canonical
    (returnBelow.weaken (beforeProperties.1.trans beforeProperties.2.2.1).next_le) elseAccepted
  have safe := safe_resolved elseProperties.2.1
    (after.older _ (returnBelow.weaken beforeProperties.1.next_le))
  exact (finishIf form allocation conditionAccepted thenAccepted elseAccepted accepted after safe).weaken_entry
    beforeProperties.1.next_le

theorem if_with_else_condition
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {condition : Syntax.Expr} {thenBody elseBody : Syntax.Block} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {conditionResult : InferredExpression × State} {thenResult elseResult : BlockResult}
    {result : StatementResult}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (form : source.value = .ifThen condition thenBody (some elseBody))
    (allocation : initial.allocateStatementId = (id, allocated))
    (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok conditionResult)
    (thenAccepted : inferStatementsFuel fuel context thenBody.value expectedReturn conditionResult.2 = .ok thenResult)
    (elseAccepted : inferStatementsFuel fuel context elseBody.value expectedReturn
      (thenResult.state.restoreLexicalScope conditionResult.2.lexicalScope) = .ok elseResult)
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (lifetime : GeneralizationLifetime event allocated.inference.next conditionResult.2 [conditionResult.1.type]) :
    GeneralizationLifetime event initial.inference.next result.state [result.type] := by
  have beforeProperties := prefixProperties ready catalog returnBelow allocation conditionAccepted thenAccepted
  have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  have sameNext : allocated.inference.next = initial.inference.next := by rw [allocatedEq]; rfl
  have allocatedWF : allocated.RequirementsWellFormed := by
    rw [allocatedEq]; change initial.RequirementsWellFormed; exact wellFormed
  have conditionWF := (inferExprFuel_direct_progress conditionAccepted).wellFormed allocatedWF
  have thenWF := (inferStatementsFuel_direct_progress thenAccepted).wellFormed conditionWF
  have afterThen := lifetime.inferStatements beforeProperties.2.1 conditionWF catalog
    (returnBelow.weaken beforeProperties.1.next_le) (lifetime.older _ (sameNext ▸ returnBelow)) thenAccepted
  have restored := afterThen.restoreScope conditionResult.2.lexicalScope
    (inferStatementsFuel_binders_subset thenAccepted)
  have after := restored.inferStatements beforeProperties.2.2.2 thenWF catalog
    (returnBelow.weaken (beforeProperties.1.trans beforeProperties.2.2.1).next_le)
    (restored.older _ (sameNext ▸ returnBelow)) elseAccepted
  have elseProperties := inferStatementsFuel_inferenceProperties beforeProperties.2.2.2
    catalog.formation catalog.canonical
    (returnBelow.weaken (beforeProperties.1.trans beforeProperties.2.2.1).next_le) elseAccepted
  have safe := safe_resolved elseProperties.2.1 (after.older _ (sameNext ▸ returnBelow))
  have resultLifetime := finishIf form allocation conditionAccepted thenAccepted elseAccepted accepted after safe
  rw [sameNext] at resultLifetime
  exact resultLifetime

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeIndex
/-! Mapping index inference retains events created by either the base or the
key through its actual fresh variables, mapping unification and recording. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}
    {fuel : Nat} {context : SourceInference.Context}
    {source base key : Syntax.Expr} {brackets : Syntax.SourceSpan}
    {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {baseResult keyResult : InferredExpression}
    {baseState keyState valueState mappingState indexState : State}
    {keyType valueType : Ty} {final : InferredExpression × State}

theorem index_base
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (form : source.value = .index base brackets key)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (baseAccepted : inferExprFuel fuel context base none allocated = .ok (baseResult, baseState))
    (keyFresh : baseState.fresh = (keyType, keyState))
    (valueFresh : keyState.fresh = (valueType, valueState))
    (mappingAccepted : Detail.unify valueState baseResult.type (.mapping keyType valueType) = .ok mappingState)
    (keyAccepted : inferExprFuel fuel context key (some (mappingState.resolve keyType)) mappingState =
      .ok (keyResult, indexState))
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok final)
    (lifetime : GeneralizationLifetime event allocated.inference.next baseState [baseResult.type]) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  have allocatedEq : allocated = initial.allocateExpressionId.2 :=
    (congrArg Prod.snd allocation).symm
  have sameNext : allocated.inference.next = initial.inference.next := by
    rw [allocatedEq]; rfl
  have lifetime : GeneralizationLifetime event initial.inference.next baseState [baseResult.type] := by
    simpa only [sameNext] using lifetime
  have baseProperties := inferExprFuel_inferenceProperties
    (allocatedEq ▸ ready.allocateExpressionId) catalog.formation catalog.canonical (by simp) baseAccepted
  have keyProperties := fresh_eq_inferenceProperties baseProperties.2.1 keyFresh
  have valueProperties := fresh_eq_inferenceProperties keyProperties.2.1 valueFresh
  have keyLife : GeneralizationLifetime event initial.inference.next keyState [baseResult.type, keyType] := by
    simpa only [keyFresh, List.singleton_append] using lifetime.fresh baseProperties.2.1
  have valueLife : GeneralizationLifetime event initial.inference.next valueState
      [baseResult.type, keyType, valueType] := by
    simpa only [valueFresh, List.cons_append, List.nil_append] using keyLife.fresh keyProperties.2.1
  have baseBelow := baseProperties.2.2.weaken (keyProperties.1.trans valueProperties.1).next_le
  have keyBelow := keyProperties.2.2.weaken valueProperties.1.next_le
  have mappingBelow := (Ty.variablesBelow_mapping_iff _ _ _).2 ⟨keyBelow, valueProperties.2.2⟩
  have mappingReady := unify_preserves_inferenceReady valueProperties.2.1 baseBelow mappingBelow mappingAccepted
  have mappingProgress := unify_inferenceProgress valueProperties.2.1.solved baseBelow mappingBelow mappingAccepted
  have mappingLife := valueLife.unify valueProperties.2.1 baseBelow mappingBelow
    (valueLife.values _ (by simp))
    ((safe_mapping_iff _ _ _ _).2 ⟨valueLife.values _ (by simp), valueLife.values _ (by simp)⟩)
    mappingAccepted
  have allocatedWellFormed : allocated.RequirementsWellFormed := by
    rw [allocatedEq]
    exact wellFormed
  have baseWellFormed := (inferExprFuel_direct_progress baseAccepted).wellFormed allocatedWellFormed
  have valueWellFormed : valueState.RequirementsWellFormed := by
    rw [← show keyState.fresh.2 = valueState from congrArg Prod.snd valueFresh,
      ← show baseState.fresh.2 = keyState from congrArg Prod.snd keyFresh]
    exact baseWellFormed
  have mappingWellFormed := unify_preserves_requirementsWellFormed mappingAccepted valueWellFormed
  have resolvedKeyBelow := mappingReady.solved.variablesBelow_apply (keyBelow.weaken mappingProgress.next_le)
  have keyExpected : ∀ type ∈ (some (mappingState.resolve keyType) : Option Ty),
      type.VariablesBelow mappingState.inference.next := by
    intro type member
    cases Option.some.inj (Option.mem_def.mp member)
    exact resolvedKeyBelow
  have keySafe : ∀ type ∈ (some (mappingState.resolve keyType) : Option Ty),
      Safe binder.scheme.quantified mappingState type := by
    intro type member
    cases Option.some.inj (Option.mem_def.mp member)
    exact safe_resolved mappingReady (mappingLife.values _ (by simp))
  have indexProperties := inferExprFuel_inferenceProperties mappingReady
    catalog.formation catalog.canonical keyExpected keyAccepted
  have indexLife := mappingLife.inferExpr mappingReady mappingWellFormed catalog
    keyExpected keySafe keyAccepted
  have valueBelow := valueProperties.2.2.weaken
    (Nat.le_trans mappingProgress.next_le indexProperties.1.next_le)
  have prefixProgress := baseProperties.1.trans (keyProperties.1.trans
    (valueProperties.1.trans (mappingProgress.trans indexProperties.1)))
  have recorded : recordExpressionWithExpected context source id (indexState.resolve valueType)
      (.index baseResult.id keyResult.id) [] expected indexState = .ok final := by
    simpa only [inferExprFuel, allocation, form, baseAccepted, keyFresh, valueFresh,
      mappingAccepted, keyAccepted, bind, Except.bind] using accepted
  have finalLife := indexLife.recordExpression catalog.catalog indexProperties.2.1
    (indexProperties.2.1.solved.variablesBelow_apply valueBelow)
    (fun type member => (sameNext ▸ expectedBelow type member).weaken prefixProgress.next_le)
    (safe_resolved indexProperties.2.1 (indexLife.values _ (by simp)))
    (fun type member => indexLife.older type (expectedBelow type member)) recorded
  exact finalLife.restrict_outputs (by intro type member; exact List.mem_append_right _ member)

theorem index_key
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (form : source.value = .index base brackets key)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (baseAccepted : inferExprFuel fuel context base none allocated = .ok (baseResult, baseState))
    (keyFresh : baseState.fresh = (keyType, keyState))
    (valueFresh : keyState.fresh = (valueType, valueState))
    (mappingAccepted : Detail.unify valueState baseResult.type (.mapping keyType valueType) = .ok mappingState)
    (keyAccepted : inferExprFuel fuel context key (some (mappingState.resolve keyType)) mappingState =
      .ok (keyResult, indexState))
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok final)
    (lifetime : GeneralizationLifetime event mappingState.inference.next indexState [keyResult.type]) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  have allocatedEq : allocated = initial.allocateExpressionId.2 :=
    (congrArg Prod.snd allocation).symm
  have sameNext : allocated.inference.next = initial.inference.next := by
    rw [allocatedEq]; rfl
  have baseProperties := inferExprFuel_inferenceProperties
    (allocatedEq ▸ ready.allocateExpressionId) catalog.formation catalog.canonical (by simp) baseAccepted
  have keyProperties := fresh_eq_inferenceProperties baseProperties.2.1 keyFresh
  have valueProperties := fresh_eq_inferenceProperties keyProperties.2.1 valueFresh
  have baseBelow := baseProperties.2.2.weaken (keyProperties.1.trans valueProperties.1).next_le
  have keyBelow := keyProperties.2.2.weaken valueProperties.1.next_le
  have mappingBelow := (Ty.variablesBelow_mapping_iff _ _ _).2 ⟨keyBelow, valueProperties.2.2⟩
  have mappingReady := unify_preserves_inferenceReady valueProperties.2.1 baseBelow mappingBelow mappingAccepted
  have mappingProgress := unify_inferenceProgress valueProperties.2.1.solved baseBelow mappingBelow mappingAccepted
  have resolvedKeyBelow := mappingReady.solved.variablesBelow_apply (keyBelow.weaken mappingProgress.next_le)
  have keyExpected : ∀ type ∈ (some (mappingState.resolve keyType) : Option Ty),
      type.VariablesBelow mappingState.inference.next := by
    intro type member
    cases Option.some.inj (Option.mem_def.mp member)
    exact resolvedKeyBelow
  have indexProperties := inferExprFuel_inferenceProperties mappingReady
    catalog.formation catalog.canonical keyExpected keyAccepted
  have prefixProgress := baseProperties.1.trans
    (keyProperties.1.trans (valueProperties.1.trans mappingProgress))
  have valueAtMapping := valueProperties.2.2.weaken mappingProgress.next_le
  have valueSafe := lifetime.older valueType valueAtMapping
  have indexLife := lifetime.weaken_entry (sameNext ▸ prefixProgress.next_le)
  have recorded : recordExpressionWithExpected context source id (indexState.resolve valueType)
      (.index baseResult.id keyResult.id) [] expected indexState = .ok final := by
    simpa only [inferExprFuel, allocation, form, baseAccepted, keyFresh, valueFresh,
      mappingAccepted, keyAccepted, bind, Except.bind] using accepted
  have finalLife := indexLife.recordExpression catalog.catalog indexProperties.2.1
    (indexProperties.2.1.solved.variablesBelow_apply (valueAtMapping.weaken indexProperties.1.next_le))
    (fun type member => (sameNext ▸ expectedBelow type member).weaken
      (Nat.le_trans prefixProgress.next_le indexProperties.1.next_le))
    (safe_resolved indexProperties.2.1 valueSafe)
    (fun type member => indexLife.older type (expectedBelow type member)) recorded
  exact finalLife.restrict_outputs (by intro type member; exact List.mem_append_right _ member)

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeMatchCases
/-! Match-arm events follow the real pattern, scope restoration and remaining arms. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}
    {fuel : Nat} {context : SourceInference.Context} {scrutinee expectedReturn : Ty}
    {saved : LexicalScope} {arm : Syntax.MatchCase} {rest : List Syntax.MatchCase}
    {initial patternState : State} {pattern : TypedMatchPattern} {body : BlockResult}
    {tail result : MatchCasesResult}

private theorem resultState
    (patternAccepted : inferMatchPatternFuel fuel context arm.value.pattern scrutinee initial = .ok (pattern, patternState))
    (bodyAccepted : inferStatementsFuel fuel context arm.value.body.value expectedReturn patternState = .ok body)
    (tailAccepted : inferMatchCasesFuel fuel context scrutinee expectedReturn saved rest
      (body.state.restoreLexicalScope saved) = .ok tail)
    (accepted : inferMatchCasesFuel (fuel + 1) context scrutinee expectedReturn saved (arm :: rest) initial = .ok result) :
    result.state = tail.state := by
  unfold inferMatchCasesFuel at accepted
  simp only [patternAccepted, bodyAccepted, tailAccepted, bind, Except.bind,
    pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  exact (congrArg MatchCasesResult.state accepted).symm

theorem matchCases_body
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (scrutineeBelow : scrutinee.VariablesBelow initial.inference.next)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (scope : initial.lexicalScope = saved)
    (patternAccepted : inferMatchPatternFuel fuel context arm.value.pattern scrutinee initial = .ok (pattern, patternState))
    (bodyAccepted : inferStatementsFuel fuel context arm.value.body.value expectedReturn patternState = .ok body)
    (tailAccepted : inferMatchCasesFuel fuel context scrutinee expectedReturn saved rest
      (body.state.restoreLexicalScope saved) = .ok tail)
    (accepted : inferMatchCasesFuel (fuel + 1) context scrutinee expectedReturn saved (arm :: rest) initial = .ok result)
    (lifetime : GeneralizationLifetime event patternState.inference.next body.state [body.type]) :
    GeneralizationLifetime event initial.inference.next result.state [] := by
  have patternProperties := inferMatchPatternFuel_inferenceProperties ready scrutineeBelow catalog.formation patternAccepted
  have bodyProperties := inferStatementsFuel_inferenceProperties patternProperties.2.1 catalog.formation catalog.canonical
    (returnBelow.weaken patternProperties.1.next_le) bodyAccepted
  have throughBody := patternProperties.1.trans bodyProperties.1
  have restoredProperties := State.restoreLexicalScope_inferenceProperties ready throughBody
  have savedSubset : saved.binders ⊆ body.state.localBinders := by
    rw [← scope]
    exact (inferMatchPatternFuel_scope patternAccepted).retained.trans
      (inferStatementsFuel_binders_subset bodyAccepted)
  have restored := lifetime.restoreScope saved savedSubset
  have bodyWF := (inferStatementsFuel_direct_progress bodyAccepted).wellFormed
    ((inferMatchPatternFuel_direct_progress patternAccepted).wellFormed wellFormed)
  have after := restored.inferMatchCases
    (scope ▸ restoredProperties.2) bodyWF catalog
    (scrutineeBelow.weaken throughBody.next_le)
    (restored.older _ (scrutineeBelow.weaken patternProperties.1.next_le))
    (returnBelow.weaken throughBody.next_le)
    (restored.older _ (returnBelow.weaken patternProperties.1.next_le)) (by rfl) tailAccepted
  rw [resultState patternAccepted bodyAccepted tailAccepted accepted]
  exact (after.restrict_outputs (by simp)).weaken_entry patternProperties.1.next_le

theorem matchCases_tail
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (scrutineeBelow : scrutinee.VariablesBelow initial.inference.next)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (_scope : initial.lexicalScope = saved)
    (patternAccepted : inferMatchPatternFuel fuel context arm.value.pattern scrutinee initial = .ok (pattern, patternState))
    (bodyAccepted : inferStatementsFuel fuel context arm.value.body.value expectedReturn patternState = .ok body)
    (tailAccepted : inferMatchCasesFuel fuel context scrutinee expectedReturn saved rest
      (body.state.restoreLexicalScope saved) = .ok tail)
    (accepted : inferMatchCasesFuel (fuel + 1) context scrutinee expectedReturn saved (arm :: rest) initial = .ok result)
    (lifetime : GeneralizationLifetime event body.state.inference.next tail.state []) :
    GeneralizationLifetime event initial.inference.next result.state [] := by
  have patternProperties := inferMatchPatternFuel_inferenceProperties ready scrutineeBelow catalog.formation patternAccepted
  have bodyProperties := inferStatementsFuel_inferenceProperties patternProperties.2.1 catalog.formation catalog.canonical
    (returnBelow.weaken patternProperties.1.next_le) bodyAccepted
  rw [resultState patternAccepted bodyAccepted tailAccepted accepted]
  exact lifetime.weaken_entry (patternProperties.1.trans bodyProperties.1).next_le

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeMatchCompletion
/-! Events in actual match arms and defaults survive the remaining match suffix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail SourceInferenceExecution
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

theorem match_after_cases
    {entryNext fuel : Nat} {context : SourceInference.Context}
    {statement : Syntax.Statement} {id : StatementId} {hidden : Resolved.LocalId}
    {scrutinee : InferredExpression} {arms : Syntax.MatchArms} {expectedReturn : Ty}
    {state : State} {checked : MatchCasesResult} {result : StatementResult} {outputs : List Ty}
    (ready : state.InferenceReady) (wellFormed : state.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (scrutineeBelow : scrutinee.type.VariablesBelow state.inference.next)
    (returnBelow : expectedReturn.VariablesBelow state.inference.next)
    (returnBefore : expectedReturn.VariablesBelow entryNext)
    (casesAccepted : inferMatchCasesFuel fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state = .ok checked)
    (accepted : matchCompletion fuel context statement id hidden scrutinee arms expectedReturn state = .ok result)
    (lifetime : GeneralizationLifetime event entryNext checked.state outputs) :
    GeneralizationLifetime event entryNext result.state [result.type] := by
  have casesProperties := inferMatchCasesFuel_inferenceProperties ready catalog.formation catalog.canonical
    scrutineeBelow returnBelow rfl casesAccepted
  unfold matchCompletion at accepted
  simp only [casesAccepted, bind, Except.bind] at accepted
  cases defaultEq : arms.value.defaultBody with
  | none =>
      simp only [defaultEq, pure, Pure.pure, Except.pure] at accepted
      split at accepted
      · cases accepted
      · injection accepted with resultEq
        subst result
        refine (lifetime.recordNode _).replaceOutputs ?_
        intro type member
        cases List.mem_singleton.mp member
        split
        · exact (show Safe binder.scheme.quantified checked.state (checked.state.resolve expectedReturn) from safe_resolved casesProperties.2.1 (lifetime.older _ returnBefore))
        · exact safe_closed _ _ (Ty.variablesBelow_constructor _ _)
  | some body =>
      cases bodyAccepted : inferStatementsFuel fuel context body.value expectedReturn checked.state with
      | error error => simp [defaultEq, bodyAccepted] at accepted
      | ok bodyResult =>
          have bodyProperties := inferStatementsFuel_inferenceProperties casesProperties.2.1 catalog.formation catalog.canonical
            (returnBelow.weaken casesProperties.1.next_le) bodyAccepted
          have bodyLife := lifetime.inferStatements casesProperties.2.1
            ((inferMatchCasesFuel_direct_progress casesAccepted).wellFormed wellFormed) catalog
            (returnBelow.weaken casesProperties.1.next_le) (lifetime.older _ returnBefore) bodyAccepted
          have savedSubset : state.localBinders ⊆ bodyResult.state.localBinders := by
            have same : checked.state.localBinders = state.localBinders := congrArg LexicalScope.binders casesProperties.2.2
            rw [← same]
            exact inferStatementsFuel_binders_subset bodyAccepted
          have restored := bodyLife.restoreScope state.lexicalScope savedSubset
          have restoredReady := (State.restoreLexicalScope_inferenceProperties ready
            (casesProperties.1.trans bodyProperties.1)).2
          simp only [defaultEq, bodyAccepted, pure, Pure.pure, Except.pure] at accepted
          split at accepted
          · cases accepted
          · injection accepted with resultEq
            subst result
            refine (restored.recordNode _).replaceOutputs ?_
            intro type member
            cases List.mem_singleton.mp member
            split
            · exact (show Safe binder.scheme.quantified (bodyResult.state.restoreLexicalScope state.lexicalScope) ((bodyResult.state.restoreLexicalScope state.lexicalScope).resolve expectedReturn) from safe_resolved restoredReady (restored.older _ returnBefore))
            · exact safe_closed _ _ (Ty.variablesBelow_constructor _ _)

theorem match_after_default
    {fuel : Nat} {context : SourceInference.Context}
    {statement : Syntax.Statement} {id : StatementId} {hidden : Resolved.LocalId}
    {scrutinee : InferredExpression} {arms : Syntax.MatchArms} {expectedReturn : Ty}
    {state : State} {checked : MatchCasesResult} {body : Syntax.Block}
    {bodyResult : BlockResult} {result : StatementResult}
    (ready : state.InferenceReady) (catalog : LifetimeInferenceContext context)
    (scrutineeBelow : scrutinee.type.VariablesBelow state.inference.next)
    (returnBelow : expectedReturn.VariablesBelow state.inference.next)
    (casesAccepted : inferMatchCasesFuel fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state = .ok checked)
    (defaultEq : arms.value.defaultBody = some body)
    (bodyAccepted : inferStatementsFuel fuel context body.value expectedReturn checked.state = .ok bodyResult)
    (accepted : matchCompletion fuel context statement id hidden scrutinee arms expectedReturn state = .ok result)
    (lifetime : GeneralizationLifetime event checked.state.inference.next bodyResult.state [bodyResult.type]) :
    GeneralizationLifetime event state.inference.next result.state [result.type] := by
  have casesProperties := inferMatchCasesFuel_inferenceProperties ready catalog.formation catalog.canonical
    scrutineeBelow returnBelow rfl casesAccepted
  have bodyProperties := inferStatementsFuel_inferenceProperties casesProperties.2.1 catalog.formation catalog.canonical
    (returnBelow.weaken casesProperties.1.next_le) bodyAccepted
  have savedSubset : state.localBinders ⊆ bodyResult.state.localBinders := by
    have same : checked.state.localBinders = state.localBinders := congrArg LexicalScope.binders casesProperties.2.2
    rw [← same]
    exact inferStatementsFuel_binders_subset bodyAccepted
  have restored := (lifetime.restoreScope state.lexicalScope savedSubset).weaken_entry casesProperties.1.next_le
  have restoredReady := (State.restoreLexicalScope_inferenceProperties ready
    (casesProperties.1.trans bodyProperties.1)).2
  unfold matchCompletion at accepted
  simp only [casesAccepted, defaultEq, bodyAccepted, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
  split at accepted
  · cases accepted
  · injection accepted with resultEq
    subst result
    refine (restored.recordNode _).replaceOutputs ?_
    intro type member
    cases List.mem_singleton.mp member
    split
    · exact (show Safe binder.scheme.quantified (bodyResult.state.restoreLexicalScope state.lexicalScope) ((bodyResult.state.restoreLexicalScope state.lexicalScope).resolve expectedReturn) from safe_resolved restoredReady (restored.older _ returnBelow))
    · exact safe_closed _ _ (Ty.variablesBelow_constructor _ _)

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimePlace
/-! Assignable mapping places retain events from their base and key through
the actual fresh variables and mapping unification. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}
    {fuel : Nat} {context : SourceInference.Context}
    {source base key : Syntax.Expr} {brackets : Syntax.SourceSpan}
    {initial : State}
    {baseResult : PlaceResolution} {keyResult : InferredExpression}
    {baseState keyState valueState mappingState indexState : State}
    {keyType valueType : Ty} {final : PlaceResolution × State}

theorem place_group
    {inner : Syntax.Expr} {child : PlaceResolution × State}
    (form : source.value = .group inner)
    (childAccepted : inferPlaceFuel fuel context inner initial = .ok child)
    (accepted : inferPlaceFuel (fuel + 1) context source initial = .ok final)
    (lifetime : GeneralizationLifetime event initial.inference.next child.2 [child.1.type]) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  have same : child = final := by simpa only [inferPlaceFuel, form, Except.ok.injEq, childAccepted] using accepted
  cases same
  exact lifetime

theorem place_index_base
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (form : source.value = .index base brackets key)
    (baseAccepted : inferPlaceFuel fuel context base initial = .ok (baseResult, baseState))
    (keyFresh : baseState.fresh = (keyType, keyState))
    (valueFresh : keyState.fresh = (valueType, valueState))
    (mappingAccepted : Detail.unify valueState baseResult.type (.mapping keyType valueType) = .ok mappingState)
    (keyAccepted : inferExprFuel fuel context key (some (mappingState.resolve keyType)) mappingState =
      .ok (keyResult, indexState))
    (accepted : inferPlaceFuel (fuel + 1) context source initial = .ok final)
    (lifetime : GeneralizationLifetime event initial.inference.next baseState [baseResult.type]) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  have baseProperties := inferPlaceFuel_inferenceProperties ready catalog.formation catalog.canonical baseAccepted
  have keyProperties := fresh_eq_inferenceProperties baseProperties.2.1 keyFresh
  have valueProperties := fresh_eq_inferenceProperties keyProperties.2.1 valueFresh
  have keyLife : GeneralizationLifetime event initial.inference.next keyState [baseResult.type, keyType] := by
    simpa only [keyFresh, List.singleton_append] using lifetime.fresh baseProperties.2.1
  have valueLife : GeneralizationLifetime event initial.inference.next valueState
      [baseResult.type, keyType, valueType] := by
    simpa only [valueFresh, List.cons_append, List.nil_append] using keyLife.fresh keyProperties.2.1
  have baseBelow := baseProperties.2.2.weaken (keyProperties.1.trans valueProperties.1).next_le
  have keyBelow := keyProperties.2.2.weaken valueProperties.1.next_le
  have mappingBelow := (Ty.variablesBelow_mapping_iff _ _ _).2 ⟨keyBelow, valueProperties.2.2⟩
  have mappingReady := unify_preserves_inferenceReady valueProperties.2.1 baseBelow mappingBelow mappingAccepted
  have mappingProgress := unify_inferenceProgress valueProperties.2.1.solved baseBelow mappingBelow mappingAccepted
  have mappingLife := valueLife.unify valueProperties.2.1 baseBelow mappingBelow
    (valueLife.values _ (by simp))
    ((safe_mapping_iff _ _ _ _).2 ⟨valueLife.values _ (by simp), valueLife.values _ (by simp)⟩)
    mappingAccepted
  have baseWellFormed := (inferPlaceFuel_direct_progress baseAccepted).wellFormed wellFormed
  have valueWellFormed : valueState.RequirementsWellFormed := by
    rw [← show keyState.fresh.2 = valueState from congrArg Prod.snd valueFresh,
      ← show baseState.fresh.2 = keyState from congrArg Prod.snd keyFresh]
    exact baseWellFormed
  have mappingWellFormed := unify_preserves_requirementsWellFormed mappingAccepted valueWellFormed
  have resolvedKeyBelow := mappingReady.solved.variablesBelow_apply (keyBelow.weaken mappingProgress.next_le)
  have keyExpected : ∀ type ∈ (some (mappingState.resolve keyType) : Option Ty),
      type.VariablesBelow mappingState.inference.next := by
    intro type member
    cases Option.some.inj (Option.mem_def.mp member)
    exact resolvedKeyBelow
  have keySafe : ∀ type ∈ (some (mappingState.resolve keyType) : Option Ty),
      Safe binder.scheme.quantified mappingState type := by
    intro type member
    cases Option.some.inj (Option.mem_def.mp member)
    exact safe_resolved mappingReady (mappingLife.values _ (by simp))
  have indexProperties := inferExprFuel_inferenceProperties mappingReady
    catalog.formation catalog.canonical keyExpected keyAccepted
  have indexLife := mappingLife.inferExpr mappingReady mappingWellFormed catalog
    keyExpected keySafe keyAccepted
  have resultEq : ({baseResult with
      projections := baseResult.projections ++ [.index keyResult.id]
      type := indexState.resolve valueType}, indexState) = final := by
    simpa only [inferPlaceFuel, form, baseAccepted, keyFresh, valueFresh,
      mappingAccepted, keyAccepted, bind, Except.bind, pure, Pure.pure, Except.pure,
      Except.ok.injEq] using accepted
  cases resultEq
  exact indexLife.replaceOutputs (by
    intro type member
    cases List.mem_singleton.mp member
    exact safe_resolved indexProperties.2.1 (indexLife.values _ (by simp)))

theorem place_index_key
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (form : source.value = .index base brackets key)
    (baseAccepted : inferPlaceFuel fuel context base initial = .ok (baseResult, baseState))
    (keyFresh : baseState.fresh = (keyType, keyState))
    (valueFresh : keyState.fresh = (valueType, valueState))
    (mappingAccepted : Detail.unify valueState baseResult.type (.mapping keyType valueType) = .ok mappingState)
    (keyAccepted : inferExprFuel fuel context key (some (mappingState.resolve keyType)) mappingState =
      .ok (keyResult, indexState))
    (accepted : inferPlaceFuel (fuel + 1) context source initial = .ok final)
    (lifetime : GeneralizationLifetime event mappingState.inference.next indexState [keyResult.type]) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  have baseProperties := inferPlaceFuel_inferenceProperties ready catalog.formation catalog.canonical baseAccepted
  have keyProperties := fresh_eq_inferenceProperties baseProperties.2.1 keyFresh
  have valueProperties := fresh_eq_inferenceProperties keyProperties.2.1 valueFresh
  have baseBelow := baseProperties.2.2.weaken (keyProperties.1.trans valueProperties.1).next_le
  have keyBelow := keyProperties.2.2.weaken valueProperties.1.next_le
  have mappingBelow := (Ty.variablesBelow_mapping_iff _ _ _).2 ⟨keyBelow, valueProperties.2.2⟩
  have mappingReady := unify_preserves_inferenceReady valueProperties.2.1 baseBelow mappingBelow mappingAccepted
  have mappingProgress := unify_inferenceProgress valueProperties.2.1.solved baseBelow mappingBelow mappingAccepted
  have resolvedKeyBelow := mappingReady.solved.variablesBelow_apply (keyBelow.weaken mappingProgress.next_le)
  have keyExpected : ∀ type ∈ (some (mappingState.resolve keyType) : Option Ty),
      type.VariablesBelow mappingState.inference.next := by
    intro type member
    cases Option.some.inj (Option.mem_def.mp member)
    exact resolvedKeyBelow
  have indexProperties := inferExprFuel_inferenceProperties mappingReady
    catalog.formation catalog.canonical keyExpected keyAccepted
  have prefixProgress := baseProperties.1.trans
    (keyProperties.1.trans (valueProperties.1.trans mappingProgress))
  have valueAtMapping := valueProperties.2.2.weaken mappingProgress.next_le
  have valueSafe := lifetime.older valueType valueAtMapping
  have indexLife := lifetime.weaken_entry prefixProgress.next_le
  have resultEq : ({baseResult with
      projections := baseResult.projections ++ [.index keyResult.id]
      type := indexState.resolve valueType}, indexState) = final := by
    simpa only [inferPlaceFuel, form, baseAccepted, keyFresh, valueFresh,
      mappingAccepted, keyAccepted, bind, Except.bind, pure, Pure.pure, Except.pure,
      Except.ok.injEq] using accepted
  cases resultEq
  exact indexLife.replaceOutputs (by
    intro type member
    cases List.mem_singleton.mp member
    exact safe_resolved indexProperties.2.1 valueSafe)

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizedStatementRecording
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

theorem GeneralizedActualStateInvariant.recordStatement
    {state : State} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant state source)
    (node : StatementNode)
    (noBindings : statementInitializedLetBindings node.form = []) :
    GeneralizedActualStateInvariant (state.recordNode (.statement node)) source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  refine ⟨⟨pending, ledger.recordStatement_noBindings node noBindings⟩,
    invariant.origins.congr_localBinders rfl,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow rfl (Nat.le_refl _),
    ?_, invariant.backed.congr rfl rfl rfl⟩
  intro binder member
  exact (invariant.privacy binder member).transport rfl (.of_substitution_eq rfl)

/-- Restore only a genuine saved scope whose binders survive the actual child.
The origin witness belongs to that saved scope, while its privacy and ledger
come from the completed child. -/
theorem GeneralizedActualStateInvariant.restoreSaved
    {outer inner : State} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant inner source)
    (origins : ActiveBinderCaptureOrigins outer source)
    (saved : outer.localBinders ⊆ inner.localBinders) :
    GeneralizedActualStateInvariant (inner.restoreLexicalScope outer.lexicalScope) source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  refine ⟨⟨pending, ledger.restoreLexicalScope _⟩, origins.restoreLexicalScope, ?_, ?_, ?_⟩
  · intro binder member
    exact invariant.quantifiersBelow binder (saved member)
  · intro binder member other present
    exact (invariant.privacy binder (saved member) other (saved present)).transport (.of_substitution_eq rfl)
  · intro binder member requirement present
    exact invariant.backed binder (saved member) requirement present

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceRawHeaderLifetime
/-! The real receipt starts its lifetime using only actual requirements,
old template backing and retained binder origins. No whole node-prefix or
entry privacy invariant is required. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail
namespace RawHeaderLifetime
variable {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}

def event
    (receipt : SourceInference.LocalHeaderRequirementTiming.Receipt fuel context source initial result)
    (ready : receipt.ready.InferenceReady)
    (extension : finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution)
    (retained : ({binder := receipt.binding.1, initializer := .expression receipt.value.id} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceState.toTypedSource roots))
    (binderRetained : receipt.binding.1 ∈ (evidenceState.toTypedSource roots).initializedLetBinders) :
    RetainedGeneralization (evidenceState.toTypedSource roots) finalized.substitution
      receipt.binding.1 receipt.value.id where
  context
  entry := initial
  readyState := receipt.ready
  value := receipt.value
  valueId := rfl
  computation := .header receipt
  ready
  extension
  retained
  binderRetained

theorem lifetime
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (receipt : SourceInference.LocalHeaderRequirementTiming.Receipt fuel context source initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (backed : LiveTemplatesBacked initial)
    (origins : ActiveBinderCaptureOrigins initial (evidenceState.toTypedSource roots))
    (retained : ({binder := receipt.binding.1, initializer := .expression receipt.value.id} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceState.toTypedSource roots))
    (binderRetained : receipt.binding.1 ∈ (evidenceState.toTypedSource roots).initializedLetBinders)
    (extension : finalized.substitution.SemanticallyExtends result.2.inference.substitution) :
    ∃ readyAtEvent readyExtension,
      GeneralizationLifetime (event (finalized := finalized) receipt readyAtEvent readyExtension retained binderRetained)
        initial.inference.next result.2 [] := by
  have inferred := receipt.initializer_inference ready formation canonical
  have readyExtension : finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution := by
    rwa [receipt.inference_eq] at extension
  have templates := LocalHeaderRequirementTiming.Receipt.templates_before receipt backed ready wellFormed formation canonical
  have readyLive : LiveBindersSafe receipt.binding.1.scheme.quantified receipt.ready :=
    generalized_live_from_finalizer resources (origins.congr_localBinders receipt.ready_binders)
      readyExtension binderRetained rfl templates
  have unchanged : SafeTransport receipt.binding.1.scheme.quantified receipt.ready result.2 :=
    .of_substitution_eq (congrArg InferState.substitution receipt.inference_eq)
  have afterLive : LiveBindersSafe receipt.binding.1.scheme.quantified result.2 := by
    intro binder member
    rw [receipt.result_binders] at member
    rcases List.mem_cons.mp member with rfl | old
    · exact (binder_private_own_quantifiers readyExtension (resources.local_no_capture _ binderRetained)).transport unchanged
    · apply (readyLive binder ?_).transport unchanged
      rw [receipt.ready_binders]
      exact old
  have sameRequirements : result.2.requirements = receipt.ready.requirements :=
    congrArg (fun output : ForItemForm × State => output.2.requirements) receipt.completed
  refine ⟨inferred.2.1, readyExtension, {
    createdAfter := Nat.le_refl _
    allocated := LocalHeaderRequirementTiming.Receipt.quantified_at_or_after_entry resources receipt ready wellFormed catalog formation canonical backed origins binderRetained extension
    bound := ?_
    transport := unchanged
    live := afterLive
    values := ?_
    older := ?_
    newRows := ?_ }⟩
  · intro q quantified
    have bound := inferred.2.1.solved.variablesBelow_apply inferred.2.2 q (List.mem_filter.mp quantified).1
    simpa only [event, receipt.inference_eq] using bound
  · simp
  · intro type below
    exact LocalHeaderRequirementTiming.Receipt.generalized_type_safe resources receipt ready wellFormed catalog formation canonical backed origins binderRetained extension below
  · intro requirement member fresh
    exact False.elim (fresh (sameRequirements ▸ member))

end RawHeaderLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceRawStatementLifetime
/-! The real receipt starts its lifetime using only actual requirements,
old template backing and retained binder origins. No whole node-prefix or
entry privacy invariant is required. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail
namespace RawStatementLifetime
variable {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initial : State} {result : Detail.StatementResult}

def event
    (receipt : SourceInference.LocalLetRequirementTiming.Receipt fuel context source initial result)
    (ready : receipt.ready.InferenceReady)
    (extension : finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution)
    (retained : ({binder := receipt.binding.1, initializer := .expression receipt.value.id} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceState.toTypedSource roots))
    (binderRetained : receipt.binding.1 ∈ (evidenceState.toTypedSource roots).initializedLetBinders) :
    RetainedGeneralization (evidenceState.toTypedSource roots) finalized.substitution
      receipt.binding.1 receipt.value.id where
  context
  entry := initial
  readyState := receipt.ready
  value := receipt.value
  valueId := rfl
  computation := .statement receipt
  ready
  extension
  retained
  binderRetained

theorem lifetime
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (receipt : SourceInference.LocalLetRequirementTiming.Receipt fuel context source initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (backed : LiveTemplatesBacked initial)
    (origins : ActiveBinderCaptureOrigins initial (evidenceState.toTypedSource roots))
    (retained : ({binder := receipt.binding.1, initializer := .expression receipt.value.id} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceState.toTypedSource roots))
    (binderRetained : receipt.binding.1 ∈ (evidenceState.toTypedSource roots).initializedLetBinders)
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution) :
    ∃ readyAtEvent readyExtension,
      GeneralizationLifetime (event (finalized := finalized) receipt readyAtEvent readyExtension retained binderRetained)
        initial.inference.next result.state [result.type] := by
  have inferred := receipt.initializer_inference ready formation canonical
  have readyExtension : finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution := by
    rwa [receipt.inference_eq] at extension
  have templates := LocalLetRequirementTiming.Receipt.templates_before receipt backed ready wellFormed formation canonical
  have readyLive : LiveBindersSafe receipt.binding.1.scheme.quantified receipt.ready :=
    generalized_live_from_finalizer resources (origins.congr_localBinders receipt.ready_binders)
      readyExtension binderRetained rfl templates
  have unchanged : SafeTransport receipt.binding.1.scheme.quantified receipt.ready result.state :=
    .of_substitution_eq (congrArg InferState.substitution receipt.inference_eq)
  have afterLive : LiveBindersSafe receipt.binding.1.scheme.quantified result.state := by
    intro binder member
    rw [receipt.result_binders] at member
    rcases List.mem_cons.mp member with rfl | old
    · exact (binder_private_own_quantifiers readyExtension (resources.local_no_capture _ binderRetained)).transport unchanged
    · apply (readyLive binder ?_).transport unchanged
      rw [receipt.ready_binders]
      exact old
  have sameRequirements : result.state.requirements = receipt.ready.requirements :=
    congrArg (fun output : Detail.StatementResult => output.state.requirements) receipt.completed
  refine ⟨inferred.2.1, readyExtension, {
    createdAfter := Nat.le_refl _
    allocated := LocalLetRequirementTiming.Receipt.lifetime_quantified_lower_bound resources receipt ready wellFormed catalog formation canonical backed origins binderRetained extension
    bound := ?_
    transport := unchanged
    live := afterLive
    values := ?_
    older := ?_
    newRows := ?_ }⟩
  · intro q quantified
    have bound := inferred.2.1.solved.variablesBelow_apply inferred.2.2 q (List.mem_filter.mp quantified).1
    simpa only [event, receipt.inference_eq] using bound
  · intro type member
    cases List.mem_singleton.mp member
    have sameType : result.type = .unit := congrArg StatementResult.type receipt.completed
    rw [sameType]
    exact safe_closed _ _ (Ty.variablesBelow_constructor 0 _)
  · intro type below
    exact LocalLetRequirementTiming.Receipt.lifetime_older_type_safe resources receipt ready wellFormed catalog formation canonical backed origins binderRetained extension below
  · intro requirement member fresh
    exact False.elim (fresh (sameRequirements ▸ member))

end RawStatementLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
end
