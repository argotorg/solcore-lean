import Solcore.SourceSemantics.SourceInferenceRecursiveSoundness

/-!
Compositional assembly for the two executable `match` statement branches.
The semantic premises are about the exact scrutinee, cases, and optional
default body returned by the successful parent traversal.  No premise claims
soundness for arbitrary independently chosen child computations.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- Assemble a default-free `match` from its actual typed children.  The
checker guard, rather than a separately postulated exhaustiveness claim,
supplies declarative exhaustiveness. -/
theorem inferStatementFuel_success_matchWithoutDefault_of_actual_typed_children
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.MatchArms} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult}
    {outer : Substitution} {target : SourceSemantics.Context}
    {scrutinee : InferredExpression} {scrutineeState : State}
    {hiddenScrutinee : Resolved.LocalId} {hiddenState : State}
    {checked : Detail.MatchCasesResult} {caseFacts : List BodyFacts}
    (statementEq : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (scrutineeSuccess : inferMatchScrutineesFuel fuel inferenceContext
      statement.span scrutinees.elements.toList allocated =
        .ok (scrutinee, scrutineeState))
    (hiddenAllocation : scrutineeState.allocateHiddenLocal =
      (hiddenScrutinee, hiddenState))
    (casesSuccess : Detail.inferMatchCasesFuel fuel inferenceContext
      scrutinee.type expectedReturn hiddenState.lexicalScope
      arms.value.cases hiddenState = .ok checked)
    (catalog : SignatureCatalogWellFormed target.signatures)
    (signaturesEq : target.signatures = inferenceContext.signatures)
    (casesPresent : arms.value.cases ≠ [])
    (invariant : ActiveLocalContextInvariant initial outer target)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId)
    (scrutineeTyping : ExpressionHasType
      ((result.state.toTypedSource roots).applySubstitution outer)
      target scrutinee.id (outer.apply scrutinee.type))
    (casesTyping : MatchCasesHaveType
      ((result.state.toTypedSource roots).applySubstitution outer) {
        returnType := outer.apply expectedReturn
        loopDepth := inferenceContext.loopDepth
      } target (outer.apply scrutinee.type)
      (checked.cases.map (TypedMatchCase.applySubstitution outer)) caseFacts)
    (allReturnEq : allBodiesSawReturn caseFacts = checked.allReturn) :
    ∃ facts,
      ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer) {
          returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth
        } target result.id target facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  obtain ⟨actualScrutinee, actualScrutineeState, actualHidden,
    actualHiddenState, actualChecked, actualScrutineeSuccess,
    actualHiddenAllocation, actualCasesSuccess, guardPassed, resultEq,
    contains⟩ :=
    inferStatementFuel_success_matchWithoutDefault_facts statementEq defaultEq
      allocationEq success roots
  have scrutineePairEq : (actualScrutinee, actualScrutineeState) =
      (scrutinee, scrutineeState) := by
    rw [scrutineeSuccess] at actualScrutineeSuccess
    exact (Except.ok.inj actualScrutineeSuccess).symm
  obtain ⟨rfl, rfl⟩ := scrutineePairEq
  have hiddenPairEq : (actualHidden, actualHiddenState) =
      (hiddenScrutinee, hiddenState) := by
    rw [hiddenAllocation] at actualHiddenAllocation
    exact actualHiddenAllocation.symm
  obtain ⟨rfl, rfl⟩ := hiddenPairEq
  have checkedEq : actualChecked = checked := by
    rw [casesSuccess] at actualCasesSuccess
    exact (Except.ok.inj actualCasesSuccess).symm
  subst actualChecked
  have allocatedInvariant : ActiveLocalContextInvariant allocated outer
      target := invariant.allocateStatementId allocationEq
  have scrutineeInvariant : ActiveLocalContextInvariant scrutineeState outer
      target := allocatedInvariant.inferMatchScrutineesFuel scrutineeSuccess
  have hiddenInvariant : ActiveLocalContextInvariant hiddenState outer target :=
    scrutineeInvariant.allocateHiddenLocal hiddenAllocation
  have checkedInvariant : ActiveLocalContextInvariant checked.state outer
      target := hiddenInvariant.inferMatchCasesFuel casesSuccess
  have checkedExtension : outer.SemanticallyExtends
      checked.state.inference.substitution := by
    simpa [resultEq, State.recordNode] using outerExtension
  have exhaustive : MatchExhaustive target (outer.apply scrutinee.type)
      (checked.cases.map (TypedMatchCase.applySubstitution outer)) none :=
    matchExhaustiveWithoutDefault_of_guard catalog signaturesEq
      casesSuccess casesTyping scrutineeTyping.type_admissible
      checkedExtension guardPassed
  have checkedCasesPresent : checked.cases ≠ [] := by
    intro checkedCasesEq
    have lengthEq := Detail.inferMatchCasesFuel_success_cases_length
      casesSuccess
    rw [checkedCasesEq] at lengthEq
    apply casesPresent
    simpa using lengthEq.symm
  have caseFactsPresent : caseFacts ≠ [] :=
    matchCasesHaveType_facts_ne_nil_of_cases_ne_nil casesTyping (by
      simpa using checkedCasesPresent)
  obtain ⟨summary, merged⟩ :=
    mergeBodyControls_withoutDefault_eq_some_of_ne_nil caseFacts
      caseFactsPresent
  subst result
  refine ⟨{
      type := if allBodiesSawReturn caseFacts then
        outer.apply expectedReturn
      else .unit
      hasValue := allBodiesSawReturn caseFacts
      sawReturn := allBodiesSawReturn caseFacts
      control := summary.eraseValue
    }, checkedInvariant.recordNode _, ?_, ?_⟩
  · exact matchWithoutDefaultStatementHasType_afterSubstitution contains
      scrutineeTyping casesTyping exhaustive allReturnEq merged
      checkedExtension
  · exact StatementResultMatchesFactsAfterSubstitution.matchWithoutDefault
      allReturnEq checkedExtension id _

/-- Assemble a `match` with a default arm from the successful scrutinee,
explicit-case, and default-body traversals.  The default body makes both
exhaustiveness and control merging total. -/
theorem inferStatementFuel_success_matchWithDefault_of_actual_typed_children
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.MatchArms} {defaultBody : Syntax.Block}
    {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult}
    {outer : Substitution} {target defaultFinal : SourceSemantics.Context}
    {scrutinee : InferredExpression} {scrutineeState : State}
    {hiddenScrutinee : Resolved.LocalId} {hiddenState : State}
    {checked : Detail.MatchCasesResult}
    {defaultResult : Detail.BlockResult}
    {caseFacts : List BodyFacts} {defaultFacts : BodyFacts}
    (statementEq : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = some defaultBody)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (scrutineeSuccess : inferMatchScrutineesFuel fuel inferenceContext
      statement.span scrutinees.elements.toList allocated =
        .ok (scrutinee, scrutineeState))
    (hiddenAllocation : scrutineeState.allocateHiddenLocal =
      (hiddenScrutinee, hiddenState))
    (casesSuccess : Detail.inferMatchCasesFuel fuel inferenceContext
      scrutinee.type expectedReturn hiddenState.lexicalScope
      arms.value.cases hiddenState = .ok checked)
    (defaultSuccess : Detail.inferStatementsFuel fuel inferenceContext
      defaultBody.value expectedReturn checked.state = .ok defaultResult)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId)
    (scrutineeTyping : ExpressionHasType
      ((result.state.toTypedSource roots).applySubstitution outer)
      target scrutinee.id (outer.apply scrutinee.type))
    (casesTyping : MatchCasesHaveType
      ((result.state.toTypedSource roots).applySubstitution outer) {
        returnType := outer.apply expectedReturn
        loopDepth := inferenceContext.loopDepth
      } target (outer.apply scrutinee.type)
      (checked.cases.map (TypedMatchCase.applySubstitution outer)) caseFacts)
    (defaultTyping : StatementsHaveType
      ((result.state.toTypedSource roots).applySubstitution outer) {
        returnType := outer.apply expectedReturn
        loopDepth := inferenceContext.loopDepth
      } target defaultResult.statements defaultFinal defaultFacts)
    (caseReturnEq : allBodiesSawReturn caseFacts = checked.allReturn)
    (defaultAgreement : BlockResultMatchesFactsAfterSubstitution outer
      defaultResult defaultFacts) :
    ∃ facts,
      ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer) {
          returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth
        } target result.id target facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  obtain ⟨actualScrutinee, actualScrutineeState, actualHidden,
    actualHiddenState, actualChecked, actualDefault, actualScrutineeSuccess,
    actualHiddenAllocation, actualCasesSuccess, actualDefaultSuccess,
    _guardPassed, resultEq, contains⟩ :=
    inferStatementFuel_success_matchWithDefault_facts statementEq defaultEq
      allocationEq success roots
  have scrutineePairEq : (actualScrutinee, actualScrutineeState) =
      (scrutinee, scrutineeState) := by
    rw [scrutineeSuccess] at actualScrutineeSuccess
    exact (Except.ok.inj actualScrutineeSuccess).symm
  obtain ⟨rfl, rfl⟩ := scrutineePairEq
  have hiddenPairEq : (actualHidden, actualHiddenState) =
      (hiddenScrutinee, hiddenState) := by
    rw [hiddenAllocation] at actualHiddenAllocation
    exact actualHiddenAllocation.symm
  obtain ⟨rfl, rfl⟩ := hiddenPairEq
  have checkedEq : actualChecked = checked := by
    rw [casesSuccess] at actualCasesSuccess
    exact (Except.ok.inj actualCasesSuccess).symm
  subst actualChecked
  have defaultEqResult : actualDefault = defaultResult := by
    rw [defaultSuccess] at actualDefaultSuccess
    exact (Except.ok.inj actualDefaultSuccess).symm
  subst actualDefault
  have allocatedInvariant : ActiveLocalContextInvariant allocated outer
      target := invariant.allocateStatementId allocationEq
  have scrutineeInvariant : ActiveLocalContextInvariant scrutineeState outer
      target := allocatedInvariant.inferMatchScrutineesFuel scrutineeSuccess
  have hiddenInvariant : ActiveLocalContextInvariant hiddenState outer target :=
    scrutineeInvariant.allocateHiddenLocal hiddenAllocation
  have defaultExtension : outer.SemanticallyExtends
      defaultResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using
      outerExtension
  obtain ⟨summary, merged⟩ :=
    mergeBodyControls_withDefault_eq_some caseFacts defaultFacts
  subst result
  refine ⟨{
      type := if allBodiesSawReturn caseFacts && defaultFacts.sawReturn then
        outer.apply expectedReturn
      else .unit
      hasValue := allBodiesSawReturn caseFacts && defaultFacts.sawReturn
      sawReturn := allBodiesSawReturn caseFacts && defaultFacts.sawReturn
      control := summary.eraseValue
    }, hiddenInvariant.restoreLexicalScope_recordNode _, ?_, ?_⟩
  · exact matchWithDefaultStatementHasType_afterSubstitution contains
      scrutineeTyping casesTyping defaultTyping caseReturnEq defaultAgreement
      merged defaultExtension
  · exact StatementResultMatchesFactsAfterSubstitution.matchWithDefault
      caseReturnEq defaultAgreement defaultExtension id _

end Solcore.SourceSemantics.SourceInferenceSoundness
