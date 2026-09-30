import Solcore.SourceSemantics.SourceInferenceCheckedBodyTypingBridge
import Solcore.SourceSemantics.SourceInferenceStatementsSoundness

/-!
An actual-success interface for the remaining mutually recursive inference
proof.  The final evidence source is fixed by one successful finalization;
each statement is typed in its own append-only local source.  No callback
asserts soundness of an arbitrary child computation unrelated to a successful
parent trace.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

/-- Facts that remain available at every sequential statement boundary.  In
particular the final substitution extends the current inference substitution,
while the semantic context may gain local binders but retains the finalized
whole-body requirement environment. -/
structure RecursiveStatementInvariant
    (inferenceContext : Frontend.SourceInference.Context)
    (expectedReturn : Ty) (finalized : Frontend.SourceInference.Result)
    (state : State) (semanticContext : SourceSemantics.Context) : Prop where
  active : ActiveLocalContextInvariant state finalized.substitution
    semanticContext
  ready : state.InferenceReady
  returnBelow : expectedReturn.VariablesBelow state.inference.next
  bindersBelow : state.LocalBindersBelowNextLocal
  nodesBelow : state.NodesBelowNextOccurrence
  substitutionExtension : finalized.substitution.SemanticallyExtends
    state.inference.substitution
  signaturesEq : semanticContext.signatures =
    (finalizedRequirementContext inferenceContext finalized).signatures
  typeParametersEq : semanticContext.typeParameters =
    inferenceContext.typeParameters
  declarationEq : semanticContext.currentDeclaration =
    some inferenceContext.scope.genericOwner
  residual : semanticContext.residualTypeVariables = true
  solvedRequirementsEq : semanticContext.solvedRequirements =
    (finalizedRequirementContext inferenceContext finalized
      ).solvedRequirements
  assumptionsMono :
    (finalizedRequirementContext inferenceContext finalized).assumptions ⊆
      semanticContext.assumptions

/-- The one-statement obligation for a fuel-indexed proof.  Its only dynamic
premise is the actual successful inference being typed; the retained source,
ledgers, and root coverage come from that same result and finalization. -/
def InferStatementFuelSoundness (fuel : Nat) : Prop :=
  ∀ {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context},
    Detail.inferStatementFuel fuel inferenceContext statement expectedReturn
      initial = .ok result →
    FinalInferenceResources inferenceContext expectedReturn evidenceState roots
      finalized →
    ProgramSignatureFormationValidated inferenceContext.signatures →
    (∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes)) →
    SignatureCatalogWellFormed inferenceContext.signatures →
    SignatureParametersWellFormed inferenceContext.scope.genericOwner
      inferenceContext.typeParameters →
    RecursiveStatementInvariant inferenceContext expectedReturn finalized
      initial semanticContext →
    TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource →
    result.state.integerPatterns ⊆ evidenceState.integerPatterns →
    result.state.integerLiterals ⊆ evidenceState.integerLiterals →
    result.state.requirements ⊆ evidenceState.requirements →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.statement result.id) →
    ∃ finalContext facts,
      RecursiveStatementInvariant inferenceContext expectedReturn finalized
        result.state finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts

/-- Once the one-statement theorem is proved at every smaller fuel, list
sequencing needs no separate semantic callback.  This is the exact proposition
consumed by the checker-body bridge. -/
theorem inferStatementsFuelSoundness_of_statementSoundness
    {fuel : Nat}
    (statementSound : ∀ childFuel, childFuel < fuel →
      InferStatementFuelSoundness childFuel) :
    InferStatementsFuelSoundness fuel := by
  intro inferenceContext statements expectedReturn initial result
    evidenceState roots finalized semanticContext success resources
    signatureFormation functionsCanonical catalog signatureParameters
    initialActive ready returnBelow bindersBelow initialBelow
    finalSubstitutionExtension resultExtension integerPatternsSubset
    integerLiteralsSubset requirementsSubset signaturesEq typeParametersEq
    declarationEq residual solvedRequirementsEq assumptionsMono covered
  have progress := Detail.inferStatementsFuel_inferenceProperties ready
    signatureFormation functionsCanonical returnBelow success
  have initialSubstitutionExtension : finalized.substitution.SemanticallyExtends
      initial.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans
      finalSubstitutionExtension progress.1.substitution_extends
  have initialInvariant : RecursiveStatementInvariant inferenceContext
      expectedReturn finalized initial semanticContext := {
    active := initialActive
    ready
    returnBelow
    bindersBelow
    nodesBelow := initialBelow
    substitutionExtension := initialSubstitutionExtension
    signaturesEq
    typeParametersEq
    declarationEq
    residual
    solvedRequirementsEq
    assumptionsMono
  }
  obtain ⟨finalContext, facts, finalInvariant, typing, agreement⟩ :=
    inferStatementsFuel_success_statementsHaveType_under_ambient_bounded_scoped_evidence_literals
      (fun state context => RecursiveStatementInvariant inferenceContext
        expectedReturn finalized state context)
      (roots := roots) initialInvariant initialBelow resultExtension
      integerPatternsSubset integerLiteralsSubset requirementsSubset covered
      (fun childBound childInvariant childSuccess childExtension
        childIntegerPatternsSubset childIntegerLiteralsSubset
        childRequirementsSubset childCovered =>
        statementSound _ childBound childSuccess resources
          signatureFormation functionsCanonical catalog signatureParameters
          childInvariant childExtension childIntegerPatternsSubset
          childIntegerLiteralsSubset childRequirementsSubset childCovered)
      success
  exact ⟨finalContext, facts, finalInvariant.active, typing, agreement⟩

/-- The remaining branch proof can be supplied one fuel layer at a time.  A
single statement at fuel `n` may invoke a statement list only at smaller
fuel; the sequencing theorem above then closes all source-ordered lists. -/
theorem inferStatementsFuelSoundness_of_recursive_statement_step
    (step : ∀ fuel,
      (∀ childFuel, childFuel < fuel →
        InferStatementsFuelSoundness childFuel) →
      InferStatementFuelSoundness fuel) :
    ∀ fuel, InferStatementsFuelSoundness fuel := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel induction =>
      apply inferStatementsFuelSoundness_of_statementSoundness
      intro childFuel childBound
      apply step childFuel
      intro nestedFuel nestedBound
      exact induction nestedFuel (Nat.lt_trans nestedBound childBound)

end Solcore.SourceSemantics.SourceInferenceSoundness
