import Solcore.SourceSemantics.SourceCompiledGeneralizedAssemblyContracts
import Solcore.SourceSemantics.SourceCompiledGeneralizedStatementSequence
import Solcore.SourceSemantics.SourceCompiledGeneralizedStatementReturnPrivacy

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : Selected compiled row fuel}

/-- The actual head statement derives the return privacy required by the tail. -/
theorem statements_cons_with_return
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (headSound : StatementRootedSoundness selected childFuel)
    (tailSound : StatementsRootedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {expectedReturn : Ty}
    {initial : State} {result : Detail.BlockResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    {statement next : Syntax.Statement} {rest : List Syntax.Statement}
    (returnSafe : ∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (boundary : StatementsBoundary selected (childFuel + 1) inferenceContext
      (statement :: next :: rest) expectedReturn initial result frames target) :
    StatementsConclusion selected inferenceContext expectedReturn result frames target := by
  obtain ⟨head, tail, headAccepted, tailAccepted, resultEq⟩ :=
    inferStatementsFuel_success_cons_facts boundary.accepted
  subst result
  have headProperties := Detail.inferStatementFuel_inferenceProperties boundary.invariant.ready
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked)
    boundary.invariant.returnBelow headAccepted
  have tailProperties := Detail.inferStatementsFuel_inferenceProperties headProperties.2.1
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked)
    (boundary.invariant.returnBelow.weaken headProperties.1.next_le) tailAccepted
  have headBelow := (Detail.inferStatementFuel_occurrenceBoundExtends headAccepted
    ).nodesBelowNextOccurrence boundary.invariant.nodesBelow
  have headToTail := inferStatementsFuel_success_typingSourceExtends tailAccepted
    headBelow (bodyRoots selected)
  let headBoundary := ({
      accepted := headAccepted
      interfaces := boundary.interfaces
      extension := boundary.extension.trans tailProperties.1.substitution_extends
      scope := boundary.scope
      invariant := boundary.invariant
      actual := boundary.actual
      operational := boundary.operational
      rawSubtree := (boundary.rawSubtrees head.id (by simp)).monoBefore headToTail
      integerPatterns := (Detail.inferStatementsFuel_integerPatterns_subset tailAccepted).trans boundary.integerPatterns
      integerLiterals := (Detail.inferStatementsFuel_integerLiterals_subset tailAccepted).trans boundary.integerLiterals
      requirements := (Detail.inferStatementsFuel_requirements_subset tailAccepted).trans boundary.requirements
      covered := boundary.covered head.id (by simp)
      actualCovered := boundary.actualCovered head.id (by simp) } :
      StatementBoundary selected childFuel inferenceContext statement expectedReturn initial head frames target)
  obtain ⟨middle, headFacts, middleInvariant, middleActual, middleOperational, headTyping, headAgreement⟩ :=
    headSound returnSafe returnAdmissible headBoundary
  have middleSafe := headBoundary.return_safe checked returnSafe
  have middleAdmissible : TypeAdmissible middle (selected.body.finalized.substitution.apply expectedReturn) :=
    StructuralSubstitution.TypeAdmissible.transportContext
      (middleInvariant.signaturesEq.trans boundary.invariant.signaturesEq.symm)
      (middleInvariant.typeParametersEq.trans boundary.invariant.typeParametersEq.symm)
      (middleInvariant.declarationEq.trans boundary.invariant.declarationEq.symm)
      (middleActual.variables_eq.trans boundary.actual.variables_eq.symm)
      (middleInvariant.residual.trans boundary.invariant.residual.symm) returnAdmissible
  have assumptionsEq := statementHasType_assumptions_eq headTyping
  have covered : ∀ id ∈ tail.statements,
      TemplateScopeCovered selected.body.finalized.typedSource middle (.statement id) := by
    intro id member owner scopes
    change owner.requirement.predicate ∈ middle.assumptions
    rw [assumptionsEq]
    exact boundary.covered id (by simp [member]) owner scopes
  obtain ⟨finalContext, tailFacts, invariant, actual, operational, tailTyping, tailAgreement⟩ :=
    tailSound middleSafe middleAdmissible ({
      accepted := tailAccepted
      interfaces := boundary.interfaces
      extension := boundary.extension
      scope := boundary.scope
      invariant := middleInvariant
      actual := middleActual
      operational := middleOperational
      rawSubtrees := fun id member => boundary.rawSubtrees id (by simp [member])
      integerPatterns := boundary.integerPatterns
      integerLiterals := boundary.integerLiterals
      requirements := boundary.requirements
      covered
      actualCovered := fun id member => boundary.actualCovered id (by simp [member]) } :
      StatementsBoundary selected childFuel inferenceContext (next :: rest) expectedReturn
        head.state tail frames middle)
  obtain ⟨tailHead, tailRest, tailEq⟩ := inferStatementsFuel_success_statements_eq_cons tailAccepted
  have typing : StatementsHaveType selected.body.finalized.typedSource
      { returnType := selected.body.finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth }
      target (head.id :: tail.statements) finalContext (.cons headFacts tailFacts) := by
    rw [tailEq]
    exact .cons headTyping (by simpa [tailEq] using tailTyping)
  exact ⟨finalContext, .cons headFacts tailFacts, invariant, actual, operational, typing,
    BlockResultMatchesFactsAfterSubstitution.cons headAgreement tailAgreement⟩

theorem statementsRooted_zero : StatementsRootedSoundness selected 0 := by
  intro inferenceContext statements expectedReturn initial result frames target returnSafe returnAdmissible boundary
  have success := boundary.accepted
  simp only [Detail.inferStatementsFuel] at success
  cases success

/-- Source-order recursion consumes the smaller actual statement and block proofs. -/
theorem statementsRooted_step
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (headSound : StatementRootedSoundness selected childFuel)
    (tailSound : StatementsRootedSoundness selected childFuel) :
    StatementsRootedSoundness selected (childFuel + 1) := by
  intro inferenceContext statements expectedReturn initial result frames target returnSafe returnAdmissible boundary
  cases statements with
  | nil => exact statements_nil boundary
  | cons statement rest =>
    cases rest with
    | nil => exact statements_singleton boundary (fun head => headSound returnSafe returnAdmissible head)
    | cons next rest => exact statements_cons_with_return checked headSound tailSound returnSafe returnAdmissible boundary

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
