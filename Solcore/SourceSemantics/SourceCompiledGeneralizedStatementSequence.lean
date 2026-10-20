import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedStatementsContracts

/-! Source-order composition passes only the actual head and tail calls to
their semantic consumers. Each call remains tied to one selected finalizer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization
open SourceInferenceStatementsSoundness

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {inferenceContext : SourceInference.Context} {expectedReturn : Ty}
    {initial : State} {result : Detail.BlockResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}

theorem statements_nil
    (boundary : StatementsBoundary selected (childFuel + 1) inferenceContext [] expectedReturn
      initial result frames target) :
    StatementsConclusion selected inferenceContext expectedReturn result frames target := by
  have same := inferStatementsFuel_success_nil_facts boundary.accepted
  subst result
  exact ⟨target, .empty, boundary.invariant, boundary.actual, boundary.operational,
    .nil _ _, BlockResultMatchesFactsAfterSubstitution.empty _ _⟩

theorem statements_singleton
    {statement : Syntax.Statement}
    (boundary : StatementsBoundary selected (childFuel + 1) inferenceContext [statement] expectedReturn
      initial result frames target)
    (recursive : ∀ {head : Detail.StatementResult},
      StatementBoundary selected childFuel inferenceContext statement expectedReturn
        initial head frames target →
      StatementConclusion selected inferenceContext expectedReturn head frames target) :
    StatementsConclusion selected inferenceContext expectedReturn result frames target := by
  obtain ⟨head, accepted, same⟩ := inferStatementsFuel_success_singleton_facts boundary.accepted
  subst result
  obtain ⟨finalContext, facts, invariant, actual, operational, typing, agreement⟩ :=
    recursive ({
      accepted
      interfaces := boundary.interfaces
      extension := boundary.extension
      scope := boundary.scope
      invariant := boundary.invariant
      actual := boundary.actual
      operational := boundary.operational
      rawSubtree := boundary.rawSubtrees head.id (by simp)
      integerPatterns := boundary.integerPatterns
      integerLiterals := boundary.integerLiterals
      requirements := boundary.requirements
      covered := boundary.covered head.id (by simp)
      actualCovered := boundary.actualCovered head.id (by simp) } :
      StatementBoundary selected childFuel inferenceContext statement expectedReturn initial head frames target)
  exact ⟨finalContext, .singleton facts, invariant, actual, operational,
    .singleton typing, BlockResultMatchesFactsAfterSubstitution.singleton agreement⟩

theorem statements_cons
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {statement next : Syntax.Statement} {rest : List Syntax.Statement}
    (boundary : StatementsBoundary selected (childFuel + 1) inferenceContext
      (statement :: next :: rest) expectedReturn initial result frames target)
    (headSound : ∀ {head : Detail.StatementResult},
      StatementBoundary selected childFuel inferenceContext statement expectedReturn
        initial head frames target →
      StatementConclusion selected inferenceContext expectedReturn head frames target)
    (tailSound : ∀ {head : Detail.StatementResult} {tail : Detail.BlockResult}
        {middle : SourceSemantics.Context},
      Detail.inferStatementFuel childFuel inferenceContext statement expectedReturn initial = .ok head →
      StatementsBoundary selected childFuel inferenceContext (next :: rest) expectedReturn
        head.state tail frames middle →
      StatementsConclusion selected inferenceContext expectedReturn tail frames middle) :
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
  obtain ⟨middle, headFacts, middleInvariant, middleActual, middleOperational, headTyping, headAgreement⟩ :=
    headSound ({
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
  have assumptionsEq := statementHasType_assumptions_eq headTyping
  have covered : ∀ id ∈ tail.statements,
      TemplateScopeCovered selected.body.finalized.typedSource middle (.statement id) := by
    intro id member owner scopes
    change owner.requirement.predicate ∈ middle.assumptions
    rw [assumptionsEq]
    exact boundary.covered id (by simp [member]) owner scopes
  obtain ⟨finalContext, tailFacts, invariant, actual, operational, tailTyping, tailAgreement⟩ :=
    tailSound headAccepted ({
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

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
