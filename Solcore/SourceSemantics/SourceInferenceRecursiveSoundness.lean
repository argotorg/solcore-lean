import Solcore.SourceSemantics.SourceInferenceCheckedBodyTypingBridge
import Solcore.SourceSemantics.SourceInferenceStatementsSoundness
import Solcore.SourceSemantics.SourceInferenceStatementLocalBound

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

/-- Reserving the statement occurrence leaves every recursive semantic and
inference premise intact, apart from advancing the occurrence bound. -/
theorem RecursiveStatementInvariant.allocateStatementId
    {wholeContext : Frontend.SourceInference.Context}
    {expectedReturn : Ty}
    {finalized : Frontend.SourceInference.Result}
    {initial allocated : State}
    {id : StatementId}
    {semanticContext : SourceSemantics.Context}
    (invariant : RecursiveStatementInvariant wholeContext expectedReturn
      finalized initial semanticContext)
    (allocationEq : initial.allocateStatementId = (id, allocated)) :
    RecursiveStatementInvariant wholeContext expectedReturn finalized
      allocated semanticContext := by
  have allocatedEq : initial.allocateStatementId.2 = allocated :=
    congrArg Prod.snd allocationEq
  subst allocated
  refine {
    active := invariant.active.allocateStatementId allocationEq
    ready := ?_
    returnBelow := ?_
    bindersBelow := ?_
    nodesBelow := ?_
    substitutionExtension := ?_
    signaturesEq := invariant.signaturesEq
    typeParametersEq := invariant.typeParametersEq
    declarationEq := invariant.declarationEq
    residual := invariant.residual
    solvedRequirementsEq := invariant.solvedRequirementsEq
    assumptionsMono := invariant.assumptionsMono
  }
  · exact invariant.ready.allocateStatementId
  · exact invariant.returnBelow
  · exact State.allocateStatementId_preserves_localBindersBelowNextLocal
      initial invariant.bindersBelow
  · exact State.allocateStatementId_preserves_nodesBelowNextOccurrence
      initial invariant.nodesBelow
  · exact invariant.substitutionExtension

/-- Once a branch has produced its actual semantic typing, the generic
frontend progress facts and lexical-only context change reconstruct the
invariant for the next source-ordered statement. -/
theorem RecursiveStatementInvariant.of_statement_typing
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {finalized : Frontend.SourceInference.Result}
    {initialContext finalContext : SourceSemantics.Context}
    {roots : List NodeId} {facts : StatementFacts}
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial initialContext)
    (success : Detail.inferStatementFuel fuel inferenceContext statement
      expectedReturn initial = .ok result)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (resultActive : ActiveLocalContextInvariant result.state
      finalized.substitution finalContext)
    (resultBindersBelow : result.state.LocalBindersBelowNextLocal)
    (resultSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        result.state.inference.substitution)
    (typing : StatementHasType
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution)
      { returnType := finalized.substitution.apply expectedReturn
        loopDepth := inferenceContext.loopDepth }
      initialContext result.id finalContext facts) :
    RecursiveStatementInvariant wholeContext expectedReturn finalized
      result.state finalContext := by
  have properties := Detail.inferStatementFuel_inferenceProperties
    initialInvariant.ready signatureFormation functionsCanonical
    initialInvariant.returnBelow success
  have fields := statementHasType_nonlocal_fields_eq typing
  refine {
    active := resultActive
    ready := properties.2.1
    returnBelow := initialInvariant.returnBelow.weaken properties.1.next_le
    bindersBelow := resultBindersBelow
    nodesBelow := (Detail.inferStatementFuel_occurrenceBoundExtends success
      ).nodesBelowNextOccurrence initialInvariant.nodesBelow
    substitutionExtension := resultSubstitutionExtension
    signaturesEq := fields.1.trans initialInvariant.signaturesEq
    typeParametersEq := fields.2.1.trans initialInvariant.typeParametersEq
    declarationEq := fields.2.2.1.trans initialInvariant.declarationEq
    residual := fields.2.2.2.1.trans initialInvariant.residual
    solvedRequirementsEq := fields.2.2.2.2.1.trans
      initialInvariant.solvedRequirementsEq
    assumptionsMono := ?_
  }
  rw [fields.2.2.2.2.2]
  exact initialInvariant.assumptionsMono

/-- Package a branch-local soundness proof as the recursive successor
invariant.  All state progress is supplied by the concrete successful
statement inference, so branch proofs need only establish the declarative
judgment and its result facts. -/
theorem RecursiveStatementInvariant.close_statement_branch
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {finalized : Frontend.SourceInference.Result}
    {initialContext : SourceSemantics.Context}
    {roots : List NodeId}
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial initialContext)
    (success : Detail.inferStatementFuel fuel inferenceContext statement
      expectedReturn initial = .ok result)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (resultBindersBelow : result.state.LocalBindersBelowNextLocal)
    (resultSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        result.state.inference.substitution)
    (branch : ∃ finalContext facts,
      ActiveLocalContextInvariant result.state finalized.substitution
        finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        initialContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts) :
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        initialContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
  obtain ⟨finalContext, facts, resultActive, typing, agreement⟩ := branch
  exact ⟨finalContext, facts,
    RecursiveStatementInvariant.of_statement_typing initialInvariant success
      signatureFormation functionsCanonical resultActive resultBindersBelow
      resultSubstitutionExtension typing,
    typing, agreement⟩

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
    finalized.substitution.SemanticallyExtends
      result.state.inference.substitution →
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
    finalSubstitutionExtension rawResultExtension resultExtension
    integerPatternsSubset
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
    inferStatementsFuel_success_statementsHaveType_under_ambient_bounded_scoped_evidence_with_extra
      (fun state context => RecursiveStatementInvariant inferenceContext
        expectedReturn finalized state context)
      (fun state => finalized.substitution.SemanticallyExtends
        state.inference.substitution ∧
        state.integerLiterals ⊆ evidenceState.integerLiterals)
      (roots := roots) initialInvariant initialBelow resultExtension
      integerPatternsSubset requirementsSubset
      ⟨finalSubstitutionExtension, integerLiteralsSubset⟩
      (fun headInvariant headSuccess tailSuccess tailExtra => by
        have headProperties := Detail.inferStatementFuel_inferenceProperties
          headInvariant.ready signatureFormation functionsCanonical
          headInvariant.returnBelow headSuccess
        have tailProperties := Detail.inferStatementsFuel_inferenceProperties
          headProperties.2.1 signatureFormation functionsCanonical
          (headInvariant.returnBelow.weaken headProperties.1.next_le)
          tailSuccess
        exact ⟨TypeSystem.Substitution.SemanticallyExtends.trans
            tailExtra.1 tailProperties.1.substitution_extends,
          List.Subset.trans
            (Detail.inferStatementsFuel_integerLiterals_subset tailSuccess)
            tailExtra.2⟩)
      covered
      (fun childBound childInvariant childSuccess childExtension
        childIntegerPatternsSubset childRequirementsSubset childExtra
        childCovered =>
        statementSound _ childBound childSuccess resources
          signatureFormation functionsCanonical catalog signatureParameters
          childInvariant childExtra.1 childExtension childIntegerPatternsSubset
          childExtra.2 childRequirementsSubset childCovered)
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

/-- Strong, two-source one-statement theorem needed by nested blocks and
lambda bodies.  `semanticSource` is the enclosing construct's completed local
source; `finalized.typedSource` is only the whole-body evidence source.  The
resource index deliberately belongs to the whole checker body, not the
possibly different return type or loop depth of this local traversal. -/
def InferStatementFuelScopedSoundness (fuel : Nat) : Prop :=
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {initial : State}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {semanticContext : SourceSemantics.Context},
    Detail.inferStatementFuel fuel inferenceContext statement expectedReturn
      initial = .ok result →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    inferenceContext.signatures = wholeContext.signatures →
    inferenceContext.scope.genericOwner = wholeContext.scope.genericOwner →
    inferenceContext.typeParameters = wholeContext.typeParameters →
    inferenceContext.assumptions = wholeContext.assumptions →
    ProgramSignatureFormationValidated inferenceContext.signatures →
    (∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes)) →
    SignatureCatalogWellFormed inferenceContext.signatures →
    SignatureParametersWellFormed inferenceContext.scope.genericOwner
      inferenceContext.typeParameters →
    RecursiveStatementInvariant wholeContext expectedReturn finalized
      initial semanticContext →
    finalized.substitution.SemanticallyExtends
      result.state.inference.substitution →
    TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) semanticSource →
    TypingSourceExtends semanticSource finalized.typedSource →
    TypingSourceExtends (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) →
    result.state.integerPatterns ⊆ evidenceState.integerPatterns →
    result.state.integerLiterals ⊆ evidenceState.integerLiterals →
    result.state.requirements ⊆ evidenceState.requirements →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.statement result.id) →
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts

/-- Source-ordered sequencing for the strong two-source contract.  Unlike the
checker specialization, this can be instantiated with a block or lambda's
local parent source while its proof obligations still consult whole-body
coverage and ledgers. -/
def InferStatementsFuelScopedSoundness (fuel : Nat) : Prop :=
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statements : List Syntax.Statement} {initial : State}
    {result : Detail.BlockResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {semanticContext : SourceSemantics.Context},
    Detail.inferStatementsFuel fuel inferenceContext statements expectedReturn
      initial = .ok result →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    inferenceContext.signatures = wholeContext.signatures →
    inferenceContext.scope.genericOwner = wholeContext.scope.genericOwner →
    inferenceContext.typeParameters = wholeContext.typeParameters →
    inferenceContext.assumptions = wholeContext.assumptions →
    ProgramSignatureFormationValidated inferenceContext.signatures →
    (∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes)) →
    SignatureCatalogWellFormed inferenceContext.signatures →
    SignatureParametersWellFormed inferenceContext.scope.genericOwner
      inferenceContext.typeParameters →
    RecursiveStatementInvariant wholeContext expectedReturn finalized
      initial semanticContext →
    finalized.substitution.SemanticallyExtends
      result.state.inference.substitution →
    TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) semanticSource →
    TypingSourceExtends semanticSource finalized.typedSource →
    TypingSourceExtends (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) →
    result.state.integerPatterns ⊆ evidenceState.integerPatterns →
    result.state.integerLiterals ⊆ evidenceState.integerLiterals →
    result.state.requirements ⊆ evidenceState.requirements →
    (∀ statement ∈ result.statements,
      TemplateScopeCovered finalized.typedSource semanticContext
        (.statement statement)) →
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      StatementsHaveType semanticSource
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.statements finalContext facts ∧
      BlockResultMatchesFactsAfterSubstitution finalized.substitution result
        facts

theorem inferStatementsFuelScopedSoundness_of_statementSoundness
    {fuel : Nat}
    (statementSound : ∀ childFuel, childFuel < fuel →
      InferStatementFuelScopedSoundness childFuel) :
    InferStatementsFuelScopedSoundness fuel := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statements
    initial result evidenceState roots finalized semanticSource semanticContext
    success resources signaturesEq ownerEq parametersEq assumptionsEq
    signatureFormation functionsCanonical catalog signatureParameters
    initialInvariant finalSubstitutionExtension resultExtension
    semanticSourceExtension rawResultExtension integerPatternsSubset
    integerLiteralsSubset requirementsSubset covered
  obtain ⟨finalContext, facts, finalInvariant, typing, agreement⟩ :=
    inferStatementsFuel_success_statementsHaveType_under_ambient_bounded_scoped_evidence_with_extra
      (fun state context => RecursiveStatementInvariant wholeContext
        expectedReturn finalized state context)
      (fun state => finalized.substitution.SemanticallyExtends
        state.inference.substitution ∧
        state.integerLiterals ⊆ evidenceState.integerLiterals ∧
        TypingSourceExtends (state.toTypedSource roots)
          (evidenceState.toTypedSource roots))
      (roots := roots) initialInvariant initialInvariant.nodesBelow
      resultExtension integerPatternsSubset requirementsSubset
      ⟨finalSubstitutionExtension, integerLiteralsSubset,
        rawResultExtension⟩
      (by
        intro headFuel childFuel headInitial headContext headStatement head
          tail remaining headInvariant headSuccess tailSuccess tailExtra
        have headProperties := Detail.inferStatementFuel_inferenceProperties
          headInvariant.ready signatureFormation functionsCanonical
          headInvariant.returnBelow headSuccess
        have tailProperties := Detail.inferStatementsFuel_inferenceProperties
          headProperties.2.1 signatureFormation functionsCanonical
          (headInvariant.returnBelow.weaken headProperties.1.next_le)
          tailSuccess
        have headNodesBelow : head.state.NodesBelowNextOccurrence :=
          (Detail.inferStatementFuel_occurrenceBoundExtends headSuccess
            ).nodesBelowNextOccurrence headInvariant.nodesBelow
        have headToTail : TypingSourceExtends
            (head.state.toTypedSource roots)
            (tail.state.toTypedSource roots) :=
          inferStatementsFuel_success_typingSourceExtends tailSuccess
            headNodesBelow roots
        exact ⟨TypeSystem.Substitution.SemanticallyExtends.trans
            tailExtra.1 tailProperties.1.substitution_extends,
          List.Subset.trans
            (Detail.inferStatementsFuel_integerLiterals_subset tailSuccess)
            tailExtra.2.1,
          TypingSourceExtends.trans headToTail tailExtra.2.2⟩)
      covered
      (fun childBound childInvariant childSuccess childExtension
        childIntegerPatternsSubset childRequirementsSubset childExtra
        childCovered =>
        statementSound _ childBound childSuccess resources signaturesEq
          ownerEq parametersEq assumptionsEq signatureFormation
          functionsCanonical catalog signatureParameters childInvariant
          childExtra.1 childExtension semanticSourceExtension
          childExtra.2.2 childIntegerPatternsSubset childExtra.2.1
          childRequirementsSubset childCovered)
      success
  exact ⟨finalContext, facts, finalInvariant, typing, agreement⟩

/-- The local-source statement and block judgments close by strong fuel
induction once the syntax-directed one-statement step is supplied. -/
theorem inferStatementsFuelScopedSoundness_of_recursive_statement_step
    (step : ∀ fuel,
      (∀ childFuel, childFuel < fuel →
        InferStatementsFuelScopedSoundness childFuel) →
      InferStatementFuelScopedSoundness fuel) :
    ∀ fuel, InferStatementsFuelScopedSoundness fuel := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel induction =>
      apply inferStatementsFuelScopedSoundness_of_statementSoundness
      intro childFuel childBound
      apply step childFuel
      intro nestedFuel nestedBound
      exact induction nestedFuel (Nat.lt_trans nestedBound childBound)

/-- The checker-facing statement theorem is the whole-body specialization of
the two-source recursive theorem.  The initial substitution invariant follows
from the actual successful list inference and its final substitution
extension; no extra callback is assumed at this boundary. -/
theorem inferStatementsFuelSoundness_of_scopedSoundness
    {fuel : Nat}
    (scopedSound : InferStatementsFuelScopedSoundness fuel) :
    InferStatementsFuelSoundness fuel := by
  intro inferenceContext statements expectedReturn initial result
    evidenceState roots finalized semanticContext success resources
    signatureFormation functionsCanonical catalog signatureParameters
    initialActive ready returnBelow bindersBelow initialBelow
    finalSubstitutionExtension rawResultExtension resultExtension
    integerPatternsSubset integerLiteralsSubset requirementsSubset
    signaturesEq typeParametersEq declarationEq residual
    solvedRequirementsEq assumptionsMono covered
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
    scopedSound (wholeContext := inferenceContext)
      (wholeReturn := expectedReturn)
      (semanticSource := finalized.typedSource)
      success resources rfl rfl rfl rfl signatureFormation
      functionsCanonical catalog signatureParameters initialInvariant
      finalSubstitutionExtension resultExtension
      (TypingSourceExtends.refl _) rawResultExtension
      integerPatternsSubset integerLiteralsSubset requirementsSubset covered
  exact ⟨finalContext, facts, finalInvariant.active, typing, agreement⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
