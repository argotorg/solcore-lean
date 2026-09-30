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

/-- An actual expression traversal may refine types and append expression
nodes, but it does not change the active lexical context.  This is the common
state step before `if`, `while`, and `for` bodies. -/
theorem RecursiveStatementInvariant.inferExprFuel
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {expectedReturn : Ty}
    {expression : Syntax.Expr} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    (invariant : RecursiveStatementInvariant wholeContext expectedReturn
      finalized initial semanticContext)
    (success : Detail.inferExprFuel fuel inferenceContext expression expected
      initial = .ok (inferred, resultState))
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (expectedBelow : ∀ type ∈ expected,
      type.VariablesBelow initial.inference.next)
    (resultSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        resultState.inference.substitution) :
    RecursiveStatementInvariant wholeContext expectedReturn finalized
      resultState semanticContext := by
  have properties := Detail.inferExprFuel_inferenceProperties invariant.ready
    signatureFormation functionsCanonical expectedBelow success
  refine {
    active := invariant.active.inferExprFuel success
    ready := properties.2.1
    returnBelow := invariant.returnBelow.weaken properties.1.next_le
    bindersBelow := Detail.inferExprFuel_preserves_localBindersBelowNextLocal
      invariant.bindersBelow success
    nodesBelow := (Detail.inferExprFuel_occurrenceBoundExtends success
      ).nodesBelowNextOccurrence invariant.nodesBelow
    substitutionExtension := resultSubstitutionExtension
    signaturesEq := invariant.signaturesEq
    typeParametersEq := invariant.typeParametersEq
    declarationEq := invariant.declarationEq
    residual := invariant.residual
    solvedRequirementsEq := invariant.solvedRequirementsEq
    assumptionsMono := invariant.assumptionsMono
  }

/-- Leaving a branch restores the outer lexical binders while retaining all
allocator and substitution progress of the inner traversal. -/
theorem RecursiveStatementInvariant.restoreLexicalScope
    {wholeContext : Frontend.SourceInference.Context}
    {expectedReturn : Ty}
    {finalized : Frontend.SourceInference.Result}
    {outer inner : State}
    {semanticContext : SourceSemantics.Context}
    (invariant : RecursiveStatementInvariant wholeContext expectedReturn
      finalized outer semanticContext)
    (progress : outer.InferenceProgress inner)
    (innerBelow : inner.NodesBelowNextOccurrence)
    (nextLocalLe : outer.nextLocal ≤ inner.nextLocal)
    (substitutionExtension : finalized.substitution.SemanticallyExtends
      inner.inference.substitution) :
    RecursiveStatementInvariant wholeContext expectedReturn finalized
      (inner.restoreLexicalScope outer.lexicalScope) semanticContext := by
  have restoredProperties := State.restoreLexicalScope_inferenceProperties
    invariant.ready progress
  refine {
    active := invariant.active.restoreLexicalScope
    ready := restoredProperties.2
    returnBelow := invariant.returnBelow.weaken restoredProperties.1.next_le
    bindersBelow := State.restoreLexicalScope_preserves_localBindersBelowNextLocal
      invariant.bindersBelow nextLocalLe
    nodesBelow := State.restoreLexicalScope_preserves_nodesBelowNextOccurrence
      inner outer.lexicalScope innerBelow
    substitutionExtension := ?_
    signaturesEq := invariant.signaturesEq
    typeParametersEq := invariant.typeParametersEq
    declarationEq := invariant.declarationEq
    residual := invariant.residual
    solvedRequirementsEq := invariant.solvedRequirementsEq
    assumptionsMono := invariant.assumptionsMono
  }
  exact substitutionExtension

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

/-- A successful block consumes the scoped soundness theorem for its actual
body traversal.  The recorded block node supplies each body root's coverage;
the body source and three ledgers are prefixes of the enclosing statement's
successful result. -/
theorem inferStatementFuel_success_block_of_scoped_body
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {body : List Syntax.Statement}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .block body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions =
      wholeContext.assumptions)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (resultExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource)
    (rawResultExtension : TypingSourceExtends
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (bodySound : InferStatementsFuelScopedSoundness fuel) :
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
        result facts := by
  obtain ⟨bodyResult, bodySuccess, resultEq, parentNode⟩ :=
    inferStatementFuel_success_block_facts statementEq allocationEq success
      roots
  obtain ⟨bodyResult', bodySuccess', _allocatedBelow, bodyExtension,
      bodyIntegerPatternsSubset, bodyRequirementsSubset⟩ :=
    inferStatementFuel_success_block_child_provenance statementEq allocationEq
      success initialInvariant.nodesBelow roots
  have bodyResultEq : bodyResult' = bodyResult := by
    rw [bodySuccess] at bodySuccess'
    exact (Except.ok.inj bodySuccess').symm
  subst bodyResult'
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have bodySubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        bodyResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using
      resultSubstitutionExtension
  have bodyIntegerLiteralsSubset :
      bodyResult.state.integerLiterals ⊆ result.state.integerLiterals := by
    rw [resultEq]
    intro literal member
    simpa [State.restoreLexicalScope, State.recordNode] using member
  have bodyCovered : ∀ child, child ∈ bodyResult.statements →
      TemplateScopeCovered finalized.typedSource semanticContext
        (.statement child) := by
    intro child member
    have childEdge : DirectChild (result.state.toTypedSource roots)
        (.statement result.id) (.statement child) := by
      refine ⟨.statement {
        id := result.id
        span := statement.span
        type := result.type
        form := .block bodyResult.statements
      }, ?_, ?_⟩
      · refine ⟨parentNode.1, ?_⟩
        exact congrArg NodeId.statement parentNode.2
      · simpa [nodeChildIds, Node.references, StatementForm.references] using
          (List.mem_map.mpr ⟨child, member, rfl⟩ :
            NodeId.statement child ∈
              bodyResult.statements.map NodeId.statement)
    have coveredEdge : DirectChild finalized.typedSource
        (.statement result.id) (.statement child) :=
      DirectChild.ofTypingSourceExtends resultExtension
        (FlexibleSubstitution.directChild_applySubstitution
          finalized.substitution childEdge)
    exact TemplateScopeCovered.statementChild parentCovered
      resources.graph_closed coveredEdge (fun _ membership => membership)
  have branch : ∃ finalContext facts,
      ActiveLocalContextInvariant result.state finalized.substitution
        finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
    have blockSound := inferStatementFuel_success_block_sound
      statementEq allocationEq success initialInvariant.active roots
      (by
        intro actualBody actualSuccess
        have actualEq : actualBody = bodyResult := by
          rw [bodySuccess] at actualSuccess
          exact (Except.ok.inj actualSuccess).symm
        subst actualBody
        obtain ⟨bodyContext, bodyFacts, bodyInvariant, bodyTyping,
            bodyAgreement⟩ :=
          bodySound bodySuccess resources signaturesEq ownerEq parametersEq
            assumptionsEq signatureFormation functionsCanonical catalog
            signatureParameters allocatedInvariant bodySubstitutionExtension
            (bodyExtension.applySubstitution finalized.substitution)
            resultExtension
            (TypingSourceExtends.trans bodyExtension rawResultExtension)
            (List.Subset.trans bodyIntegerPatternsSubset integerPatternsSubset)
            (List.Subset.trans bodyIntegerLiteralsSubset integerLiteralsSubset)
            (List.Subset.trans bodyRequirementsSubset requirementsSubset)
            bodyCovered
        exact ⟨bodyContext, bodyFacts, bodyInvariant.active, bodyTyping,
          bodyAgreement⟩)
    obtain ⟨facts, active, typing, agreement⟩ := blockSound
    exact ⟨semanticContext, facts, active, typing, agreement⟩
  exact RecursiveStatementInvariant.close_statement_branch initialInvariant
    success signatureFormation functionsCanonical
    (inferStatementFuel_preserves_localBindersBelowNextLocal
      initialInvariant.bindersBelow success)
    resultSubstitutionExtension branch

/-- The while-loop body is checked at the actual condition-result state and
typed under the loop-depth increment.  Its semantic source is the completed
while statement, while coverage and requirements remain anchored to the
whole finalized body. -/
theorem inferStatementFuel_success_whileLoop_of_scoped_body
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {body : Syntax.Block}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .whileLoop condition body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions =
      wholeContext.assumptions)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (resultExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource)
    (rawResultExtension : TypingSourceExtends
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (conditionSound : ∀ {inferredCondition : InferredExpression}
      {conditionState : State},
      Detail.inferExprFuel fuel inferenceContext condition (some .bool)
        allocated = .ok (inferredCondition, conditionState) →
      ExpressionHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        semanticContext inferredCondition.id
        (finalized.substitution.apply inferredCondition.type))
    (bodySound : InferStatementsFuelScopedSoundness fuel) :
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
        result facts := by
  let loopContext : Frontend.SourceInference.Context := {
    inferenceContext with loopDepth := inferenceContext.loopDepth + 1 }
  obtain ⟨inferredCondition, conditionState, bodyResult, conditionSuccess,
      actualBodySuccess, resultEq, contains⟩ :=
    inferStatementFuel_success_whileLoop_facts statementEq allocationEq
      success roots
  obtain ⟨actualConditionState, actualBodyResult,
      ⟨actualCondition, actualConditionSuccess⟩, actualBodySuccess',
      conditionBelow, bodySourceExtension, bodyIntegerPatternsSubset,
      bodyRequirementsSubset⟩ :=
    inferStatementFuel_success_whileLoop_child_provenance statementEq
      allocationEq success initialInvariant.nodesBelow roots
  have conditionStateEq : actualConditionState = conditionState := by
    rw [conditionSuccess] at actualConditionSuccess
    exact (congrArg Prod.snd
      (Except.ok.inj actualConditionSuccess)).symm
  subst actualConditionState
  have bodyResultEq : actualBodyResult = bodyResult := by
    rw [actualBodySuccess] at actualBodySuccess'
    exact (Except.ok.inj actualBodySuccess').symm
  subst actualBodyResult
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical (by
      intro expected member
      simp only [Option.mem_def] at member
      injection member with expectedEq
      subst expected
      simp [Ty.bool]) conditionSuccess
  have conditionReturnBelow :
      expectedReturn.VariablesBelow conditionState.inference.next :=
    allocatedInvariant.returnBelow.weaken conditionProperties.1.next_le
  have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
    (context := loopContext) conditionProperties.2.1 signatureFormation
    functionsCanonical conditionReturnBelow actualBodySuccess
  have bodySubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        bodyResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using
      resultSubstitutionExtension
  have conditionSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        conditionState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans
      bodySubstitutionExtension bodyProperties.1.substitution_extends
  have conditionInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized conditionState semanticContext :=
    allocatedInvariant.inferExprFuel conditionSuccess signatureFormation
      functionsCanonical (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [Ty.bool]) conditionSubstitutionExtension
  have bodyIntegerLiteralsSubset :
      bodyResult.state.integerLiterals ⊆ result.state.integerLiterals := by
    rw [resultEq]
    intro literal member
    simpa [State.restoreLexicalScope, State.recordNode] using member
  have bodyCovered : ∀ child, child ∈ bodyResult.statements →
      TemplateScopeCovered finalized.typedSource semanticContext
        (.statement child) := by
    intro child member
    have childReference : (.statement child : NodeId) ∈
        (StatementForm.whileLoop inferredCondition.id
          bodyResult.statements).references := by
      simp [StatementForm.references, member]
    exact TemplateScopeCovered.statementChild_of_recorded_reference
      contains childReference resultExtension parentCovered
      resources.graph_closed (fun _ membership => membership)
  obtain ⟨bodyFinal, bodyFacts, bodyInvariant, bodyTyping,
      bodyAgreement⟩ :=
    bodySound actualBodySuccess resources (by simpa [loopContext] using signaturesEq)
      (by simpa [loopContext] using ownerEq)
      (by simpa [loopContext] using parametersEq)
      (by simpa [loopContext] using assumptionsEq)
      signatureFormation functionsCanonical catalog signatureParameters
      conditionInvariant bodySubstitutionExtension
      (bodySourceExtension.applySubstitution finalized.substitution)
      resultExtension
      (TypingSourceExtends.trans bodySourceExtension rawResultExtension)
      (List.Subset.trans bodyIntegerPatternsSubset integerPatternsSubset)
      (List.Subset.trans bodyIntegerLiteralsSubset integerLiteralsSubset)
      (List.Subset.trans bodyRequirementsSubset requirementsSubset)
      bodyCovered
  have branch : ∃ finalContext facts,
      ActiveLocalContextInvariant result.state finalized.substitution
        finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
    have conditionTyping := conditionSound conditionSuccess
    have conditionEq : finalized.substitution.apply inferredCondition.type =
        .bool := by
      simpa using Detail.inferExprFuel_expected_type_apply_eq
        conditionSuccess conditionSubstitutionExtension
    subst result
    refine ⟨semanticContext, {
        type := .unit
        hasValue := false
        sawReturn := false
        control := .loop bodyFacts.control
      }, conditionInvariant.active.restoreLexicalScope_recordNode _, ?_, ?_⟩
    · exact whileLoopStatementHasType_afterSubstitution contains
        conditionTyping conditionEq bodyTyping
    · exact StatementResultMatchesFactsAfterSubstitution.whileLoop
        finalized.substitution bodyFacts id _
  exact RecursiveStatementInvariant.close_statement_branch initialInvariant
    success signatureFormation functionsCanonical
    (inferStatementFuel_preserves_localBindersBelowNextLocal
      initialInvariant.bindersBelow success)
    resultSubstitutionExtension branch

/-- The no-else conditional consumes only its actual then-body traversal;
the missing else branch contributes the ordinary unit control fact. -/
theorem inferStatementFuel_success_ifWithoutElse_of_scoped_body
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {thenBody : Syntax.Block}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .ifThen condition thenBody none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions =
      wholeContext.assumptions)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (resultExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource)
    (rawResultExtension : TypingSourceExtends
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (conditionSound : ∀ {inferredCondition : InferredExpression}
      {conditionState : State},
      Detail.inferExprFuel fuel inferenceContext condition (some .bool)
        allocated = .ok (inferredCondition, conditionState) →
      ExpressionHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        semanticContext inferredCondition.id
        (finalized.substitution.apply inferredCondition.type))
    (thenSound : InferStatementsFuelScopedSoundness fuel) :
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
        result facts := by
  obtain ⟨inferredCondition, conditionState, thenResult, conditionSuccess,
      thenSuccess, resultEq, contains⟩ :=
    inferStatementFuel_success_ifWithoutElse_facts statementEq allocationEq
      success roots
  obtain ⟨actualConditionState, actualThenResult,
      ⟨actualCondition, actualConditionSuccess⟩, actualThenSuccess,
      _conditionBelow, thenSourceExtension, thenIntegerPatternsSubset,
      thenRequirementsSubset⟩ :=
    inferStatementFuel_success_ifWithoutElse_child_provenance statementEq
      allocationEq success initialInvariant.nodesBelow roots
  have conditionStateEq : actualConditionState = conditionState := by
    rw [conditionSuccess] at actualConditionSuccess
    exact (congrArg Prod.snd
      (Except.ok.inj actualConditionSuccess)).symm
  subst actualConditionState
  have thenResultEq : actualThenResult = thenResult := by
    rw [thenSuccess] at actualThenSuccess
    exact (Except.ok.inj actualThenSuccess).symm
  subst actualThenResult
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical (by
      intro expected member
      simp only [Option.mem_def] at member
      injection member with expectedEq
      subst expected
      simp [Ty.bool]) conditionSuccess
  have conditionReturnBelow :
      expectedReturn.VariablesBelow conditionState.inference.next :=
    allocatedInvariant.returnBelow.weaken conditionProperties.1.next_le
  have thenProperties := Detail.inferStatementsFuel_inferenceProperties
    conditionProperties.2.1 signatureFormation functionsCanonical
    conditionReturnBelow thenSuccess
  have thenSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        thenResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using
      resultSubstitutionExtension
  have conditionSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        conditionState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans
      thenSubstitutionExtension thenProperties.1.substitution_extends
  have conditionInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized conditionState semanticContext :=
    allocatedInvariant.inferExprFuel conditionSuccess signatureFormation
      functionsCanonical (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [Ty.bool]) conditionSubstitutionExtension
  have thenIntegerLiteralsSubset :
      thenResult.state.integerLiterals ⊆ result.state.integerLiterals := by
    rw [resultEq]
    intro literal member
    simpa [State.restoreLexicalScope, State.recordNode] using member
  have thenCovered : ∀ child, child ∈ thenResult.statements →
      TemplateScopeCovered finalized.typedSource semanticContext
        (.statement child) := by
    intro child member
    have childReference : (.statement child : NodeId) ∈
        (StatementForm.ifThen inferredCondition.id thenResult.statements
          none).references := by
      simp [StatementForm.references, member]
    exact TemplateScopeCovered.statementChild_of_recorded_reference
      contains childReference resultExtension parentCovered
      resources.graph_closed (fun _ membership => membership)
  obtain ⟨thenFinal, thenFacts, thenInvariant, thenTyping,
      thenAgreement⟩ :=
    thenSound thenSuccess resources signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters conditionInvariant thenSubstitutionExtension
      (thenSourceExtension.applySubstitution finalized.substitution)
      resultExtension
      (TypingSourceExtends.trans thenSourceExtension rawResultExtension)
      (List.Subset.trans thenIntegerPatternsSubset integerPatternsSubset)
      (List.Subset.trans thenIntegerLiteralsSubset integerLiteralsSubset)
      (List.Subset.trans thenRequirementsSubset requirementsSubset)
      thenCovered
  have branch : ∃ finalContext facts,
      ActiveLocalContextInvariant result.state finalized.substitution
        finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
    have conditionTyping := conditionSound conditionSuccess
    have conditionEq : finalized.substitution.apply inferredCondition.type =
        .bool := by
      simpa using Detail.inferExprFuel_expected_type_apply_eq
        conditionSuccess conditionSubstitutionExtension
    subst result
    refine ⟨semanticContext, {
        type := .unit
        hasValue := false
        sawReturn := false
        control := thenFacts.control.branches (.ordinary .unit)
      }, conditionInvariant.active.restoreLexicalScope_recordNode _, ?_, ?_⟩
    · exact ifWithoutElseStatementHasType_afterSubstitution contains
        conditionTyping conditionEq thenTyping
    · exact StatementResultMatchesFactsAfterSubstitution.ifWithoutElse
        finalized.substitution thenFacts id _
  exact RecursiveStatementInvariant.close_statement_branch initialInvariant
    success signatureFormation functionsCanonical
    (inferStatementFuel_preserves_localBindersBelowNextLocal
      initialInvariant.bindersBelow success)
    resultSubstitutionExtension branch

/-- Both branches of a successful conditional are typed from their concrete
traces.  The second branch starts from the restored condition scope, while
both branches' roots remain direct children of the completed parent node. -/
theorem inferStatementFuel_success_ifWithElse_of_scoped_bodies
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {thenBody elseBody : Syntax.Block}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .ifThen condition thenBody
      (some elseBody))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions =
      wholeContext.assumptions)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (resultExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource)
    (rawResultExtension : TypingSourceExtends
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (conditionSound : ∀ {inferredCondition : InferredExpression}
      {conditionState : State},
      Detail.inferExprFuel fuel inferenceContext condition (some .bool)
        allocated = .ok (inferredCondition, conditionState) →
      ExpressionHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        semanticContext inferredCondition.id
        (finalized.substitution.apply inferredCondition.type))
    (branchSound : InferStatementsFuelScopedSoundness fuel) :
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
        result facts := by
  obtain ⟨inferredCondition, conditionState, thenResult, elseResult,
      conditionSuccess, thenSuccess, elseSuccess, resultEq, contains⟩ :=
    inferStatementFuel_success_ifWithElse_facts statementEq allocationEq
      success roots
  obtain ⟨actualConditionState, actualThenResult, actualElseResult,
      ⟨actualCondition, actualConditionSuccess⟩, actualThenSuccess,
      actualElseSuccess, _conditionBelow, _elseInputBelow,
      thenSourceExtension, elseSourceExtension,
      thenIntegerPatternsSubset, elseIntegerPatternsSubset,
      thenRequirementsSubset, elseRequirementsSubset⟩ :=
    inferStatementFuel_success_ifWithElse_child_provenance statementEq
      allocationEq success initialInvariant.nodesBelow roots
  have conditionStateEq : actualConditionState = conditionState := by
    rw [conditionSuccess] at actualConditionSuccess
    exact (congrArg Prod.snd
      (Except.ok.inj actualConditionSuccess)).symm
  subst actualConditionState
  have thenResultEq : actualThenResult = thenResult := by
    rw [thenSuccess] at actualThenSuccess
    exact (Except.ok.inj actualThenSuccess).symm
  subst actualThenResult
  have elseResultEq : actualElseResult = elseResult := by
    rw [elseSuccess] at actualElseSuccess
    exact (Except.ok.inj actualElseSuccess).symm
  subst actualElseResult
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical (by
      intro expected member
      simp only [Option.mem_def] at member
      injection member with expectedEq
      subst expected
      simp [Ty.bool]) conditionSuccess
  have conditionReturnBelow :
      expectedReturn.VariablesBelow conditionState.inference.next :=
    allocatedInvariant.returnBelow.weaken conditionProperties.1.next_le
  have thenProperties := Detail.inferStatementsFuel_inferenceProperties
    conditionProperties.2.1 signatureFormation functionsCanonical
    conditionReturnBelow thenSuccess
  have thenBelow : thenResult.state.NodesBelowNextOccurrence :=
    (Detail.inferStatementsFuel_occurrenceBoundExtends thenSuccess
      ).nodesBelowNextOccurrence
        ((Detail.inferExprFuel_occurrenceBoundExtends conditionSuccess
          ).nodesBelowNextOccurrence allocatedInvariant.nodesBelow)
  have restoredProperties := State.restoreLexicalScope_inferenceProperties
    conditionProperties.2.1 thenProperties.1
  have elseReturnBelow : expectedReturn.VariablesBelow
      (thenResult.state.restoreLexicalScope
        conditionState.lexicalScope).inference.next :=
    conditionReturnBelow.weaken restoredProperties.1.next_le
  have elseProperties := Detail.inferStatementsFuel_inferenceProperties
    restoredProperties.2 signatureFormation functionsCanonical
    elseReturnBelow elseSuccess
  have elseSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        elseResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using
      resultSubstitutionExtension
  have elseInputSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        (thenResult.state.restoreLexicalScope
          conditionState.lexicalScope).inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans
      elseSubstitutionExtension elseProperties.1.substitution_extends
  have conditionSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        conditionState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans
      elseInputSubstitutionExtension restoredProperties.1.substitution_extends
  have conditionInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized conditionState semanticContext :=
    allocatedInvariant.inferExprFuel conditionSuccess signatureFormation
      functionsCanonical (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [Ty.bool]) conditionSubstitutionExtension
  have elseInputInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized
      (thenResult.state.restoreLexicalScope conditionState.lexicalScope)
      semanticContext :=
    conditionInvariant.restoreLexicalScope thenProperties.1 thenBelow
      (Detail.inferStatementsFuel_nextLocal_le thenSuccess)
      elseInputSubstitutionExtension
  have thenSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        thenResult.state.inference.substitution := by
    simpa [State.restoreLexicalScope] using
      elseInputSubstitutionExtension
  have elseIntegerLiteralsSubset :
      elseResult.state.integerLiterals ⊆ result.state.integerLiterals := by
    rw [resultEq]
    intro literal member
    simpa [State.restoreLexicalScope, State.recordNode] using member
  have thenIntegerLiteralsSubset :
      thenResult.state.integerLiterals ⊆ result.state.integerLiterals := by
    have throughElse : thenResult.state.integerLiterals ⊆
        elseResult.state.integerLiterals := by
      simpa [State.restoreLexicalScope] using
        (Detail.inferStatementsFuel_integerLiterals_subset elseSuccess)
    exact List.Subset.trans throughElse elseIntegerLiteralsSubset
  have thenCovered : ∀ child, child ∈ thenResult.statements →
      TemplateScopeCovered finalized.typedSource semanticContext
        (.statement child) := by
    intro child member
    have childReference : (.statement child : NodeId) ∈
        (StatementForm.ifThen inferredCondition.id thenResult.statements
          (some elseResult.statements)).references := by
      simp [StatementForm.references, member]
    exact TemplateScopeCovered.statementChild_of_recorded_reference
      contains childReference resultExtension parentCovered
      resources.graph_closed (fun _ membership => membership)
  obtain ⟨thenFinal, thenFacts, thenInvariant, thenTyping,
      thenAgreement⟩ :=
    branchSound thenSuccess resources signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters conditionInvariant thenSubstitutionExtension
      (thenSourceExtension.applySubstitution finalized.substitution)
      resultExtension
      (TypingSourceExtends.trans thenSourceExtension rawResultExtension)
      (List.Subset.trans thenIntegerPatternsSubset integerPatternsSubset)
      (List.Subset.trans thenIntegerLiteralsSubset integerLiteralsSubset)
      (List.Subset.trans thenRequirementsSubset requirementsSubset)
      thenCovered
  have elseIntegerPatternsSubset' :=
    List.Subset.trans elseIntegerPatternsSubset integerPatternsSubset
  have elseIntegerLiteralsSubset' :=
    List.Subset.trans elseIntegerLiteralsSubset integerLiteralsSubset
  have elseRequirementsSubset' :=
    List.Subset.trans elseRequirementsSubset requirementsSubset
  have elseCovered : ∀ child, child ∈ elseResult.statements →
      TemplateScopeCovered finalized.typedSource semanticContext
        (.statement child) := by
    intro child member
    have childReference : (.statement child : NodeId) ∈
        (StatementForm.ifThen inferredCondition.id thenResult.statements
          (some elseResult.statements)).references := by
      simp [StatementForm.references, member]
    exact TemplateScopeCovered.statementChild_of_recorded_reference
      contains childReference resultExtension parentCovered
      resources.graph_closed (fun _ membership => membership)
  obtain ⟨elseFinal, elseFacts, elseInvariant, elseTyping,
      elseAgreement⟩ :=
    branchSound elseSuccess resources signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters elseInputInvariant elseSubstitutionExtension
      (elseSourceExtension.applySubstitution finalized.substitution)
      resultExtension
      (TypingSourceExtends.trans elseSourceExtension rawResultExtension)
      elseIntegerPatternsSubset' elseIntegerLiteralsSubset'
      elseRequirementsSubset' elseCovered
  have branch : ∃ finalContext facts,
      ActiveLocalContextInvariant result.state finalized.substitution
        finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
    have conditionTyping := conditionSound conditionSuccess
    have conditionEq : finalized.substitution.apply inferredCondition.type =
        .bool := by
      simpa using Detail.inferExprFuel_expected_type_apply_eq
        conditionSuccess conditionSubstitutionExtension
    subst result
    refine ⟨semanticContext, {
        type := if thenFacts.sawReturn && elseFacts.sawReturn then
          finalized.substitution.apply expectedReturn
        else
          .unit
        hasValue := thenFacts.sawReturn && elseFacts.sawReturn
        sawReturn := thenFacts.sawReturn && elseFacts.sawReturn
        control := thenFacts.control.branches elseFacts.control
      }, conditionInvariant.active.restoreLexicalScope_recordNode _, ?_, ?_⟩
    · exact ifWithElseStatementHasType_afterSubstitution contains
        conditionTyping conditionEq thenTyping elseTyping thenAgreement
        elseAgreement elseSubstitutionExtension
    · exact StatementResultMatchesFactsAfterSubstitution.ifWithElse
        thenAgreement elseAgreement elseSubstitutionExtension id _
  exact RecursiveStatementInvariant.close_statement_branch initialInvariant
    success signatureFormation functionsCanonical
    (inferStatementFuel_preserves_localBindersBelowNextLocal
      initialInvariant.bindersBelow success)
    resultSubstitutionExtension branch

end Solcore.SourceSemantics.SourceInferenceSoundness
