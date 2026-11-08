import Solcore.SourceSemantics.Internal.Inference.RootedContracts
import Solcore.SourceSemantics.Internal.Inference.StatementDispatch
import Solcore.SourceSemantics.Internal.Privacy.Lifetimes
import Solcore.SourceSemantics.SourceProgramCheckingSoundness

/-!
# Rooted soundness

Exact source-prefix typing follows from the retained contract, and it reaches the checked body. Main
theorems:
`SourceInferenceSoundness.SelectedCheckedBodyTypingBridge.checkedBodyStatementsHaveType_of_inferStatementsFuel_sound`.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualRecursiveSoundness
/-! Exact source-prefix expression typing is recovered from the corrected
retained contract, and whole-body inference retains actual context provenance. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

theorem actualInferExprFuelScopedSoundness_of_retainedSoundness
    {fuel : Nat}
    (retainedSound : ActualInferExprFuelRetainedSoundness fuel) :
    ActualInferExprFuelScopedSoundness fuel := by
  intro wholeContext inferenceContext wholeReturn expression expected initial
    resultState evidenceState inferred roots finalized semanticSource
    frames semanticContext success resources interfaces resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    resultExtension semanticExtension rawExtension integerPatternsSubset
    integerLiteralsSubset requirementsSubset covered actualCovered
  have resultToFinal : TypingSourceExtends
      ((resultState.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource :=
    TypingSourceExtends.trans resultExtension semanticExtension
  have requirementsRetained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id :=
    ExpressionRequirementsRetainedAt.ofTypingSourceExtends
      finalized.substitution resultToFinal
  have childrenRetained : ExpressionDirectChildrenRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id :=
    ExpressionDirectChildrenRetainedAt.ofTypingSourceExtends
      finalized.substitution resultToFinal
  have base := retainedSound success resources interfaces resultSubstitutionExtension
    signaturesEq ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    (ProperDescendantsPreserved.ofTypingSourceExtends resultToFinal)
    (RawProperDescendantsPreserved.ofTypingSourceExtends rawExtension)
    integerPatternsSubset integerLiteralsSubset requirementsSubset
    requirementsRetained
    (ExpressionCoercionPrimariesRetainedAt.ofTypingSourceExtends finalized.substitution resultToFinal)
    (ExpressionOperatorSiteRetainedAt.ofTypingSourceExtends finalized.substitution resultToFinal)
    childrenRetained covered
    (ProperDescendantsPreserved.ofTypingSourceExtends resultExtension) actualCovered
  cases base with
  | @intro node rawType plan contains typeEq formType rawAdmissible
      requirements =>
      have evidenceMember : Node.expression node ∈
          (evidenceState.toTypedSource roots).nodes :=
        rawExtension.nodes_prefix.subset contains.1
      have finalAdmissible : TypeAdmissible semanticContext
          (finalized.substitution.apply inferred.type) := by
        have nodeAdmissible := resources.expressionTypeAdmissible_in_active
          evidenceMember
          (invariant.typeParameterBinders (by
            simpa [ownerEq, typeParametersEq] using canonical))
          invariant.signatures_eq_whole invariant.typeParametersEq
          invariant.declarationEq invariant.residual
        simpa only [typeEq] using nodeAdmissible
      exact
        (ExpressionTypingBase.intro contains typeEq formType rawAdmissible
          requirements).expressionHasType
          (ExpressionNodesPreservedAt.ofTypingSourceExtends resultExtension)
          finalAdmissible


theorem actualInferStatementsFuelSoundness_of_scopedSoundness
    {fuel : Nat}
    (scopedSound : ActualInferStatementsFuelScopedSoundness fuel) :
    ActualInferStatementsFuelSoundness fuel := by
  intro inferenceContext statements expectedReturn initial result
    evidenceState roots finalized frames semanticContext success resources interfaces
    signatureFormation functionsCanonical catalog signatureParameters
    initialActive actual operational returnAdmissible initialSchemeIsolation ready returnBelow bindersBelow
    initialBelow
    finalSubstitutionExtension rawResultExtension resultExtension
    integerPatternsSubset integerLiteralsSubset requirementsSubset
    signaturesEq typeParametersEq declarationEq residual
    solvedRequirementsEq assumptionsMono covered actualCovered
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
    schemeIsolation := initialSchemeIsolation
    substitutionExtension := initialSubstitutionExtension
    signaturesEq
    typeParametersEq
    declarationEq
    residual
    solvedRequirementsEq
    assumptionsMono
  }
  obtain ⟨finalContext, facts, finalInvariant, finalActual, finalOperational, typing, agreement⟩ :=
    scopedSound (wholeContext := inferenceContext)
      (wholeReturn := expectedReturn)
      (semanticSource := finalized.typedSource)
      success resources interfaces rfl rfl rfl rfl signatureFormation
      functionsCanonical catalog signatureParameters initialInvariant actual operational returnAdmissible
      finalSubstitutionExtension resultExtension
      (TypingSourceExtends.refl _) rawResultExtension
      integerPatternsSubset integerLiteralsSubset requirementsSubset covered actualCovered
  exact ⟨finalContext, facts, finalInvariant.active, finalActual, finalOperational, typing, agreement⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualRootedSoundness
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

theorem actualInferExprFuelRootedSoundness_of_retainedSoundness
    {fuel : Nat} (retainedSound : ActualInferExprFuelRetainedSoundness fuel) :
    ActualInferExprFuelRootedSoundness fuel := by
  intro wholeContext inferenceContext wholeReturn expression expected initial
    resultState evidenceState inferred roots finalized semanticSource
    frames semanticContext success resources interfaces resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    resultPreserved rawPreserved integerPatternsSubset
    integerLiteralsSubset requirementsSubset covered actualCovered
  have finalPreserved : SubtreePreserved finalized.substitution
      (resultState.toTypedSource roots) finalized.typedSource (.expression inferred.id) := by
    rw [resources.source_eq]
    exact rawPreserved.substituted finalized.substitution
  have finalNodes : ExpressionNodesPreservedAt [inferred.id]
      ((resultState.toTypedSource roots).applySubstitution finalized.substitution)
      finalized.typedSource := by
    intro id node member contains
    have same : id = inferred.id := by simpa using member
    subst id
    exact finalPreserved.subgraph.containsExpression contains (.inl rfl)
  have requirementsRetained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id := by
    intro node requirement contains member
    have found := finalNodes (by simp)
      (FlexibleSubstitution.ContainsExpression.applySubstitution finalized.substitution contains)
    apply found.primaryRequirementOccursAt
    simpa [ExpressionNode.applySubstitution] using member
  have childrenRetained : ExpressionDirectChildrenRetainedAt
      (resultState.toTypedSource roots) finalized.typedSource inferred.id :=
    ExpressionDirectChildrenRetainedAt.ofExpressionNodesPreservedAt finalNodes
  have base := retainedSound success resources interfaces resultSubstitutionExtension
    signaturesEq ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    finalPreserved.proper rawPreserved.proper integerPatternsSubset integerLiteralsSubset
    requirementsSubset requirementsRetained
    (ExpressionCoercionPrimariesRetainedAt.ofExpressionNodesPreservedAt finalized.substitution finalNodes)
    (ExpressionOperatorSiteRetainedAt.ofExpressionNodesPreservedAt finalized.substitution finalNodes)
    childrenRetained covered
    resultPreserved.proper actualCovered
  cases base with
  | @intro node rawType plan contains typeEq formType rawAdmissible requirements =>
      have evidenceMember : Node.expression node ∈
          (evidenceState.toTypedSource roots).nodes :=
        rawPreserved.nodes (.expression node) contains.1
          (.inl (congrArg NodeId.expression contains.2))
      have finalAdmissible : TypeAdmissible semanticContext
          (finalized.substitution.apply inferred.type) := by
        have nodeAdmissible := resources.expressionTypeAdmissible_in_active
          evidenceMember
          (invariant.typeParameterBinders (by
            simpa [ownerEq, typeParametersEq] using canonical))
          invariant.signatures_eq_whole invariant.typeParametersEq
          invariant.declarationEq invariant.residual
        simpa only [typeEq] using nodeAdmissible
      have semanticNodes : ExpressionNodesPreservedAt [inferred.id]
          ((resultState.toTypedSource roots).applySubstitution finalized.substitution)
          semanticSource := by
        intro id selected member found
        have same : id = inferred.id := by simpa using member
        subst id
        exact resultPreserved.subgraph.containsExpression found (.inl rfl)
      exact (ExpressionTypingBase.intro contains typeEq formType rawAdmissible requirements
        ).expressionHasType semanticNodes finalAdmissible

theorem actualInferExprFuelScopedSoundness_of_rootedSoundness
    {fuel : Nat} (rooted : ActualInferExprFuelRootedSoundness fuel) :
    ActualInferExprFuelScopedSoundness fuel := by
  intro wholeContext inferenceContext wholeReturn expression expected initial
    resultState evidenceState inferred roots finalized semanticSource
    frames semanticContext success resources interfaces resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    resultExtension _ rawExtension integerPatternsSubset
    integerLiteralsSubset requirementsSubset covered actualCovered
  exact rooted success resources interfaces resultSubstitutionExtension signaturesEq
    ownerEq typeParametersEq assumptionsEq signatureFormation
    functionsCanonical catalog canonical invariant actual operational expectedBelow expectedAdmissible
    (SubtreePreserved.ofTypingSourceExtends resultExtension)
    (RawSubtreePreserved.ofTypingSourceExtends rawExtension)
    integerPatternsSubset integerLiteralsSubset requirementsSubset covered actualCovered

theorem actualInferStatementFuelScopedSoundness_of_rootedSoundness
    {fuel : Nat} (rooted : ActualInferStatementFuelRootedSoundness fuel) :
    ActualInferStatementFuelScopedSoundness fuel := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statement
    initial result evidenceState roots finalized semanticSource frames semanticContext
    success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq
    signatureFormation functionsCanonical catalog signatureParameters
    invariant actual operational returnAdmissible substitutionExtension resultExtension _ rawExtension
    integerPatternsSubset integerLiteralsSubset requirementsSubset covered actualCovered
  exact rooted success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq
    signatureFormation functionsCanonical catalog signatureParameters invariant actual operational returnAdmissible
    substitutionExtension (SubtreePreserved.ofTypingSourceExtends resultExtension)
    (RawSubtreePreserved.ofTypingSourceExtends rawExtension)
    integerPatternsSubset integerLiteralsSubset requirementsSubset covered actualCovered

theorem actualInferStatementsFuelScopedSoundness_of_rootedSoundness
    {fuel : Nat} (rooted : ActualInferStatementsFuelRootedSoundness fuel) :
    ActualInferStatementsFuelScopedSoundness fuel := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statements
    initial result evidenceState roots finalized semanticSource frames semanticContext
    success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq
    signatureFormation functionsCanonical catalog signatureParameters
    invariant actual operational returnAdmissible substitutionExtension resultExtension _ rawExtension
    integerPatternsSubset integerLiteralsSubset requirementsSubset covered actualCovered
  exact rooted success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq
    signatureFormation functionsCanonical catalog signatureParameters invariant actual operational returnAdmissible
    substitutionExtension (fun _ _ => SubtreePreserved.ofTypingSourceExtends resultExtension)
    (fun _ _ => RawSubtreePreserved.ofTypingSourceExtends rawExtension)
    integerPatternsSubset integerLiteralsSubset requirementsSubset covered actualCovered

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizedMatchState
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

theorem safe_active_iff {state : State} {type : Ty} :
    Safe (activeSchemeQuantifiers state) state type ↔
      ∀ binder ∈ state.localBinders, Safe binder.scheme.quantified state type := by
  constructor
  · intro all binder member v occurs quantified
    exact all v occurs (List.mem_flatMap.mpr ⟨binder, member, quantified⟩)
  · intro each v occurs active
    obtain ⟨binder, member, quantified⟩ := List.mem_flatMap.mp active
    exact each binder member v occurs quantified

theorem GeneralizedActualStateInvariant.pattern_safe_transport
    {fuel : Nat} {context : SourceInference.Context} {pattern : Syntax.Pattern}
    {expected type : Ty} {initial final : State} {inferred : TypedMatchPattern} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (expectedBelow : expected.VariablesBelow initial.inference.next)
    (expectedSafe : Safe (activeSchemeQuantifiers initial) initial expected)
    (typeSafe : Safe (activeSchemeQuantifiers initial) initial type)
    (accepted : Detail.inferMatchPatternFuel fuel context pattern expected initial = .ok (inferred, final)) :
    Safe (activeSchemeQuantifiers final) final type := by
  have scope := ProtectedVariables.inferMatchPatternFuel_scope accepted
  have privacy := ProtectedVariables.inferMatchPatternFuel_private ready expectedBelow formation
    (activeSchemeQuantifiers_below_next invariant.quantifiersBelow) expectedSafe invariant.privacy.all_live accepted
  rw [scope.quantified]
  exact privacy.1 type typeSafe

theorem GeneralizedActualStateInvariant.ofMatchCases
    {fuel : Nat} {context : SourceInference.Context} {cases : List Syntax.MatchCase}
    {expected scrutinee : Ty} {initial : State} {result : Detail.MatchCasesResult}
    {outerScope : LexicalScope} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (scrutineeBelow : scrutinee.VariablesBelow initial.inference.next)
    (scrutineeSafe : Safe (activeSchemeQuantifiers initial) initial scrutinee)
    (returnBelow : expected.VariablesBelow initial.inference.next)
    (returnSafe : Safe (activeSchemeQuantifiers initial) initial expected)
    (scope : initial.lexicalScope = outerScope)
    (accepted : Detail.inferMatchCasesFuel fuel context scrutinee expected outerScope cases initial = .ok result) :
    GeneralizedActualStateInvariant result.state source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have properties := Detail.inferMatchCasesFuel_inferenceProperties ready formation canonical
    scrutineeBelow returnBelow scope accepted
  have binders : result.state.localBinders = initial.localBinders :=
    congrArg LexicalScope.binders ((Detail.inferMatchCasesFuel_success_lexicalScope_eq scope accepted).trans scope.symm)
  refine ⟨⟨pending, (actualLedgerFamily fuel).statements.matchCases accepted ledger⟩,
    invariant.origins.congr_localBinders binders,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow binders properties.1.next_le,
    ?_, invariant.backed.transport (fun _ member => binders ▸ member)
      (Detail.inferMatchCasesFuel_requirements_subset accepted) properties.1.substitution_extends⟩
  intro binder member
  have old : binder ∈ initial.localBinders := binders ▸ member
  exact (ProtectedVariables.inferMatchCasesFuel_private binder.scheme.quantified fuel context
    scrutinee expected outerScope cases initial ready invariant.requirements
    (invariant.quantifiersBelow binder old) (invariant.privacy binder old) catalog formation canonical
    scrutineeBelow (safe_active_iff.mp scrutineeSafe binder old) returnBelow
    (safe_active_iff.mp returnSafe binder old) scope result accepted).2.1

theorem GeneralizedActualStateInvariant.scrutinees_safe_transport
    {fuel : Nat} {context : SourceInference.Context} {span : Syntax.SourceSpan}
    {sources : List Syntax.Expr} {initial final : State}
    {inferred : InferredExpression} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (accepted : inferMatchScrutineesFuel fuel context span sources initial = .ok (inferred, final)) :
    SafeTransport (activeSchemeQuantifiers initial) initial final := by
  have finish (elements : List InferredExpression) (after : State)
      (elementsAccepted : Detail.inferExprsFuel fuel context sources initial = .ok (elements, after))
      (recorded : (pure ({
          id := after.allocateExpressionId.1
          type := Ty.productMany (elements.map (·.type)) },
        after.allocateExpressionId.2.recordNode (.expression {
          id := after.allocateExpressionId.1, span,
          type := Ty.productMany (elements.map (·.type)), form := .tuple (elements.map (·.id))})) :
          Except Error (InferredExpression × State)) = .ok (inferred, final)) :
      SafeTransport (activeSchemeQuantifiers initial) initial final := by
    have same := Except.ok.inj recorded
    cases same
    exact (inferExprsFuel_private (activeSchemeQuantifiers initial) fuel context sources initial
      ready invariant.requirements (activeSchemeQuantifiers_below_next invariant.quantifiersBelow)
      invariant.privacy.all_live catalog formation canonical _ elementsAccepted).1
  cases sources with
  | nil =>
    unfold inferMatchScrutineesFuel at accepted
    cases elementsAccepted : Detail.inferExprsFuel fuel context [] initial with
    | error error => simp [elementsAccepted, bind, Except.bind] at accepted
    | ok pair =>
      obtain ⟨elements, after⟩ := pair
      simp only [elementsAccepted, bind, Except.bind] at accepted
      exact finish elements after elementsAccepted accepted
  | cons first rest =>
    cases rest with
    | nil =>
      exact (inferExprFuel_private (activeSchemeQuantifiers initial) fuel context first none initial
        ready invariant.requirements (activeSchemeQuantifiers_below_next invariant.quantifiersBelow)
        invariant.privacy.all_live catalog formation canonical (by simp) (by simp) _ accepted).1
    | cons second tail =>
      unfold inferMatchScrutineesFuel at accepted
      cases elementsAccepted : Detail.inferExprsFuel fuel context (first :: second :: tail) initial with
      | error error => simp [elementsAccepted, bind, Except.bind] at accepted
      | ok pair =>
        obtain ⟨elements, after⟩ := pair
        simp only [elementsAccepted, bind, Except.bind] at accepted
        exact finish elements after elementsAccepted accepted

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedCheckedBodyTypingBridge
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000

namespace Solcore.SourceSemantics.SourceInferenceSoundness.SelectedCheckedBodyTypingBridge

open Frontend Frontend.SourceInference TypeSystem

/-- A fixed monomorphic input-binder sequence determines its final lexical
context uniquely.  This lets a single recursive typing derivation supply the
same `BodyFacts` to every input extension admitted by the checker header. -/
private theorem monoBindersExtend_final_unique
    {owner : Resolved.DeclarationId} {base first second : SourceSemantics.Context}
    {binders : List TypedBinder} {types : List Ty}
    (left : MonoBindersExtend owner base binders types first)
    (right : MonoBindersExtend owner base binders types second) :
    first = second := by
  induction left generalizing second with
  | nil context =>
      cases right
      rfl
  | @cons context middle first binder binders type types scheme head tail ih =>
      cases right with
      | cons _ otherHead otherTail =>
          cases head
          cases otherHead
          exact ih otherTail

/-- Statement-root encoding is injective on lists. -/
private theorem statementRoots_injective
    {first second : List StatementId}
    (equal : first.map NodeId.statement = second.map NodeId.statement) :
    first = second := by
  induction first generalizing second with
  | nil =>
      cases second <;> simp at equal ⊢
  | cons head rest induction =>
      cases second with
      | nil => simp at equal
      | cons other others =>
          simp only [List.map_cons, List.cons.injEq] at equal
          rcases equal with ⟨headEq, restEq⟩
          have : head = other := NodeId.statement.inj headEq
          subst other
          simp [induction restEq]

private theorem monoBindersExtend_solvedRequirements_eq
    {owner : Resolved.DeclarationId}
    {base final : SourceSemantics.Context}
    {binders : List TypedBinder} {types : List Ty}
    (extension : MonoBindersExtend owner base binders types final) :
    final.solvedRequirements = base.solvedRequirements := by
  induction extension with
  | nil => rfl
  | cons _ head _ induction =>
      exact induction.trans head.context_fields.2.2.2.2

private theorem monoBindersExtend_signatures_eq
    {owner : Resolved.DeclarationId}
    {base final : SourceSemantics.Context}
    {binders : List TypedBinder} {types : List Ty}
    (extension : MonoBindersExtend owner base binders types final) :
    final.signatures = base.signatures := by
  induction extension with
  | nil => rfl
  | cons _ head _ induction =>
      exact induction.trans head.context_fields.1

private theorem monoBindersExtend_scope_fields
    {owner : Resolved.DeclarationId}
    {base final : SourceSemantics.Context}
    {binders : List TypedBinder} {types : List Ty}
    (extension : MonoBindersExtend owner base binders types final) :
    final.typeParameters = base.typeParameters ∧
      final.currentDeclaration = base.currentDeclaration ∧
        final.residualTypeVariables = base.residualTypeVariables := by
  induction extension with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons _ head _ induction =>
      exact ⟨induction.1.trans head.context_fields.2.2.1,
        induction.2.1.trans head.context_fields.2.1,
        induction.2.2.trans head.residualTypeVariables_eq⟩

/-- Return-type unification changes neither the owner, inputs, nor occurrence
nodes of the source carrier. -/
private theorem unify_toTypedSource_eq
    {state unified : State} {left right : Ty} {roots : List NodeId}
    (success : Detail.unify state left right = .ok unified) :
    unified.toTypedSource roots = state.toTypedSource roots := by
  have headerEq := Detail.unify_state_header success
  have ownerEq : unified.owner = state.owner := by
    have projected := congrArg State.Header.owner headerEq
    simpa [State.header] using projected
  have inputsEq : unified.inputs = state.inputs := by
    have projected := congrArg State.Header.inputs headerEq
    simpa [State.header] using projected
  have nodesEq := (Detail.unify_occurrenceState_eq success).1
  simp [State.toTypedSource, ownerEq, inputsEq, nodesEq]

private theorem monoBindersExtend_typeWellFormed
    {owner : Resolved.DeclarationId} {base final : SourceSemantics.Context}
    {binders : List TypedBinder} {types : List Ty} {type : Ty}
    (extension : MonoBindersExtend owner base binders types final)
    (wellFormed : TypeWellFormed base type) : TypeWellFormed final type := by
  induction extension with
  | nil => exact wellFormed
  | cons _ head _ induction =>
      cases head
      exact induction (wellFormed.withLocal _ _ _)

/-- Once recursive statement inference has its closed soundness theorem, a
successful body check satisfies the statement-only checker proposition with
one shared facts witness for every compatible lexical context. -/
theorem checkedBodyStatementsHaveType_of_inferStatementsFuel_sound
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (header : CheckedBodyHeaderWellFormed signatures signature checked)
    (predicatesFixed :
      signature.scheme.predicates.map
        (TypedTraitResolution.applySubstitution checked.substitution) =
          signature.scheme.predicates)
    (signatureFormation : ProgramSignatureFormationValidated signatures)
    (functionsCanonical : ∀ candidate ∈ signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed signatures)
    (signatureParameters : SignatureParametersWellFormed signature.id
      signature.scheme.parameters)
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked)
    (interfaces : ExecutableCoercionInterfaces.BodyInterfaces signatures checked)
    (sourceMonomorphic : ExecutableBinderInterfaces.SourceMonomorphic checked.typedBody)
    (recursiveSound : ActualInferStatementsFuelSoundness fuel) :
    CheckedBodyStatementsHaveType signatures signature checked := by
  intro statements roots
  obtain ⟨declaration, body, finalState, result, found, inferred, unified,
    finalized, checkedEq⟩ :=
    checkFunctionBody_success_witness success
  have declarationIdEq : declaration.id = signature.id :=
    (ProgramEnvironment.declaration?_sound found).2
  have substitutionEq : checked.substitution = result.substitution := by
    simp [checkedEq]
  obtain ⟨canonicalContext, canonicalExtension⟩ := header.inputs_extend
  let initial := State.initial declaration.id
    ((signature.parameterNames.zip signature.parameterTypes).map
      fun parameter => (parameter.1, Scheme.mono parameter.2))
    signature.parameterComptime
  have inputExtension : MonoBindersExtend declaration.id
      (checkedBodyContext signatures signature checked)
      (initial.localBinders.map
        (TypedBinder.applySubstitution result.substitution))
      signature.parameterTypes canonicalContext := by
    have inputsEq :=
      checkFunctionBody_success_typedBody_inputs success
    rw [inputsEq] at canonicalExtension
    rw [substitutionEq] at canonicalExtension
    rw [← declarationIdEq] at canonicalExtension
    simpa only [initial, State.initial_inputs_eq_localBinders] using
      canonicalExtension
  have initialInvariant : ActiveLocalContextInvariant initial
      result.substitution canonicalContext := by
    constructor
    · apply LocalEnvironmentAligned.ofInitialMonoBindersExtend
        declaration.id
        ((signature.parameterNames.zip signature.parameterTypes).map
          fun parameter => (parameter.1, Scheme.mono parameter.2))
        signature.parameterComptime result.substitution
        (context := checkedBodyContext signatures signature checked)
        (final := canonicalContext) (types := signature.parameterTypes)
        rfl rfl
      exact inputExtension
    · apply ActiveLocalFormation.ofMonoBindersExtend
      exact inputExtension
  have initialSchemeIsolation : ActiveSchemeQuantifierIsolation initial := by
    apply activeSchemeQuantifierIsolation_initial_mono
    intro entry member
    rcases List.mem_map.mp member with ⟨parameter, _, rfl⟩
    rfl
  have initialReady : initial.InferenceReady := by
    simpa only [initial] using State.InferenceReady.initial declaration.id
      ((signature.parameterNames.zip signature.parameterTypes).map
        fun parameter => (parameter.1, Scheme.mono parameter.2))
      signature.parameterComptime
  have returnBelow : (Ty.productMany signature.returnTypes).VariablesBelow
      initial.inference.next := by
    apply Ty.variablesBelow_productMany
    intro returnType member
    have closed := StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil
      (header.return_types returnType member)
    intro metavariable free
    rw [closed] at free
    simp at free
  have initialBindersBelow : initial.LocalBindersBelowNextLocal := by
    simpa only [initial] using State.initial_localBindersBelowNextLocal
      declaration.id
      ((signature.parameterNames.zip signature.parameterTypes).map
        fun parameter => (parameter.1, Scheme.mono parameter.2))
      signature.parameterComptime
  have initialBelow : initial.NodesBelowNextOccurrence :=
    State.initial_nodesBelowNextOccurrence declaration.id
      ((signature.parameterNames.zip signature.parameterTypes).map
        fun parameter => (parameter.1, Scheme.mono parameter.2))
      signature.parameterComptime
  have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
    initialReady signatureFormation functionsCanonical returnBelow inferred
  have returnBelowBody :
      (Ty.productMany signature.returnTypes).VariablesBelow
        body.state.inference.next :=
    returnBelow.weaken bodyProperties.1.next_le
  have unifyProgress : body.state.InferenceProgress finalState :=
    Detail.unify_inferenceProgress bodyProperties.2.1.solved
      bodyProperties.2.2 returnBelowBody unified
  have unifiedReady : finalState.InferenceReady :=
    Detail.unify_preserves_inferenceReady bodyProperties.2.1
      bodyProperties.2.2 returnBelowBody unified
  have sourceEq :
      (body.state.toTypedSource (body.statements.map NodeId.statement)).applySubstitution
        result.substitution = result.typedSource := by
    calc
      (body.state.toTypedSource (body.statements.map NodeId.statement)).applySubstitution
          result.substitution =
          (finalState.toTypedSource (body.statements.map NodeId.statement)).applySubstitution
            result.substitution := by
              rw [unify_toTypedSource_eq unified]
      _ = result.typedSource := (Detail.finalize_typedSource finalized).symm
  have sourceExtends : TypingSourceExtends
      ((body.state.toTypedSource (body.statements.map NodeId.statement)).applySubstitution
        result.substitution) checked.typedBody := by
    rw [sourceEq, checkedEq]
    exact TypingSourceExtends.refl result.typedSource
  have rawSourceExtends : TypingSourceExtends
      (body.state.toTypedSource
        (body.statements.map NodeId.statement))
      (finalState.toTypedSource
        (body.statements.map NodeId.statement)) := by
    rw [unify_toTypedSource_eq unified]
    exact TypingSourceExtends.refl _
  have patternsSubset : body.state.integerPatterns ⊆
      finalState.integerPatterns := by
    rw [Detail.unify_integerPatterns unified]
    intro pattern member
    exact member
  have literalsSubset : body.state.integerLiterals ⊆
      finalState.integerLiterals := by
    rw [Detail.unify_integerLiterals unified]
    intro literal member
    exact member
  have requirementsSubset : body.state.requirements ⊆
      finalState.requirements := by
    rw [Detail.unify_requirements_eq unified]
    intro requirement member
    exact member
  let finalResources : FinalInferenceResources
      {
        environment
        signatures
        scope := .ofDeclaration declaration
        typeParameters := signature.scheme.parameters
        assumptions := signature.scheme.predicates
      }
      (Ty.productMany signature.returnTypes) finalState
      (body.statements.map NodeId.statement) result :=
    FinalInferenceResources.ofFinalize finalized
  have substitutionExtends : result.substitution.SemanticallyExtends
      body.state.inference.substitution := by
    rw [finalResources.substitution_eq]
    exact (unifyProgress.trans
      (finalResources.progress_of_ready unifiedReady)).substitution_extends
  have activeSignaturesEq : canonicalContext.signatures =
      (finalizedRequirementContext
        {
          environment
          signatures
          scope := .ofDeclaration declaration
          typeParameters := signature.scheme.parameters
          assumptions := signature.scheme.predicates
        } result).signatures := by
    calc
      canonicalContext.signatures =
          (checkedBodyContext signatures signature checked).signatures :=
        monoBindersExtend_signatures_eq canonicalExtension
      _ = _ := by
        simp [checkedBodyContext, finalizedRequirementContext,
          declarationContext, Context.withResidualTypeVariables,
          Context.withSolvedRequirements, Context.withAssumptions,
          Context.forDeclaration]
  have scopeFields := monoBindersExtend_scope_fields canonicalExtension
  have activeParametersEq : canonicalContext.typeParameters =
      signature.scheme.parameters := by
    calc
      canonicalContext.typeParameters =
          (checkedBodyContext signatures signature checked).typeParameters :=
        scopeFields.1
      _ = signature.scheme.parameters := by
        simp [checkedBodyContext, declarationContext,
          Context.withResidualTypeVariables, Context.withSolvedRequirements,
          Context.withAssumptions, Context.forDeclaration]
  have activeDeclarationEq : canonicalContext.currentDeclaration =
      some declaration.id := by
    calc
      canonicalContext.currentDeclaration =
          (checkedBodyContext signatures signature checked
            ).currentDeclaration := scopeFields.2.1
      _ = some declaration.id := by
        simp [checkedBodyContext, declarationContext,
          Context.withResidualTypeVariables, Context.withSolvedRequirements,
          Context.withAssumptions, Context.forDeclaration,
          declarationIdEq]
  have activeResidual : canonicalContext.residualTypeVariables = true := by
    calc
      canonicalContext.residualTypeVariables =
          (checkedBodyContext signatures signature checked
            ).residualTypeVariables := scopeFields.2.2
      _ = true := by
        simp [checkedBodyContext, declarationContext,
          Context.withResidualTypeVariables]
  have activeRequirementsEq : canonicalContext.solvedRequirements =
      (finalizedRequirementContext
        {
          environment
          signatures
          scope := .ofDeclaration declaration
          typeParameters := signature.scheme.parameters
          assumptions := signature.scheme.predicates
        } result).solvedRequirements := by
    calc
      canonicalContext.solvedRequirements =
          (checkedBodyContext signatures signature checked
            ).solvedRequirements :=
        monoBindersExtend_solvedRequirements_eq canonicalExtension
      _ = _ := by
        simp [checkedBodyContext, finalizedRequirementContext,
          declarationContext, checkedEq, Context.withResidualTypeVariables,
          Context.withSolvedRequirements, Context.withAssumptions,
          Context.forDeclaration]
  have assumptionsMono :
      (finalizedRequirementContext
        {
          environment
          signatures
          scope := .ofDeclaration declaration
          typeParameters := signature.scheme.parameters
          assumptions := signature.scheme.predicates
        } result).assumptions ⊆ canonicalContext.assumptions := by
    have canonicalAssumptions :=
      MonoBindersExtend.assumptions_eq canonicalExtension
    have predicatesFixedResult :
        signature.scheme.predicates.map
          (TypedTraitResolution.applySubstitution result.substitution) =
            signature.scheme.predicates := by
      simpa only [checkedEq] using predicatesFixed
    intro predicate member
    rw [canonicalAssumptions]
    have substitutedMember : predicate ∈
        signature.scheme.predicates.map
          (TypedTraitResolution.applySubstitution result.substitution) := by
      simpa [finalizedRequirementContext, Context.withSolvedRequirements,
        Context.withAssumptions] using member
    rw [predicatesFixedResult] at substitutedMember
    simpa [checkedBodyContext, declarationContext,
      Context.withResidualTypeVariables, Context.withSolvedRequirements,
      Context.withAssumptions, Context.forDeclaration] using
      substitutedMember
  have rootCoverage : ∀ statement ∈ body.statements,
      TemplateScopeCovered result.typedSource canonicalContext
        (.statement statement) := by
    intro statement member
    apply TemplateScopeCovered.root finalResources.graph_closed.rootsHaveNoParent
    rw [finalize_statementRoots finalized]
    exact List.mem_map_of_mem member
  let bodyContext : Frontend.SourceInference.Context :=
    { environment, signatures, scope := .ofDeclaration declaration,
      typeParameters := signature.scheme.parameters,
      assumptions := signature.scheme.predicates }
  have emptyActual : ActualContext bodyContext result []
      (checkedBodyContext signatures signature checked) := by
    apply ActualContext.empty
    · rfl
    · have fixed : signature.scheme.predicates.map
          (TypedTraitResolution.applySubstitution result.substitution) =
            signature.scheme.predicates := by
        simpa only [checkedEq] using predicatesFixed
      simp [bodyContext, checkedBodyContext, declarationContext,
        finalizedRequirementContext, Context.withResidualTypeVariables,
        Context.withSolvedRequirements, Context.withAssumptions,
        Context.forDeclaration, fixed]
    · simpa [checkedEq, bodyContext, ProgramTypeScope.ofDeclaration, declarationIdEq] using
        checkFunctionBody_success_typedBody_owner success
  have actual : ActualContext bodyContext result [] canonicalContext :=
    emptyActual.monoBinders canonicalExtension
  have rawMonomorphic : ExecutableBinderInterfaces.SourceMonomorphic
      (finalState.toTypedSource (body.statements.map NodeId.statement)) := by
    apply ExecutableBinderInterfaces.SourceMonomorphic.beforeSubstitution
      (substitution := result.substitution)
    rw [← finalResources.source_eq]
    simpa only [checkedEq] using sourceMonomorphic
  have operational : ActualStateInvariant initial
      (finalState.toTypedSource (body.statements.map NodeId.statement)) := by
    apply ActualStateInvariant.initial
    · intro entry member
      obtain ⟨parameter, _, rfl⟩ := List.mem_map.mp member
      rfl
    · exact rawMonomorphic
  have expectedFixed : result.substitution.apply
      (Ty.productMany signature.returnTypes) =
        Ty.productMany signature.returnTypes := by
    have resultType : result.type = Ty.productMany signature.returnTypes := by
      simpa [checkedEq] using header.result_type
    exact (Detail.finalize_type finalized).symm.trans resultType
  have returnWellFormed : TypeWellFormed canonicalContext
      (Ty.productMany signature.returnTypes) := by
    apply monoBindersExtend_typeWellFormed canonicalExtension
    exact ⟨header.parameter_binders,
      StructuralSubstitution.TypesWellScoped.productMany
        (StructuralSubstitution.TypesWellFormed.toTypesWellScoped
          header.return_types)⟩
  have returnAdmissible : TypeAdmissible canonicalContext
      (result.substitution.apply (Ty.productMany signature.returnTypes)) := by
    rw [expectedFixed]
    exact TypeAdmissible.ofWellFormed returnWellFormed
  obtain ⟨finalContext, facts, _, _, _, typed, matching⟩ :=
    recursiveSound inferred finalResources
      (by simpa only [checkedEq] using interfaces)
      signatureFormation functionsCanonical
      catalog (by simpa [ProgramTypeScope.ofDeclaration, declarationIdEq]
        using signatureParameters)
      initialInvariant actual operational returnAdmissible
      initialSchemeIsolation initialReady returnBelow
      initialBindersBelow initialBelow
      substitutionExtends
      rawSourceExtends
      (by simpa only [checkedEq] using sourceExtends)
      patternsSubset literalsSubset requirementsSubset activeSignaturesEq
      activeParametersEq
      (by simpa [ProgramTypeScope.ofDeclaration] using activeDeclarationEq)
      activeResidual
      activeRequirementsEq assumptionsMono rootCoverage
      (by intro statement _; exact ActualContext.covers_empty (.statement statement))
  have factsType : facts.type = Ty.productMany signature.returnTypes := by
    calc
      facts.type = result.substitution.apply body.type := matching.type_eq
      _ = result.substitution.apply
          (Ty.productMany signature.returnTypes) :=
        Detail.unify_then_finalize_eq unified finalized
      _ = Ty.productMany signature.returnTypes := expectedFixed
  have actualRoots : checked.typedBody.roots =
      body.statements.map NodeId.statement := by
    rw [checkedEq]
    exact finalize_statementRoots finalized
  have statementsEq : statements = body.statements := by
    have mapped : statements.map NodeId.statement =
        body.statements.map NodeId.statement := roots.symm.trans actualRoots
    exact statementRoots_injective mapped
  refine ⟨facts, factsType, ?_⟩
  intro lexicalContext extension
  have contextEq : lexicalContext = canonicalContext :=
    monoBindersExtend_final_unique extension canonicalExtension
  subst lexicalContext
  refine ⟨finalContext, ?_⟩
  subst statements
  have typedChecked : StatementsHaveType checked.typedBody
      { returnType := Ty.productMany signature.returnTypes }
      canonicalContext body.statements finalContext facts := by
    simpa only [checkedEq, expectedFixed] using typed
  exact typedChecked

/-- For an ordinary function, all global and rigid-parameter premises of the
recursive bridge come from the successful raw-workspace checker.  The body
header, closed predicates, and recursive theorem remain the separate semantic
inputs to this final assembly step. -/
theorem checkedBodyStatementsHaveType_ofCheckProgram_function
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    {program : CheckedProgram}
    {signature : ProgramFunctionSignature} {function : CheckedFunction}
    (programSuccess : Frontend.checkProgram raw fuel = .ok program)
    (member : signature ∈ program.signatures.functions)
    (header : CheckedBodyHeaderWellFormed program.signatures signature
      function)
    (predicatesFixed :
      signature.scheme.predicates.map
        (TypedTraitResolution.applySubstitution function.substitution) =
          signature.scheme.predicates)
    (bodySuccess : checkFunctionBody program.environment program.signatures
      signature fuel = .ok function)
    (interfaces : ExecutableCoercionInterfaces.BodyInterfaces program.signatures function)
    (sourceMonomorphic : ExecutableBinderInterfaces.SourceMonomorphic function.typedBody)
    (recursiveSound : ActualInferStatementsFuelSoundness fuel) :
    CheckedBodyStatementsHaveType program.signatures signature function := by
  apply checkedBodyStatementsHaveType_of_inferStatementsFuel_sound header
    predicatesFixed
  · exact Frontend.checkProgram_success_signature_formation programSuccess
  · intro candidate candidateMember
    exact (Frontend.checkProgram_success_function_signature_shape
      programSuccess candidateMember).2
  · exact SignatureCatalogWellFormed.ofCheckProgram programSuccess
  · exact (Frontend.checkProgram_success_signature_parameters_wellFormed
      programSuccess).functions signature member
  · exact bodySuccess
  · exact interfaces
  · exact sourceMonomorphic
  · exact recursiveSound

/-- The synthetic function signature used for an implementation method has
the implementation's canonical rigid parameter row.  Its other global
premises are the same raw-checker facts as for ordinary functions. -/
theorem checkedBodyStatementsHaveType_ofCheckProgram_method
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    {program : CheckedProgram}
    {implementation : ProgramImplementationSignature}
    {trait : ProgramTraitSignature}
    {method : ProgramImplMethodSignature} {function : CheckedFunction}
    (programSuccess : Frontend.checkProgram raw fuel = .ok program)
    (implementationMember :
      implementation ∈ program.signatures.implementations)
    (header : CheckedBodyHeaderWellFormed program.signatures
      (implementation.functionSignatureOfMethodWithTrait trait method)
      function)
    (predicatesFixed :
      (implementation.functionSignatureOfMethodWithTrait trait method
        ).scheme.predicates.map
        (TypedTraitResolution.applySubstitution function.substitution) =
      (implementation.functionSignatureOfMethodWithTrait trait method
        ).scheme.predicates)
    (bodySuccess : checkFunctionBody program.environment program.signatures
      (implementation.functionSignatureOfMethodWithTrait trait method) fuel =
        .ok function)
    (interfaces : ExecutableCoercionInterfaces.BodyInterfaces program.signatures function)
    (sourceMonomorphic : ExecutableBinderInterfaces.SourceMonomorphic function.typedBody)
    (recursiveSound : ActualInferStatementsFuelSoundness fuel) :
    CheckedBodyStatementsHaveType program.signatures
      (implementation.functionSignatureOfMethodWithTrait trait method)
      function := by
  apply checkedBodyStatementsHaveType_of_inferStatementsFuel_sound header
    predicatesFixed
  · exact Frontend.checkProgram_success_signature_formation programSuccess
  · intro candidate candidateMember
    exact (Frontend.checkProgram_success_function_signature_shape
      programSuccess candidateMember).2
  · exact SignatureCatalogWellFormed.ofCheckProgram programSuccess
  · simpa [ProgramImplementationSignature.functionSignatureOfMethodWithTrait,
      ProgramImplementationSignature.functionSignatureOfMethod] using
      (Frontend.checkProgram_success_signature_parameters_wellFormed
        programSuccess).implementations implementation implementationMember
  · exact bodySuccess
  · exact interfaces
  · exact sourceMonomorphic
  · exact recursiveSound

end Solcore.SourceSemantics.SourceInferenceSoundness.SelectedCheckedBodyTypingBridge
end
