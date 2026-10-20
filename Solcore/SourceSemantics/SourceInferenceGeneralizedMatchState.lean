import Solcore.SourceSemantics.SourceInferenceGeneralizedPatternState
import Solcore.SourceSemantics.SourceInferenceGeneralizedStatementRecording

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
