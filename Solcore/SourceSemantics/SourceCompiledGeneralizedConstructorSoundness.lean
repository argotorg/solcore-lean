import Solcore.SourceSemantics.SourceCompiledGeneralizedFreshConstructor

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
  {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
  {selected : Selected compiled row fuel}

theorem constructor_call
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRetainedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {expression callee : Syntax.Expr}
    {arguments : Syntax.DelimitedList Syntax.Expr} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
    (form : expression.value = .call callee arguments)
    (discovery : Detail.constructorCalleeCandidates inferenceContext initial.allocateExpressionId.2 callee =
      .ok [(dataType, constructor)])
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext expression
      expected initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource
      target selected.body.finalized.substitution inferred := by
  generalize allocation : initial.allocateExpressionId = allocatedPair
  obtain ⟨id, allocated⟩ := allocatedPair
  have found : Detail.constructorCalleeCandidates inferenceContext allocated callee =
      .ok [(dataType, constructor)] := by simpa only [allocation] using discovery
  have members := Detail.constructorCalleeCandidates_success_members found dataType constructor (by simp)
  have success := boundary.accepted
  unfold Detail.inferExprFuel at success
  simp only [allocation, form, found, bind, Except.bind] at success
  generalize fresh : Detail.freshDataConstructorInstantiation dataType constructor allocated = pair at success
  obtain ⟨instantiation, constructorState⟩ := pair
  exact freshConstructorRetained checked recursive boundary allocation members.1 members.2 fresh success

theorem constructor_dot
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRetainedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {expression : Syntax.Expr}
    {dot : Syntax.SourceSpan} {name : Syntax.Identifier}
    {arguments : Option (Syntax.DelimitedList Syntax.Expr)} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : expression.value = .dotConstructor dot name arguments)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext expression
      expected initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource
      target selected.body.finalized.substitution inferred := by
  have formation := boundary.scope.formation checked
  have catalog := boundary.scope.catalog checked
  generalize allocation : initial.allocateExpressionId = allocatedPair
  obtain ⟨id, allocated⟩ := allocatedPair
  have invariant := boundary.invariant.allocateExpressionId allocation
  have operational := boundary.operational.allocateExpressionId
  rw [allocation] at operational
  have expectedBelow : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
    rw [allocateExpressionId_inferenceNext_eq allocation]
    exact boundary.expectedBelow
  have allocatedSame : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  have expectedSafe : ∀ binder ∈ allocated.localBinders, ∀ type ∈ expected,
      ProtectedVariables.Safe binder.scheme.quantified allocated type := by
    rw [allocatedSame]
    exact boundary.expectedSafe
  have success := boundary.accepted
  unfold Detail.inferExprFuel at success
  simp only [allocation, form, bind, Except.bind] at success
  cases found : Detail.contextualConstructorCandidate inferenceContext allocated expected name.value with
  | error error => simp [found] at success
  | ok pair =>
    obtain ⟨dataType, constructor, typeArguments⟩ := pair
    simp only [found] at success
    obtain ⟨dataMember, constructorMember, expectedType, expectedEq, nominalEq⟩ :=
      Detail.contextualConstructorCandidate_success_facts found
    have bounded := Detail.contextualConstructorCandidate_success_instantiation_variablesBelow
      invariant.ready expectedBelow formation found
    have activeCatalog : SignatureCatalogWellFormed target.signatures := by
      rw [invariant.signatures_eq_whole, ← boundary.scope.signatures]
      exact catalog
    have activeData : dataType ∈ target.signatures.dataTypes := by
      rw [invariant.signatures_eq_whole, ← boundary.scope.signatures]
      exact dataMember
    have resultAdmissible : TypeAdmissible target
        (selected.body.finalized.substitution.apply
          (Detail.instantiateDataConstructor dataType constructor typeArguments).resultType) := by
      have expectedTyped := boundary.expectedAdmissible expectedType (by simp [expectedEq])
      have resolved : selected.body.finalized.substitution.apply (allocated.resolve expectedType) =
          selected.body.finalized.substitution.apply expectedType := by
        simpa only [State.resolve, InferState.resolve] using invariant.substitutionExtension expectedType
      rw [← resolved, nominalEq] at expectedTyped
      exact expectedTyped
    have valid := SourceSemantics.DataConstructorInstantiation.Admissible.instantiateDataConstructor_applySubstitution
      activeCatalog activeData constructorMember selected.body.finalized.substitution resultAdmissible
    have privacy : ∀ binder ∈ allocated.localBinders,
        (∀ type ∈ (Detail.instantiateDataConstructor dataType constructor typeArguments).payloadTypes,
          ProtectedVariables.Safe binder.scheme.quantified allocated type) ∧
        ProtectedVariables.Safe binder.scheme.quantified allocated
          (Detail.instantiateDataConstructor dataType constructor typeArguments).resultType := by
      intro binder member
      have accepted : Detail.contextualConstructorCandidate inferenceContext allocated
          (some expectedType) name.value = .ok (dataType, constructor, typeArguments) := expectedEq ▸ found
      exact ProtectedVariables.contextual_constructor invariant.ready formation
        (expectedSafe binder member expectedType (by simp [expectedEq])) accepted
    exact constructorApplicationRetained checked recursive success boundary.interfaces boundary.extension
      boundary.scope invariant boundary.actual operational bounded.1 bounded.2 expectedBelow
      (fun binder member => (privacy binder member).1)
      (fun binder member => (privacy binder member).2) expectedSafe valid boundary.rawProper
      boundary.integerPatterns boundary.integerLiterals boundary.requirements boundary.expressionRequirements
      boundary.coercionPrimaries boundary.directChildren boundary.covered boundary.actualCovered

theorem constructor_field
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRetainedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {expression base : Syntax.Expr}
    {dot : Syntax.SourceSpan} {name : Syntax.Identifier} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : expression.value = .field base dot name)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext expression
      expected initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource
      target selected.body.finalized.substitution inferred := by
  generalize allocation : initial.allocateExpressionId = allocatedPair
  obtain ⟨id, allocated⟩ := allocatedPair
  have success := boundary.accepted
  unfold Detail.inferExprFuel at success
  simp only [allocation, form, bind, Except.bind] at success
  cases discovery : Detail.constructorCalleeCandidates inferenceContext allocated expression with
  | error error => simp [discovery] at success
  | ok candidates =>
    cases candidates with
    | nil =>
      simp only [discovery] at success
      repeat' split at success
      all_goals simp_all [throw]
    | cons first rest =>
      obtain ⟨dataType, constructor⟩ := first
      cases rest with
      | cons second tail => simp [discovery] at success
      | nil =>
        simp only [discovery] at success
        have members := Detail.constructorCalleeCandidates_success_members discovery dataType constructor (by simp)
        generalize fresh : Detail.freshDataConstructorInstantiation dataType constructor allocated = pair at success
        obtain ⟨instantiation, constructorState⟩ := pair
        exact freshConstructorRetained checked recursive boundary allocation members.1 members.2 fresh success

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
