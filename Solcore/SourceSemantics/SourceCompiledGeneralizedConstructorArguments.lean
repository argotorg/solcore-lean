import Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionList
import Solcore.SourceSemantics.SourceInferenceSelectedConstructorInstantiation

/-! Constructor arguments use the expected payload types from the actual
constructor instantiation. Each child is checked in the selected final source
and preserves the incoming generalized scope. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

theorem constructorArgumentsRooted
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : Selected compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRetainedSoundness selected childFuel) :
    ∀ {inferenceContext : SourceInference.Context} {sources : List Syntax.Expr}
      {expectedTypes : List Ty} {initial resultState : State}
      {inferred : List InferredExpression}
      {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    Detail.inferConstructorArgumentsFuel childFuel inferenceContext sources expectedTypes initial =
      .ok (inferred, resultState) →
    ExecutableCoercionInterfaces.SourceInterfaces (checkingContext selected).signatures
      selected.body.finalized.solvedRequirements selected.body.finalized.typedSource →
    selected.body.finalized.substitution.SemanticallyExtends resultState.inference.substitution →
    CheckingScope selected inferenceContext →
    RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target →
    ActualContext (checkingContext selected) selected.body.finalized frames target →
    GeneralizedActualStateInvariant initial (evidenceSource selected) →
    (∀ type ∈ expectedTypes, type.VariablesBelow initial.inference.next) →
    (∀ type ∈ expectedTypes, TypeAdmissible target (selected.body.finalized.substitution.apply type)) →
    (∀ binder ∈ initial.localBinders, ∀ type ∈ expectedTypes,
      ProtectedVariables.Safe binder.scheme.quantified initial type) →
    (∀ argument ∈ inferred, RawSubtreePreserved (resultState.toTypedSource (bodyRoots selected))
      (evidenceSource selected) (.expression argument.id)) →
    resultState.integerPatterns ⊆ selected.body.returned.integerPatterns →
    resultState.integerLiterals ⊆ selected.body.returned.integerLiterals →
    resultState.requirements ⊆ selected.body.returned.requirements →
    (∀ argument ∈ inferred, TemplateScopeCovered selected.body.finalized.typedSource target
      (.expression argument.id)) →
    (∀ argument ∈ inferred, ActualContext.Covers selected.body.finalized frames (.expression argument.id)) →
    ExpressionsHaveTypes selected.body.finalized.typedSource target (inferred.map (·.id))
      (expectedTypes.map selected.body.finalized.substitution.apply) := by
  intro inferenceContext sources
  induction sources with
  | nil =>
    intro expectedTypes initial resultState inferred frames target accepted
    cases expectedTypes with
    | nil =>
      simp only [Detail.inferConstructorArgumentsFuel, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      intros
      exact .nil target
    | cons _ _ => simp [Detail.inferConstructorArgumentsFuel] at accepted
  | cons source sources induction =>
    intro expectedTypes initial resultState inferred frames target accepted interfaces extension scope
      invariant actual operational expectedBelow expectedAdmissible expectedSafe rawPreserved
      integerPatternsSubset integerLiteralsSubset requirementsSubset covered actualCovered
    cases expectedTypes with
    | nil => simp [Detail.inferConstructorArgumentsFuel] at accepted
    | cons expected expectedTypes =>
      have formation := scope.formation checked
      have functions := scope.functionsCanonical checked
      have catalog := scope.catalog checked
      unfold Detail.inferConstructorArgumentsFuel at accepted
      cases headSuccess : Detail.inferExprFuel childFuel inferenceContext source
          (some (initial.resolve expected)) initial with
      | error error => simp [headSuccess, bind, Except.bind] at accepted
      | ok pair =>
        obtain ⟨head, headState⟩ := pair
        simp only [headSuccess, bind, Except.bind] at accepted
        cases tailSuccess : Detail.inferConstructorArgumentsFuel childFuel inferenceContext
            sources expectedTypes headState with
        | error error => simp [tailSuccess] at accepted
        | ok pair =>
          obtain ⟨tail, tailState⟩ := pair
          simp only [tailSuccess, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at accepted
          obtain ⟨rfl, rfl⟩ := accepted
          have headExpectedBelow : ∀ type ∈ some (initial.resolve expected),
              type.VariablesBelow initial.inference.next := by
            intro type member
            have same : type = initial.resolve expected := by
              simpa only [Option.mem_def, Option.some.injEq] using member.symm
            subst type
            exact invariant.ready.solved.variablesBelow_apply (expectedBelow expected (by simp))
          have headExpectedSafe : ∀ binder ∈ initial.localBinders,
              ∀ type ∈ some (initial.resolve expected),
              ProtectedVariables.Safe binder.scheme.quantified initial type := by
            intro binder member type typeMember
            have same : type = initial.resolve expected := by
              simpa only [Option.mem_def, Option.some.injEq] using typeMember.symm
            subst type
            exact ProtectedVariables.safe_resolved invariant.ready
              (expectedSafe binder member expected (by simp))
          have headProperties := Detail.inferExprFuel_inferenceProperties invariant.ready formation
            functions headExpectedBelow headSuccess
          have tailExpectedBelow : ∀ type ∈ expectedTypes, type.VariablesBelow headState.inference.next :=
            fun type member => (expectedBelow type (by simp [member])).weaken headProperties.1.next_le
          have tailProperties := Detail.inferConstructorArgumentsFuel_inferenceProperties
            headProperties.2.1 formation functions tailExpectedBelow tailSuccess
          have headExtension := extension.trans tailProperties.1.substitution_extends
          have initialExtension := headExtension.trans headProperties.1.substitution_extends
          have initialResolved : selected.body.finalized.substitution.apply (initial.resolve expected) =
              selected.body.finalized.substitution.apply expected := by
            simpa only [State.resolve, InferState.resolve] using initialExtension expected
          have headExpectedAdmissible : ∀ type ∈ some (initial.resolve expected),
              TypeAdmissible target (selected.body.finalized.substitution.apply type) := by
            intro type member
            have same : type = initial.resolve expected := by
              simpa only [Option.mem_def, Option.some.injEq] using member.symm
            rw [same, initialResolved]
            exact expectedAdmissible expected (by simp)
          have headInvariant := invariant.ofExpression formation functions headExpectedBelow
            headExtension headSuccess
          have headOperational := operational.ofExpression invariant.ready catalog formation functions
            headExpectedBelow headExpectedSafe headSuccess
          have headToFinal := inferConstructorArgumentsFuel_success_typingSourceExtends
            tailSuccess headInvariant.nodesBelow (bodyRoots selected)
          have headTyped := expressionRooted_of_retained checked recursive ({
            accepted := headSuccess
            interfaces := interfaces
            extension := headExtension
            scope := scope
            invariant := invariant
            actual := actual
            operational := operational
            expectedBelow := headExpectedBelow
            expectedAdmissible := headExpectedAdmissible
            expectedSafe := headExpectedSafe
            integerPatterns := (Detail.inferConstructorArgumentsFuel_integerPatterns_subset tailSuccess).trans
              integerPatternsSubset
            integerLiterals := (Detail.inferConstructorArgumentsFuel_integerLiterals_subset tailSuccess).trans
              integerLiteralsSubset
            requirements := (Detail.inferConstructorArgumentsFuel_requirements_subset tailSuccess).trans
              requirementsSubset
            covered := covered head (by simp)
            actualCovered := actualCovered head (by simp)
            rawSubtree := (rawPreserved head (by simp)).monoBefore headToFinal } :
            RootedExpressionBoundary selected childFuel inferenceContext source
              (some (initial.resolve expected)) initial head headState frames target)
          have headTypeEq : selected.body.finalized.substitution.apply head.type =
              selected.body.finalized.substitution.apply expected :=
            (Detail.inferExprFuel_expected_type_apply_eq headSuccess headExtension).trans initialResolved
          have tailSafe : ∀ binder ∈ headState.localBinders, ∀ type ∈ expectedTypes,
              ProtectedVariables.Safe binder.scheme.quantified headState type := by
            have binders : headState.localBinders = initial.localBinders :=
              congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq headSuccess)
            intro binder member type typeMember
            have old := binders ▸ member
            have privacy := ProtectedVariables.inferExprFuel_private binder.scheme.quantified childFuel
              inferenceContext source (some (initial.resolve expected)) initial invariant.ready
              operational.requirements (operational.quantifiersBelow binder old)
              (operational.privacy binder old) catalog formation functions headExpectedBelow
              (headExpectedSafe binder old) _ headSuccess
            exact privacy.1 type (expectedSafe binder old type (by simp [typeMember]))
          have tailTyped := induction tailSuccess interfaces extension scope headInvariant actual
            headOperational tailExpectedBelow
            (fun type member => expectedAdmissible type (by simp [member])) tailSafe
            (fun argument member => rawPreserved argument (by simp [member]))
            integerPatternsSubset integerLiteralsSubset requirementsSubset
            (fun argument member => covered argument (by simp [member]))
            (fun argument member => actualCovered argument (by simp [member]))
          exact .cons (by simpa only [headTypeEq] using headTyped) tailTyped

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
