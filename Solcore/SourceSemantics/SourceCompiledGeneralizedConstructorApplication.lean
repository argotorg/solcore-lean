import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceInferenceGeneralizedConstructorState

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

theorem constructorApplicationRetained
    {rawSource : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram rawSource fuel = .ok compiled.program)
    (recursive : ExpressionRetainedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {arguments : List Syntax.Expr} {instantiation : DataConstructorInstantiation} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (success : Detail.inferConstructorApplicationFuel childFuel inferenceContext source id instantiation
      arguments expected initial = .ok (inferred, resultState))
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces (checkingContext selected).signatures
      selected.body.finalized.solvedRequirements selected.body.finalized.typedSource)
    (extension : selected.body.finalized.substitution.SemanticallyExtends resultState.inference.substitution)
    (scope : CheckingScope selected inferenceContext)
    (invariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target)
    (actual : ActualContext (checkingContext selected) selected.body.finalized frames target)
    (operational : GeneralizedActualStateInvariant initial (evidenceSource selected))
    (payloadBelow : ∀ type ∈ instantiation.payloadTypes, type.VariablesBelow initial.inference.next)
    (resultBelow : instantiation.resultType.VariablesBelow initial.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (payloadSafe : ∀ binder ∈ initial.localBinders, ∀ type ∈ instantiation.payloadTypes,
      ProtectedVariables.Safe binder.scheme.quantified initial type)
    (resultSafe : ∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial instantiation.resultType)
    (expectedSafe : ∀ binder ∈ initial.localBinders, ∀ type ∈ expected,
      ProtectedVariables.Safe binder.scheme.quantified initial type)
    (instantiationValid : SourceSemantics.DataConstructorInstantiation.Admissible target
      (instantiation.applySubstitution selected.body.finalized.substitution))
    (raw : RawProperDescendantsPreserved (resultState.toTypedSource (bodyRoots selected))
      (evidenceSource selected) (.expression inferred.id))
    (patterns : resultState.integerPatterns ⊆ selected.body.returned.integerPatterns)
    (literals : resultState.integerLiterals ⊆ selected.body.returned.integerLiterals)
    (requirements : resultState.requirements ⊆ selected.body.returned.requirements)
    (retained : ExpressionRequirementsRetainedAt (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource inferred.id)
    (coercionsRetained : ExpressionCoercionPrimariesRetainedAt (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource inferred.id)
    (childrenRetained : ExpressionDirectChildrenRetainedAt (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource inferred.id)
    (covered : TemplateScopeCovered selected.body.finalized.typedSource target (.expression inferred.id))
    (actualCovered : ActualContext.Covers selected.body.finalized frames (.expression inferred.id)) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource
      target selected.body.finalized.substitution inferred := by
  have formation := scope.formation checked
  have functions := scope.functionsCanonical checked
  have catalog := scope.catalog checked
  have canonical := scope.canonical checked
  have activeCatalog : SignatureCatalogWellFormed target.signatures := by
    rw [invariant.signatures_eq_whole, ← scope.signatures]; exact catalog
  have binders := invariant.typeParameterBinders (by simpa only [scope.owner, scope.parameters] using canonical)
  have finish {argumentInitial argumentsState : State} {inferredArguments : List InferredExpression}
      (argumentInvariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized argumentInitial target)
      (argumentOperational : GeneralizedActualStateInvariant argumentInitial (evidenceSource selected))
      (argumentSafe : ∀ binder ∈ argumentInitial.localBinders, ∀ type ∈ instantiation.payloadTypes,
        ProtectedVariables.Safe binder.scheme.quantified argumentInitial type)
      (payloadAt : ∀ type ∈ instantiation.payloadTypes, type.VariablesBelow argumentInitial.inference.next)
      (resultAt : instantiation.resultType.VariablesBelow argumentInitial.inference.next)
      (expectedAt : ∀ type ∈ expected, type.VariablesBelow argumentInitial.inference.next)
      (argumentsSuccess : Detail.inferConstructorArgumentsFuel childFuel inferenceContext arguments instantiation.payloadTypes
        argumentInitial = .ok (inferredArguments, argumentsState))
      (recorded : Detail.recordExpressionWithExpected inferenceContext source id
        (argumentsState.resolve instantiation.resultType) (.constructor instantiation (inferredArguments.map (·.id))) []
        expected argumentsState = .ok (inferred, resultState)) :
      ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
    have properties := Detail.inferConstructorArgumentsFuel_inferenceProperties argumentInvariant.ready formation functions
      payloadAt argumentsSuccess
    have recording := Detail.recordExpressionWithExpected_inferenceProperties properties.2.1
      (properties.2.1.solved.variablesBelow_apply (resultAt.weaken properties.1.next_le))
      (fun type member => (expectedAt type member).weaken properties.1.next_le) recorded
    have argumentExtension := extension.trans recording.1.substitution_extends
    have argumentToParent : TypingSourceExtends (argumentsState.toTypedSource (bodyRoots selected)) (resultState.toTypedSource (bodyRoots selected)) := by
      constructor
      · obtain ⟨fitted, fittedSuccess, _, stateEq⟩ := Detail.recordExpressionWithExpected_success_record recorded
        change resultState.owner = argumentsState.owner
        dsimp only at stateEq
        rw [stateEq]
        exact congrArg State.Header.owner (Detail.SelectedMetadata.withExpected_state_header fittedSuccess)
      · exact recordExpressionWithExpected_success_nodesPrefix recorded
    obtain ⟨coercions, contains⟩ := recordExpressionWithExpected_success_containsExpression recorded (bodyRoots selected)
    have edge : ∀ argument ∈ inferredArguments, DirectChild (resultState.toTypedSource (bodyRoots selected))
        (.expression inferred.id) (.expression argument.id) := by
      intro argument member
      refine ⟨.expression _, ⟨contains.1, rfl⟩, ?_⟩
      simp only [nodeChildIds, Node.references, ExpressionForm.references]
      exact List.mem_map.mpr ⟨argument.id, List.mem_map.mpr ⟨argument, member, rfl⟩, rfl⟩
    have payloadAdmissible : ∀ type ∈ instantiation.payloadTypes,
        TypeAdmissible target (selected.body.finalized.substitution.apply type) := by
      intro type member
      apply SourceSemantics.DataConstructorInstantiation.Admissible.payload_type_admissible
        activeCatalog binders instantiationValid
      exact List.mem_map.mpr ⟨type, member, rfl⟩
    have typed := constructorArgumentsRooted checked recursive argumentsSuccess interfaces argumentExtension
      scope argumentInvariant actual argumentOperational payloadAt payloadAdmissible argumentSafe
      (fun argument member => (raw.childSubtree (edge argument member)).monoBefore argumentToParent)
      (by rw [← recordExpressionWithExpected_integerPatterns_eq recorded]; exact patterns)
      (by rw [← Detail.recordExpressionWithExpected_integerLiterals_eq recorded]; exact literals)
      ((Detail.recordExpressionWithExpected_requirements_subset recorded).trans requirements)
      (fun argument member => covered.expressionChild selected.body.resources.graph_closed (childrenRetained (edge argument member)))
      (fun argument member => actualCovered.directChild (childrenRetained (edge argument member)))
    have rawEq : selected.body.finalized.substitution.apply (argumentsState.resolve instantiation.resultType) =
        selected.body.finalized.substitution.apply instantiation.resultType := by
      simpa only [State.resolve, InferState.resolve] using argumentExtension instantiation.resultType
    have rawAdmissible : TypeAdmissible target
        (selected.body.finalized.substitution.apply (argumentsState.resolve instantiation.resultType)) := by
      rw [rawEq]
      exact SourceSemantics.DataConstructorInstantiation.Admissible.result_type_admissible
        binders instantiationValid
    have formType : ExpressionFormHasRawType selected.body.finalized.typedSource target
        ((.constructor instantiation (inferredArguments.map (·.id)) : ExpressionForm).applySubstitution selected.body.finalized.substitution)
        (selected.body.finalized.substitution.apply (argumentsState.resolve instantiation.resultType)) (.ordinary []) := by
      rw [rawEq]
      exact .constructor instantiationValid typed
    exact recordExpressionWithExpected_success_expressionTypingBase_actual selected.body.resources interfaces recorded extension
      requirements retained coercionsRetained catalog scope.signatures invariant formType rawAdmissible covered
  unfold Detail.inferConstructorApplicationFuel at success
  by_cases arity : arguments.length = instantiation.payloadTypes.length
  · simp only [arity] at success
    cases expected with
    | none =>
      simp only [pure, Pure.pure, Except.pure, bind, Except.bind] at success
      cases args : Detail.inferConstructorArgumentsFuel childFuel inferenceContext arguments instantiation.payloadTypes initial with
      | error error => simp [args] at success
      | ok pair =>
        obtain ⟨inferredArguments, argumentsState⟩ := pair
        simp only [args] at success
        exact finish invariant operational payloadSafe payloadBelow resultBelow expectedBelow args success
    | some expectedType =>
      cases unified : Detail.unify initial instantiation.resultType expectedType with
      | error error => simp [unified, bind, Except.bind] at success
      | ok argumentInitial =>
        simp only [unified, bind, Except.bind] at success
        have expectedTypeBelow := expectedBelow expectedType (by simp)
        have progress := Detail.unify_inferenceProgress invariant.ready.solved resultBelow expectedTypeBelow unified
        cases args : Detail.inferConstructorArgumentsFuel childFuel inferenceContext arguments instantiation.payloadTypes argumentInitial with
        | error error => simp [args] at success
        | ok pair =>
          obtain ⟨inferredArguments, argumentsState⟩ := pair
          simp only [args] at success
          have argumentReady := Detail.unify_preserves_inferenceReady invariant.ready resultBelow expectedTypeBelow unified
          have argsProperties := Detail.inferConstructorArgumentsFuel_inferenceProperties argumentReady formation functions
            (fun type member => (payloadBelow type member).weaken progress.next_le) args
          have recordProperties := Detail.recordExpressionWithExpected_inferenceProperties argsProperties.2.1
            (argsProperties.2.1.solved.variablesBelow_apply
              (resultBelow.weaken (Nat.le_trans progress.next_le argsProperties.1.next_le)))
            (fun type member => (expectedBelow type member).weaken (Nat.le_trans progress.next_le argsProperties.1.next_le)) success
          have argumentExtension := extension.trans (recordProperties.1.substitution_extends.trans argsProperties.1.substitution_extends)
          exact finish (invariant.unify resultBelow expectedTypeBelow argumentExtension unified)
            (operational.unify invariant.ready resultBelow expectedTypeBelow resultSafe
              (fun binder member => expectedSafe binder member expectedType (by simp)) unified)
            (by
              intro binder member type typeMember
              have same : argumentInitial.localBinders = initial.localBinders :=
                congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope unified)
              have old := same ▸ member
              exact ProtectedVariables.unify (resultSafe binder old)
                (expectedSafe binder old expectedType (by simp)) unified type
                (payloadSafe binder old type typeMember))
            (fun type member => (payloadBelow type member).weaken progress.next_le)
            (resultBelow.weaken progress.next_le)
            (fun type member => (expectedBelow type member).weaken progress.next_le) args success
  · simp [arity, bind, Except.bind] at success


end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
