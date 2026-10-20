import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionRooted
import Solcore.SourceSemantics.SourceInferenceSelectedAttachedChild
import Solcore.SourceSemantics.SourceInferenceSelectedExpressionState
import Solcore.SourceSemantics.SourceInferenceExpressionDispatchSoundness

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

/-- Arguments whose roots gain coercion metadata retain their original raw typing while actual inference threads generalized state through the argument list. -/
theorem expressionsRetainedBases
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    ∀ childFuel : Nat,
    (∀ smaller, smaller < childFuel → ExpressionRetainedSoundness selected smaller) →
    ∀ {inferenceContext : SourceInference.Context} {expressions : List Syntax.Expr}
      {initial resultState : State} {inferred : List InferredExpression}
      {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    Detail.inferExprsFuel childFuel inferenceContext expressions initial = .ok (inferred, resultState) →
    ExecutableCoercionInterfaces.SourceInterfaces (checkingContext selected).signatures
      selected.body.finalized.solvedRequirements selected.body.finalized.typedSource →
    selected.body.finalized.substitution.SemanticallyExtends resultState.inference.substitution →
    CheckingScope selected inferenceContext →
    RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target →
    ActualContext (checkingContext selected) selected.body.finalized frames target →
    GeneralizedActualStateInvariant initial (evidenceSource selected) →
    (∀ argument ∈ inferred, AttachedChildPreserved selected.body.finalized.substitution
      (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource
      selected.body.finalized.typedSource (evidenceSource selected) argument.id) →
    resultState.integerPatterns ⊆ selected.body.returned.integerPatterns →
    resultState.integerLiterals ⊆ selected.body.returned.integerLiterals →
    resultState.requirements ⊆ selected.body.returned.requirements →
    (∀ argument ∈ inferred, TemplateScopeCovered selected.body.finalized.typedSource target
      (.expression argument.id)) →
    (∀ argument ∈ inferred, ActualContext.Covers selected.body.finalized frames (.expression argument.id)) →
    ArgumentTypingBasesValid (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  intro childFuel
  induction childFuel with
  | zero =>
    intro recursive inferenceContext expressions initial resultState inferred frames target success
    simp [Detail.inferExprsFuel] at success
  | succ childFuel induction =>
    intro recursive inferenceContext expressions initial resultState inferred frames target success
      interfaces extension scope invariant actual operational rawPreserved
      integerPatternsSubset integerLiteralsSubset requirementsSubset covered actualCovered
    have signatureFormation := scope.formation checked
    have functionsCanonical := scope.functionsCanonical checked
    have catalog := scope.catalog checked
    cases expressions with
    | nil =>
      simp only [Detail.inferExprsFuel, Except.ok.injEq, Prod.mk.injEq] at success
      cases success.1
      exact .nil
    | cons expression rest =>
      unfold Detail.inferExprsFuel at success
      cases headSuccess : Detail.inferExprFuel childFuel inferenceContext expression none initial with
      | error error => simp [headSuccess, bind, Except.bind] at success
      | ok pair =>
        rcases pair with ⟨head, headState⟩
        simp only [headSuccess, bind, Except.bind] at success
        cases tailSuccess : Detail.inferExprsFuel childFuel inferenceContext rest headState with
        | error error => simp [tailSuccess] at success
        | ok pair =>
          rcases pair with ⟨tail, tailState⟩
          simp only [tailSuccess, pure, Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          have headProperties := Detail.inferExprFuel_inferenceProperties invariant.ready
            signatureFormation functionsCanonical (by simp) headSuccess
          have tailProperties := Detail.inferExprsFuel_inferenceProperties headProperties.2.1
            signatureFormation functionsCanonical tailSuccess
          have headExtension := extension.trans tailProperties.1.substitution_extends
          have headInvariant := invariant.ofExpression signatureFormation functionsCanonical
            (by simp) headExtension headSuccess
          have headOperational := operational.ofExpression invariant.ready catalog signatureFormation
            functionsCanonical (by simp) (by simp) headSuccess
          have headToFinal := inferExprsFuel_success_typingSourceExtends_under_bound
            tailSuccess headInvariant.nodesBelow (bodyRoots selected)
          have headPreserved := (rawPreserved head (by simp)).monoBefore headToFinal
          have headTyped := (recursive childFuel (Nat.lt_succ_self childFuel)) ({
            accepted := headSuccess
            interfaces := interfaces
            extension := headExtension
            scope := scope
            invariant := invariant
            actual := actual
            operational := operational
            expectedBelow := by simp
            expectedAdmissible := by simp
            expectedSafe := by simp
            integerPatterns := List.Subset.trans
              (Detail.inferExprsFuel_integerPatterns_subset tailSuccess) integerPatternsSubset
            integerLiterals := List.Subset.trans
              (Detail.inferExprsFuel_integerLiterals_subset tailSuccess) integerLiteralsSubset
            requirements := List.Subset.trans
              (Detail.inferExprsFuel_requirements_subset tailSuccess) requirementsSubset
            covered := covered head (by simp)
            actualCovered := actualCovered head (by simp)
            proper := headPreserved.finalized
            rawProper := headPreserved.raw
            expressionRequirements := headPreserved.requirements
            coercionPrimaries := headPreserved.coercions
            operatorSite := headPreserved.operators
            directChildren := headPreserved.children } :
            RetainedExpressionBoundary selected childFuel inferenceContext expression none
              initial head headState frames target)
          have tailTyped := induction
            (fun smaller less => recursive smaller (Nat.lt_trans less (Nat.lt_succ_self childFuel)))
            tailSuccess interfaces extension scope headInvariant actual headOperational
            (fun argument member => rawPreserved argument (List.mem_cons_of_mem _ member))
            integerPatternsSubset integerLiteralsSubset requirementsSubset
            (fun argument member => covered argument (List.mem_cons_of_mem _ member))
            (fun argument member => actualCovered argument (List.mem_cons_of_mem _ member))
          exact .cons (headTyped.weakenNodeSource headToFinal.nodes_prefix) tailTyped

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
