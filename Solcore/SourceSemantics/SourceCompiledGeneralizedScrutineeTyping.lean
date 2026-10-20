import Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionList
import Solcore.SourceSemantics.SourceCompiledGeneralizedMatchContracts

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

structure ScrutineeBoundary (selected : Selected compiled row fuel)
    (childFuel : Nat) (inferenceContext : SourceInference.Context) (span : Syntax.SourceSpan)
    (sources : List Syntax.Expr) (initial : State) (inferred : InferredExpression) (result : State)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop where
  accepted : inferMatchScrutineesFuel childFuel inferenceContext span sources initial = .ok (inferred, result)
  interfaces : ExecutableCoercionInterfaces.SourceInterfaces (checkingContext selected).signatures
    selected.body.finalized.solvedRequirements selected.body.finalized.typedSource
  extension : selected.body.finalized.substitution.SemanticallyExtends result.inference.substitution
  scope : CheckingScope selected inferenceContext
  invariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target
  actual : ActualContext (checkingContext selected) selected.body.finalized frames target
  operational : GeneralizedActualStateInvariant initial (evidenceSource selected)
  rawSubtree : RawSubtreePreserved (result.toTypedSource (bodyRoots selected))
    (evidenceSource selected) (.expression inferred.id)
  integerPatterns : result.integerPatterns ⊆ selected.body.returned.integerPatterns
  integerLiterals : result.integerLiterals ⊆ selected.body.returned.integerLiterals
  requirements : result.requirements ⊆ selected.body.returned.requirements
  covered : TemplateScopeCovered selected.body.finalized.typedSource target (.expression inferred.id)
  actualCovered : ActualContext.Covers selected.body.finalized frames (.expression inferred.id)

private theorem syntheticScrutinee
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : Selected compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundness selected smaller)
    {inferenceContext : SourceInference.Context} {span : Syntax.SourceSpan} {sources : List Syntax.Expr}
    {initial elementsState : State} {elements : List InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (accepted : Detail.inferExprsFuel childFuel inferenceContext sources initial = .ok (elements, elementsState))
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces (checkingContext selected).signatures
      selected.body.finalized.solvedRequirements selected.body.finalized.typedSource)
    (extension : selected.body.finalized.substitution.SemanticallyExtends elementsState.inference.substitution)
    (scope : CheckingScope selected inferenceContext)
    (invariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target)
    (actual : ActualContext (checkingContext selected) selected.body.finalized frames target)
    (operational : GeneralizedActualStateInvariant initial (evidenceSource selected))
    (rawSubtree : RawSubtreePreserved
      ((elementsState.allocateExpressionId.2.recordNode (.expression {
        id := elementsState.allocateExpressionId.1, span,
        type := Ty.productMany (elements.map (·.type)), form := .tuple (elements.map (·.id))
      })).toTypedSource (bodyRoots selected)) (evidenceSource selected)
      (.expression elementsState.allocateExpressionId.1))
    (integerPatterns : elementsState.integerPatterns ⊆ selected.body.returned.integerPatterns)
    (integerLiterals : elementsState.integerLiterals ⊆ selected.body.returned.integerLiterals)
    (requirements : elementsState.requirements ⊆ selected.body.returned.requirements)
    (covered : TemplateScopeCovered selected.body.finalized.typedSource target
      (.expression elementsState.allocateExpressionId.1))
    (actualCovered : ActualContext.Covers selected.body.finalized frames (.expression elementsState.allocateExpressionId.1)) :
    ExpressionHasType selected.body.finalized.typedSource target elementsState.allocateExpressionId.1
      (selected.body.finalized.substitution.apply (Ty.productMany (elements.map (·.type)))) := by
  let node : ExpressionNode := {
    id := elementsState.allocateExpressionId.1, span,
    type := Ty.productMany (elements.map (·.type)), form := .tuple (elements.map (·.id)) }
  let final := elementsState.allocateExpressionId.2.recordNode (.expression node)
  have contains : ContainsExpression (final.toTypedSource (bodyRoots selected)) node.id node :=
    recordNode_containsExpression _ node
  have sourceExtension : TypingSourceExtends (elementsState.toTypedSource (bodyRoots selected))
      (final.toTypedSource (bodyRoots selected)) := by
    exact ⟨rfl, List.prefix_append _ _⟩
  have edge : ∀ element ∈ elements, DirectChild (final.toTypedSource (bodyRoots selected))
      (.expression node.id) (.expression element.id) := by
    intro element member
    refine ⟨.expression node, ⟨contains.1, rfl⟩, ?_⟩
    simpa [node, nodeChildIds, Node.references, ExpressionForm.references] using
      (List.mem_map.mpr ⟨element.id, List.mem_map.mpr ⟨element, member, rfl⟩, rfl⟩ :
        NodeId.expression element.id ∈ (elements.map (·.id)).map NodeId.expression)
  have typed := expressionsRooted checked childFuel
    (fun smaller less => recursive smaller (Nat.lt_trans less (Nat.lt_succ_self childFuel)))
    accepted interfaces extension scope invariant actual operational
    (fun element member => (rawSubtree.child (edge element member)).monoBefore sourceExtension)
    integerPatterns integerLiterals requirements
    (fun element member => covered.expressionChild selected.body.resources.graph_closed
      ((rawSubtree.finalized selected.body.resources).directChild (edge element member)))
    (fun element member => actualCovered.directChild
      ((rawSubtree.finalized selected.body.resources).directChild (edge element member)))
  have binders := invariant.typeParameterBinders (by
    simpa [scope.owner, scope.parameters] using scope.canonical checked)
  have finalContains : ContainsExpression selected.body.finalized.typedSource node.id
      (node.applySubstitution selected.body.finalized.substitution) :=
    ⟨(rawSubtree.finalized selected.body.resources).nodes (.expression node) contains.1 (.inl rfl), rfl⟩
  have formTyping : ExpressionFormHasRawType selected.body.finalized.typedSource target
      (node.applySubstitution selected.body.finalized.substitution).form
      (selected.body.finalized.substitution.apply node.type) (.ordinary []) := by
    simpa [node, ExpressionNode.applySubstitution, ExpressionForm.applySubstitution,
      FlexibleSubstitution.apply_productMany, List.map_map, Function.comp_def] using ExpressionFormHasRawType.tuple typed
  have admissible : TypeAdmissible target (selected.body.finalized.substitution.apply node.type) := by
    simpa [node, FlexibleSubstitution.apply_productMany, List.map_map, Function.comp_def] using
      typed.product_type_admissible binders
  exact ExpressionHasType.ofOrdinary (owned := [])
    (rawType := selected.body.finalized.substitution.apply node.type) finalContains formTyping admissible admissible
    (by intro requirement member; simp at member)
    (.nil _) (by simp [node, ExpressionNode.applySubstitution, ExpressionForm.applySubstitution, coercionRequirementIds])

theorem scrutineeRooted
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : Selected compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundness selected smaller)
    {inferenceContext : SourceInference.Context} {span : Syntax.SourceSpan} {sources : List Syntax.Expr}
    {initial result : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : ScrutineeBoundary selected childFuel inferenceContext span sources initial inferred result frames target) :
    ExpressionHasType selected.body.finalized.typedSource target inferred.id
      (selected.body.finalized.substitution.apply inferred.type) := by
  have accepted := boundary.accepted
  have tupleCase : ∀ (sources : List Syntax.Expr),
      (∀ expression, sources ≠ [expression]) →
      inferMatchScrutineesFuel childFuel inferenceContext span sources initial = .ok (inferred, result) →
      ExpressionHasType selected.body.finalized.typedSource target inferred.id
        (selected.body.finalized.substitution.apply inferred.type) := by
    intro manySources nonsingle accepted
    unfold inferMatchScrutineesFuel at accepted
    split at accepted
    next source => exact False.elim (nonsingle source rfl)
    next _ _ =>
      cases elementsAccepted : Detail.inferExprsFuel childFuel inferenceContext manySources initial with
      | error error => simp [elementsAccepted, bind, Except.bind] at accepted
      | ok pair =>
        rcases pair with ⟨elements, elementsState⟩
        simp only [elementsAccepted, bind, Except.bind] at accepted
        simp only [pure, Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at accepted
        rcases accepted with ⟨rfl, rfl⟩
        exact syntheticScrutinee checked recursive elementsAccepted boundary.interfaces
          boundary.extension boundary.scope boundary.invariant boundary.actual boundary.operational
          boundary.rawSubtree boundary.integerPatterns boundary.integerLiterals boundary.requirements
          boundary.covered boundary.actualCovered
  cases sources with
  | nil => exact tupleCase [] (by simp) accepted
  | cons source rest =>
    cases rest with
    | nil =>
      exact expressionRooted_of_retained checked (recursive childFuel (Nat.lt_succ_self _)) ({
        accepted := by simpa [inferMatchScrutineesFuel] using accepted
        interfaces := boundary.interfaces, extension := boundary.extension, scope := boundary.scope
        invariant := boundary.invariant, actual := boundary.actual, operational := boundary.operational
        expectedBelow := by simp
        expectedAdmissible := by simp
        expectedSafe := by simp
        integerPatterns := boundary.integerPatterns, integerLiterals := boundary.integerLiterals
        requirements := boundary.requirements, covered := boundary.covered, actualCovered := boundary.actualCovered
        rawSubtree := boundary.rawSubtree } : RootedExpressionBoundary selected childFuel inferenceContext
          source none initial inferred result frames target)
    | cons second tail => exact tupleCase (source :: second :: tail) (by simp) accepted

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
