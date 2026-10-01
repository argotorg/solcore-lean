import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceCompilerCertificates

/-! Actual bare-root, absent-RHS lowering has no source expression children.
The numeric profile below concerns retained IR; source compound admission is
still Word-only. Raw source type views come from describe, not Core type equality. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotCertificates
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces DataPatternValues
open CompatibleMixedRoute CompatiblePlaceCompilerCertificates DataPlaceCertificates

structure Layout (prepared : Prepared) : Prop where
  steps : prepared.steps = []
  ordinary : prepared.route.rootMapping = none
  sameType : prepared.route.rootType = prepared.route.leafType

private theorem nil_fields {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {position : Nat} {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root [] position steps keys leaf) :
    steps = [] ∧ keys = [] ∧ leaf = root := by
  cases path
  exact ⟨rfl, rfl, rfl⟩

theorem of_lower {compilation : SourceCoreCompatibleDataPlaces.Context}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
    {fuel : Nat} {expression : ExpressionLowerer} {scope : Scope} {reasonAt : ExpressionId → Word}
    {operator : Syntax.ValueAssignOp} {next lowered : Expr} {outputType : Ty}
    {invalid invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (bare : assignment.target.projections = [])
    (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    (accepted : lower compilation compilation.checked.signatures expression fuel source scope site assignment operator none
      outputType next reasonAt invalid invalidOperand missing = .ok lowered) :
    ∃ binder prepared index,
      rootBinder source assignment.target.root = .ok binder ∧
      prepared.route.rootSourceType = binder.scheme.body ∧
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType assignment.target.type ∧
      SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, prepared.route.rootType) ∧
      Layout prepared ∧
      lowered = execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit) next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) true invalidOperand := by
  cases generated_of_lower accepted with
  | intro route prepared index codes value described lookup preparedBy generated _ rhsGenerated =>
    cases rhsGenerated with
    | absent =>
      obtain ⟨binder, leaf, description⟩ := CompatiblePlaceDescription.of_describe described
      obtain ⟨routeEq, _, path⟩ := description.prepared preparedBy
      rw [bare] at path
      obtain ⟨steps, keys, rfl⟩ := nil_fields path
      rw [keys] at generated
      cases generated
      have rootEq : prepared.route.rootSourceType = binder.scheme.body := routeEq ▸ description.rootSource
      have view := description.selectedType
      have notMapping : ∀ k v, binder.scheme.body ≠ .mapping k v := by
        intro k v same
        rcases profile with word | integer
        · rw [same, word] at view; cases view
        · rw [same, integer] at view; cases view
      have types : route.rootType = route.leafType :=
        Except.ok.inj (description.rootProjected.symm.trans (by
          rw [← compilation.checked.catalog.project_runtimeType binder.scheme.body, view,
            compilation.checked.catalog.project_runtimeType]
          exact description.leafProjected))
      refine ⟨binder, prepared, index, description.binding, rootEq, rootEq ▸ view,
        by simpa only [routeEq] using lookup, ?_, by simp [routeEq]⟩
      exact ⟨steps, routeEq ▸ description.ordinary notMapping, routeEq ▸ types⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotCertificates
