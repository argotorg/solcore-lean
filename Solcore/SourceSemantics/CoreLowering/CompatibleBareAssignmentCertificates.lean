import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceCompilerCertificates

/-! Bare assignment receipts are extracted from the actual place compiler.
The raw declared type and virtual mapping quote remain authenticated by describe;
no native type equality is used to recover source metadata. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces DataPatternValues
open CompatibleMixedRoute CompatiblePlaceCompilerCertificates DataPlaceCertificates

structure Layout (compilation : SourceCoreCompatibleDataPlaces.Context) (prepared : Prepared) : Prop where
  steps : prepared.steps = []
  keys : prepared.keys = []
  sameType : prepared.route.rootType = prepared.route.leafType
  projected : compilation.checked.catalog.project prepared.route.rootSourceType = .ok prepared.route.rootType
  virtual : ∀ key value, prepared.route.rootSourceType = .mapping key value →
    CompatibleMapping.VirtualRoot.Generated compilation prepared.route key value
  ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none

private theorem nil_fields {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {position : Nat} {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root [] position steps keys leaf) :
    steps = [] ∧ keys = [] ∧ leaf = root := by cases path; exact ⟨rfl, rfl, rfl⟩

theorem of_lower {compilation : SourceCoreCompatibleDataPlaces.Context}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
    {fuel : Nat} {expression : ExpressionLowerer} {scope : Scope} {reasonAt : ExpressionId → Word}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {next lowered : Expr} {outputType : Ty}
    {invalid invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (bare : assignment.target.projections = [])
    (accepted : lower compilation compilation.checked.signatures expression fuel source scope site assignment operator (some rhs)
      outputType next reasonAt invalid invalidOperand missing = .ok lowered) :
    ∃ binder prepared index value,
      rootBinder source assignment.target.root = .ok binder ∧
      prepared.route.rootSourceType = binder.scheme.body ∧
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType assignment.target.type ∧
      SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, prepared.route.rootType) ∧
      Layout compilation prepared ∧ expression fuel source scope rhs reasonAt = .ok value ∧
      value.type = prepared.route.leafType ∧
      (operator = .equal ∨ prepared.route.leafType = .word ∨ prepared.route.leafType = .integer) ∧
      lowered = execute prepared (.var index) (SourceCoreCalls.packArguments []) value.expression next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand := by
  cases generated_of_lower accepted with
  | intro route prepared index codes value described lookup preparedBy generated operatorValid rhsGenerated =>
    cases rhsGenerated with
    | present rhsAccepted rhsType =>
      obtain ⟨binder, leaf, description⟩ := CompatiblePlaceDescription.of_describe described
      obtain ⟨routeEq, _, path⟩ := description.prepared preparedBy
      rw [bare] at path
      obtain ⟨steps, keys, rfl⟩ := nil_fields path
      rw [keys] at generated
      cases generated
      have rootEq : prepared.route.rootSourceType = binder.scheme.body := routeEq ▸ description.rootSource
      have types : route.rootType = route.leafType :=
        Except.ok.inj (description.rootProjected.symm.trans (by
          rw [← compilation.checked.catalog.project_runtimeType binder.scheme.body, description.selectedType,
            compilation.checked.catalog.project_runtimeType]
          exact description.leafProjected))
      refine ⟨binder, prepared, index, _, description.binding, rootEq, rootEq ▸ description.selectedType,
        by simpa only [routeEq] using lookup, ?_, rhsAccepted, by simpa only [routeEq] using rhsType.symm, ?_, by simp [routeEq]⟩
      · refine ⟨steps, keys, routeEq ▸ types, rootEq ▸ (routeEq ▸ description.rootProjected), ?_, ?_⟩
        · intro key value declared
          exact routeEq ▸ description.virtual key value (rootEq.symm.trans declared)
        · intro ordinary
          exact routeEq ▸ description.ordinary (fun key value same => ordinary key value (rootEq.trans same))
      · rcases operatorValid with ⟨same, _⟩ | word | integer
        · exact .inl same
        · exact .inr (.inl (routeEq ▸ word))
        · exact .inr (.inr (routeEq ▸ integer))

/-- Any virtual initializer is an actual pure quote; arbitrary expressions
cannot be smuggled into the empty-path normalization receipt. -/
theorem Layout.quoted {compilation : SourceCoreCompatibleDataPlaces.Context} {prepared : Prepared}
    (layout : Layout compilation prepared) {expression : Expr}
    (found : prepared.route.rootMapping = some expression) :
    ∃ value, CompatibleMapping.VirtualRoot.Quoted value expression := by
  classical
  by_cases mapping : ∃ key value, prepared.route.rootSourceType = .mapping key value
  · obtain ⟨key, value, declared⟩ := mapping
    cases layout.virtual key value declared with
    | encoded accepted unchanged quoted root =>
      have same := Option.some.inj (root.symm.trans found)
      subst expression
      exact ⟨_, CompatibleMapping.VirtualRoot.quoted_of_quote quoted⟩
  · have absent := layout.ordinary (fun key value same => mapping ⟨key, value, same⟩)
    rw [absent] at found
    cases found

end Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
