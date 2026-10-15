import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedTarget

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedTargetInversion
open Frontend SourceInference Staging.Recursive

variable {program : Program} {source : TypedSource} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {place : PlaceResolution} {target : Dynamic.ResolvedPlace}
  {size : Nat} {reason : Dynamic.SemanticFault}

/-- The actual projection derivation supplies its ordered key row and snapshot. -/
theorem resolved
    (trace : SourceExecutionSize.SourcePlaceResolves program size context evidence source environment before place target after) :
    ∃ keySize values, keySize < size ∧
      SourceExecutionSize.ExpressionsEvaluate program keySize context evidence source environment before
        (ProjectedTarget.keys place.projections) values after ∧
      ProjectedTarget.Snapshot environment before after place values target := by
  cases trace with
  | intro lookup initialRead projections currentRead initialValue selection =>
      obtain ⟨values, keySize, shaped, keys, bound⟩ := RecursiveNamedPlaceKeyContracts.projections_values projections
      refine ⟨keySize, values, Nat.lt_of_le_of_lt bound (SourceExecutionSize.child_lt_stepSize (by simp)), ?_,
        .intro lookup initialRead (ProjectedTarget.Values.of_data shaped) currentRead initialValue selection⟩
      simpa only [ProjectedTarget.keys_eq_sourceKeys] using keys

/-- No earlier fault is replaced by a getter or RHS result. -/
theorem failed
    (trace : SourceExecutionSize.SourcePlaceFaults program size context evidence source environment before place reason after) :
    (after = before ∧ ProjectedTarget.RootFault environment before place reason) ∨
    (∃ keySize, keySize < size ∧ ProjectedTarget.RootReady environment before place ∧
      SourceExecutionSize.ExpressionsFault program keySize context evidence source environment before
        (ProjectedTarget.keys place.projections) reason after) ∨
    (∃ keySize values, keySize < size ∧
      SourceExecutionSize.ExpressionsEvaluate program keySize context evidence source environment before
        (ProjectedTarget.keys place.projections) values after ∧
      ProjectedTarget.GetterFault environment before after place values reason) := by
  cases trace with
  | unbound missing => exact .inl ⟨rfl, .unbound missing⟩
  | dangling lookup missing => exact .inl ⟨rfl, .dangling lookup missing⟩
  | projectionExpression lookup read fault =>
      obtain ⟨keySize, keys, bound⟩ := RecursiveNamedPlaceKeyContracts.projections_fault fault
      exact .inr (.inl ⟨keySize, Nat.lt_of_le_of_lt bound (SourceExecutionSize.child_lt_stepSize (by simp)),
        .intro lookup read, by simpa only [ProjectedTarget.keys_eq_sourceKeys] using keys⟩)
  | danglingAfterProjections lookup read projections missing =>
      obtain ⟨values, keySize, shaped, keys, bound⟩ := RecursiveNamedPlaceKeyContracts.projections_values projections
      exact .inr (.inr ⟨keySize, values, Nat.lt_of_le_of_lt bound (SourceExecutionSize.child_lt_stepSize (by simp)),
        by simpa only [ProjectedTarget.keys_eq_sourceKeys] using keys,
        .dangling lookup read (ProjectedTarget.Values.of_data shaped) missing⟩)
  | projectionRead lookup initialRead projections currentRead initialValue fault =>
      obtain ⟨values, keySize, shaped, keys, bound⟩ := RecursiveNamedPlaceKeyContracts.projections_values projections
      exact .inr (.inr ⟨keySize, values, Nat.lt_of_le_of_lt bound (SourceExecutionSize.child_lt_stepSize (by simp)),
        by simpa only [ProjectedTarget.keys_eq_sourceKeys] using keys,
        .projection lookup initialRead (ProjectedTarget.Values.of_data shaped) currentRead initialValue fault⟩)
  | uninitialized lookup initialRead projections currentRead empty notMapping nonempty =>
      obtain ⟨values, keySize, shaped, keys, bound⟩ := RecursiveNamedPlaceKeyContracts.projections_values projections
      exact .inr (.inr ⟨keySize, values, Nat.lt_of_le_of_lt bound (SourceExecutionSize.child_lt_stepSize (by simp)),
        by simpa only [ProjectedTarget.keys_eq_sourceKeys] using keys,
        .uninitialized lookup initialRead (ProjectedTarget.Values.of_data shaped) currentRead empty notMapping nonempty⟩)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedTargetInversion
