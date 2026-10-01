import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewEdits

/-! Allocation authentication depends on the original binder inventory and its
metadata view. Changing only expression annotations retains the actual emitted
allocation and its indexed ancestry snapshot, including capture references.
These static equalities do not reconstruct runtime allocation history. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewAllocations
open Frontend SourceInference Core
abbrev Request := SourceCoreSourceCells.Request

/-- Reauthenticate the same receipt at an allocation-equivalent source view. -/
def emission {prepared : SourceCoreAllocationCodebook.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : Request} {source : TypedSource}
    (same : SourceCoreAllocationCodebook.sourceView request.source = SourceCoreAllocationCodebook.sourceView source)
    (receipt : SourceCoreAllocationCodebook.Emission prepared owner active request) :
    SourceCoreAllocationCodebook.Emission prepared owner active {request with source} :=
  {receipt with sourceExact := same.symm.trans receipt.sourceExact}

/-- The selected observed layout and all dynamic syntax stay identical. -/
def allocation {prepared : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : Request} {source : TypedSource}
    (same : SourceCoreAllocationCodebook.sourceView request.source = SourceCoreAllocationCodebook.sourceView source)
    (receipt : SourceCoreAllocationLayouts.Allocation prepared owner active request) :
    SourceCoreAllocationLayouts.Allocation prepared owner active {request with source} :=
  {receipt with authentication := emission same receipt.authentication}

/-- The emitter returns the same success or error after a view change. -/
theorem emission_status {prepared : SourceCoreAllocationCodebook.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : Request} {source : TypedSource}
    (same : SourceCoreAllocationCodebook.sourceView request.source = SourceCoreAllocationCodebook.sourceView source) :
    (SourceCoreAllocationCodebook.emitWithReceipt prepared owner active request).map (fun _ => ()) =
      (SourceCoreAllocationCodebook.emitWithReceipt prepared owner active {request with source}).map (fun _ => ()) := by
  unfold SourceCoreAllocationCodebook.emitWithReceipt
  simp (config := {zeta := false}) only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  simp only [same]
  repeat' first | rfl | split
  · rename_i yes no
    exact False.elim (no ⟨yes.1, yes.2.1, same.symm.trans yes.2.2.1, yes.2.2.2⟩)
  · rename_i no yes
    exact False.elim (no ⟨yes.1, yes.2.1, same.trans yes.2.2.1, yes.2.2.2⟩)


/-- Equality of the executable allocator, including rejection paths. -/
theorem allocate_eq {prepared : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : Request} {source : TypedSource}
    (same : SourceCoreAllocationCodebook.sourceView request.source = SourceCoreAllocationCodebook.sourceView source) :
    SourceCoreAllocationLayouts.allocate prepared owner active request =
      SourceCoreAllocationLayouts.allocate prepared owner active {request with source} := by
  have status := emission_status (prepared := prepared.codebook) (owner := owner) (active := active) same
  unfold SourceCoreAllocationLayouts.allocate SourceCoreAllocationLayouts.allocateWithReceipt
  cases left : SourceCoreAllocationCodebook.emitWithReceipt prepared.codebook owner active request <;>
    cases right : SourceCoreAllocationCodebook.emitWithReceipt prepared.codebook owner active {request with source} <;>
    simp only [left, right, Except.map, Except.error.injEq, reduceCtorEq] at status
  · cases status
    rfl
  · simp only [Except.mapError, bind, Except.bind, pure, Except.pure]
    split
    · rename_i absent
      split
      · rfl
      · rename_i entry present
        cases absent.symm.trans present
    · rename_i entry present
      split
      · rename_i absent
        cases present.symm.trans absent
      · rename_i other selected
        have equal : entry = other := Option.some.inj (present.symm.trans selected)
        subst other
        rfl


theorem allocator_eq {prepared : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : Request} {source : TypedSource} (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (same : SourceCoreAllocationCodebook.sourceView request.source = SourceCoreAllocationCodebook.sourceView source) :
    prepared.allocatorAt owner active onError request =
      prepared.allocatorAt owner active onError {request with source} :=
  congrArg (Except.mapError onError) (allocate_eq same)

/-- The real snapshot wrapper selects the same reference and emitted code.
The private annotation constructor is obtained only through its actual factory. -/
theorem annotation {prepared : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : Request} {source : TypedSource} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals : Nat} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    (view : LambdaMetadataViews.MetadataView request.source source)
    (receipt : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (prepared.allocatorAt owner active onError) request) :
    ∃ result : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (prepared.allocatorAt owner active onError) {request with source},
      result.original = receipt.original ∧ result.expression = receipt.expression := by
  have allocated : prepared.allocatorAt owner active onError {request with source} = .ok receipt.original :=
    (allocator_eq onError (CallableIndexedLambdaViewPrefix.sourceView_eq view)).symm.trans receipt.allocated
  cases found : SourceCoreCallableIndexedAllocationFrames.annotateWithReceipt frame globals
      (prepared.allocatorAt owner active onError) {request with source} with
  | error error =>
    unfold SourceCoreCallableIndexedAllocationFrames.annotateWithReceipt at found
    split at found
    · rename_i rejected
      cases allocated.symm.trans rejected
    · cases found
  | ok result =>
    have original := Except.ok.inj (result.allocated.symm.trans allocated)
    refine ⟨result, original, ?_⟩
    rw [result.exact, receipt.exact, original]
    congr 2
    simp only [SourceCoreCallableIndexedAllocationFrames.referenceIndex,
      SourceCoreCallableIndexedAllocationFrames.isNamedInput, view.inputs]
    rfl

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewAllocations
