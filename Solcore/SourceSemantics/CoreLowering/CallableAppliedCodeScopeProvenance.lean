import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectStageScopeReceipts
import Solcore.SourceSemantics.CoreLowering.CallableAppliedViewProvenance

/-! An actual applied read retains the full owner key of its lexical Code.
The read's descriptor and template refer to the same view owner, and its
sealed application receipt checks that owner against the lexical history.
Exact sidecar preparation then identifies the original caller and guard frame.
This does not identify a method from arbitrary selected-source equality or
assert that every Selected witness belongs to a supplied Code's ancestry. -/
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.CoreLowering.CallableAppliedCodeScopeProvenance
open Core Frontend SourceInference
open CallableIndexedLambdaValues CallableIndexedHistory
open SourceCoreCallableAncestryReadRecipes

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {localScope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context}
  (code : Code compiled.indexed function localScope administrative)
  (history : History code)
  {caller : SourceCoreCallableAncestryReadRecipes.State} {view target : Word}
  (read : Read compiled.indexed.ancestry.graph.inputs caller view target)
  (applied : Applied read history.metadata)

include history applied

/-- The actual read and application checks recover the lexical Code's full
specialization key, including all declaration arguments. -/
theorem template_owner : read.template.owner = code.compilation.owner := by
  have sameOrigin : SourceCoreStageCodebook.Origin.lambda
      read.template.owner read.template.id read.template.active =
      .lambda read.entry.view.owner read.entry.view.principal.initializer
        read.entry.view.cumulative :=
    read.templateOrigin.symm.trans read.viewOrigin
  have sameOwner := (SourceCoreStageCodebook.Origin.lambda.inj sameOrigin).1
  exact sameOwner.trans (applied.owner.symm.trans history.owner)

/-- Two real preparations at the recovered key return the same complete
sidecar. No comparison of source tables or method body owners is needed. -/
theorem sidecar_eq {canonical selected : SourceCoreStageContracts.Sidecar}
    (canonicalIssued : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
      code.compilation.owner = .ok canonical)
    (selectedIssued : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
      read.template.owner = .ok selected) : selected = canonical := by
  rw [template_owner code history read applied] at selectedIssued
  exact Except.ok.inj (selectedIssued.symm.trans canonicalIssued)

/-- The resulting applied scope uses the original Code's complete guard
frame, independently of its accumulated semantic source substitution. -/
theorem guard_frame {canonical selected : SourceCoreStageContracts.Sidecar}
    (canonicalIssued : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
      code.compilation.owner = .ok canonical)
    (selectedIssued : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
      read.template.owner = .ok selected)
    (after : Dynamic.Closure) (active : TypeSystem.Substitution) :
    (RecursiveStageRegistry.scope selected active after).guards =
      CallableLedger.frame canonical := by
  rw [sidecar_eq code history read applied canonicalIssued selectedIssued]
  rfl

/-- Genuine principal support fixes the selected sidecar's entire retained
method specialization. Sibling methods are never identified by body owner. -/
theorem principal_caller
    (support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code)
    {selected : SourceCoreStageContracts.Sidecar}
    (selectedIssued : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
      read.template.owner = .ok selected) :
    selected.caller = support.method.specialized := by
  have found := LambdaSourceAlignment.sidecar_lookup selectedIssued
  rw [template_owner code history read applied, support.compilation] at found
  change SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
    support.principal.named.signature.key = .ok selected.caller at found
  have same : selected.caller = support.principal.named.specialized :=
    Except.ok.inj (found.symm.trans support.principal.record)
  exact same.trans support.principal.cached.same

end Solcore.SourceSemantics.CoreLowering.CallableAppliedCodeScopeProvenance
