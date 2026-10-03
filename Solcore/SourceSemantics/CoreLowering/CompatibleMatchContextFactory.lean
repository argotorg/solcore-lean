import Solcore.SourceSemantics.CoreLowering.GenericMatchScopedContexts
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchMeaning
import Solcore.SourceSemantics.CoreLowering.CompatiblePatternRuntime
import Solcore.SourceSemantics.CoreLowering.CompatibleRuntimeContextValidity

/-! Match contexts reuse the independent source ledger and signature facts.
The actual compilation context must retain the same solved requirements;
neither emitted code nor native type equality determines unused ledger entries. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchContextFactory
open Core Frontend SourceInference

theorem of_context {values : SourceCoreCompatibleValues.Context}
    {compilation : SourceCoreCompatibleDataMatches.Context} {solved : List SolvedRequirement}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (signatures : context.signatures = values.checked.signatures)
    (sameValues : compilation.values = values)
    (sameLedger : compilation.solvedRequirements = solved) :
    CompatiblePatternLeaves.ContextValid compilation context := by
  refine ⟨?_, valid.ledger.trans sameLedger.symm, valid.valid⟩
  simpa only [SourceCoreCompatibleDataMatches.Context.signatures,
    SourceCoreCompatibleDataMatches.Context.checked, sameValues] using signatures

theorem scoped_context {source : TypedSource} {parent child : SourceSemantics.Context}
    {hiddenIds : List Resolved.LocalId} {scrutineeType : TypeSystem.Ty}
    {cases : List TypedMatchCase} {fallback : Option (List StatementId)}
    {request : GenericMatchChildren.Request} {solved : List SolvedRequirement}
    {evidence : Dynamic.EvidenceEnvironment}
    (related : GenericMatchChildren.ScopedContextFor source parent hiddenIds scrutineeType cases fallback request child)
    (valid : CompatibleExpressionLiterals.ContextValid solved parent evidence) :
    CompatibleExpressionLiterals.ContextValid solved child evidence := by
  cases related with
  | arm _ _ _ extended _ => exact CompatibleMatchMeaning.valid_binders evidence valid extended
  | default => exact valid

/-- The actual fixed compatible loop policy constructs this exact match
context. The signature and ledger obligations come from source entry facts. -/
theorem fixed_policy {values : SourceCoreCompatibleValues.Context} {solved : List SolvedRequirement}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (signatures : context.signatures = values.checked.signatures)
    (assignments : SourceCoreAssignmentFaultSites.Table)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (owner : SourceSpecialization.SpecializationKey)
    (expression : SourceCoreCompatibleDataMatches.ExpressionLowerer)
    (sourceCells : Option SourceCoreSourceCells.Allocator)
    (definitions : Option DataEnvironment) :
    let compilation : SourceCoreCompatibleDataMatches.Context := ⟨values, solved, sourceCells, definitions⟩
    (SourceCoreCompatibleDataMatches.loopPolicy values solved assignments diagnostics owner expression
      sourceCells definitions).lowerMatch = some (SourceCoreCompatibleDataMatches.lowerWithReasons compilation) ∧
      compilation.solvedRequirements = solved ∧ CompatiblePatternLeaves.ContextValid compilation context := by
  exact ⟨rfl, rfl, of_context valid signatures rfl rfl⟩

/-- Runtime match contexts keep every solved row. Coverage is transported by
its source context interface; pattern matching itself does not consume it. -/
theorem of_runtime {values : SourceCoreCompatibleValues.Context}
    {compilation : SourceCoreCompatibleDataMatches.Context} {solved : List SolvedRequirement}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    (valid : CompatibleRuntimeContextValidity.Valid solved context evidence)
    (signatures : context.signatures = values.checked.signatures)
    (sameValues : compilation.values = values)
    (sameLedger : compilation.solvedRequirements = solved) :
    CompatiblePatternRuntime.ContextValid compilation context := by
  refine ⟨?_, valid.ledger.trans sameLedger.symm, valid.runtime⟩
  simpa only [SourceCoreCompatibleDataMatches.Context.signatures,
    SourceCoreCompatibleDataMatches.Context.checked, sameValues] using signatures

private theorem runtime_binders {owner : Resolved.DeclarationId} {parent child : SourceSemantics.Context}
    {binders : List TypedBinder} {solved : List SolvedRequirement} {evidence : Dynamic.EvidenceEnvironment}
    (extended : BindersExtend owner parent binders child)
    (valid : CompatibleRuntimeContextValidity.Valid solved parent evidence) :
    CompatibleRuntimeContextValidity.Valid solved child evidence := by
  induction extended with
  | nil => exact valid
  | cons head tail ih => exact ih (valid.extend head)

theorem scoped_runtime {source : TypedSource} {parent child : SourceSemantics.Context}
    {hiddenIds : List Resolved.LocalId} {scrutineeType : TypeSystem.Ty}
    {cases : List TypedMatchCase} {fallback : Option (List StatementId)}
    {request : GenericMatchChildren.Request} {solved : List SolvedRequirement}
    {evidence : Dynamic.EvidenceEnvironment}
    (related : GenericMatchChildren.ScopedContextFor source parent hiddenIds scrutineeType cases fallback request child)
    (valid : CompatibleRuntimeContextValidity.Valid solved parent evidence) :
    CompatibleRuntimeContextValidity.Valid solved child evidence := by
  cases related with
  | arm _ _ _ extended _ => exact runtime_binders extended valid
  | default => exact valid

theorem fixed_policy_runtime {values : SourceCoreCompatibleValues.Context} {solved : List SolvedRequirement}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    (valid : CompatibleRuntimeContextValidity.Valid solved context evidence)
    (signatures : context.signatures = values.checked.signatures)
    (assignments : SourceCoreAssignmentFaultSites.Table)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (owner : SourceSpecialization.SpecializationKey)
    (expression : SourceCoreCompatibleDataMatches.ExpressionLowerer)
    (sourceCells : Option SourceCoreSourceCells.Allocator)
    (definitions : Option DataEnvironment) :
    let compilation : SourceCoreCompatibleDataMatches.Context := ⟨values, solved, sourceCells, definitions⟩
    (SourceCoreCompatibleDataMatches.loopPolicy values solved assignments diagnostics owner expression
      sourceCells definitions).lowerMatch = some (SourceCoreCompatibleDataMatches.lowerWithReasons compilation) ∧
      compilation.solvedRequirements = solved ∧ CompatiblePatternRuntime.ContextValid compilation context := by
  exact ⟨rfl, rfl, of_runtime valid signatures rfl rfl⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchContextFactory
