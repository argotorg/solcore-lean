import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedInitialContextValidity

/-! The actual named terminal and selected Source scope retain the caller's
complete ledger and resolved dictionary. No execution trace is required. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedEvidenceCallerFrames
open Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}

/-- The original caller preparation is reindexed by its genuine cached row. -/
structure CallerAt (terminal : Terminal header) (child : Staging.Recursive.Scope) where
  prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled terminal.prepared.named.specialized
  signatures : header.context.signatures = compiled.sourceProgram.signatures
  ledger : header.context.solvedRequirements = terminal.prepared.named.specialized.function.solvedRequirements
  assumptions : ∀ goal, goal ∈ terminal.prepared.named.specialized.assumptions → goal ∈ header.context.assumptions
  unique : RequirementIdsUnique header.context
  dictionary : child.evidence = prepared.view.evidence

private theorem reindex_view {left right : SourceSpecialization.SpecializedFunction}
    (same : left = right) (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled left) :
    (same ▸ prepared).view = prepared.view := by
  cases same
  rfl

/-- Parameter installation preserves the original caller's signature catalog,
assumptions and ledger; scope selection preserves its exact dictionary. -/
def of_selected (terminal : Terminal header) {stages : Staging.Recursive.Registry}
    {child : Staging.Recursive.Scope} (selected : stages.Closure header.function child)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    CallerAt terminal child := by
  let prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled terminal.prepared.named.specialized :=
    terminal.prepared.same.symm ▸ terminal.prepared
  have view : prepared.view = terminal.prepared.view := reindex_view _ _
  have fields := RecursiveNamedInitialContextValidity.mono_fields header.extended
  refine ⟨prepared, ?_, header.valid.ledger.trans terminal.aligned.solved, ?_, ?_, ?_⟩
  · rw [fields.signatures, terminal.aligned.function]
    rfl
  · intro goal member
    rw [fields.assumptions, terminal.aligned.function]
    exact member
  · exact (RecursiveNamedInitialContextValidity.scoped_ledger header.frame header.extended wellFormed).idsUnique
  · rw [stages.evidence selected, terminal.aligned.function, view]

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedEvidenceCallerFrames
