import Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderFacts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedEvidenceCallerFrames

/-! The actual prepared named row and selected Source scope determine the
complete caller dictionary at every lexical context. Local changes preserve
the nonlocal context fields; no terminal body or execution premise is needed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedEvidenceScopedCallerFrames
open Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}

/-- The dictionary keeps the original prepared row; the ledger and signature
facts refer to the actual context reached inside that named body. -/
structure CallerAt (actual : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (context : SourceSemantics.Context) (child : Staging.Recursive.Scope) where
  prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled actual.named.specialized
  signatures : context.signatures = compiled.sourceProgram.signatures
  ledger : context.solvedRequirements = actual.named.specialized.function.solvedRequirements
  assumptions : ∀ goal, goal ∈ actual.named.specialized.assumptions → goal ∈ context.assumptions
  unique : RequirementIdsUnique context
  dictionary : child.evidence = prepared.view.evidence

private theorem reindex_view {left right : SourceSpecialization.SpecializedFunction}
    (same : left = right) (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled left) :
    (same ▸ prepared).view = prepared.view := by
  cases same
  rfl

/-- Header preparation fixes the complete caller dictionary. Parameter entry
and subsequent lexical context changes preserve its assumptions and ledger. -/
def of_selected
    (actual : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {instantiation : DeclarationInstantiation}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt actual instantiation header)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child)
    {context : SourceSemantics.Context}
    (fields : Dynamic.RuntimeContextFields header.context context)
    (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    CallerAt actual context child := by
  let prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled actual.named.specialized :=
    actual.same.symm ▸ actual
  have view : prepared.view = actual.view := reindex_view _ _
  have parameters := RecursiveNamedInitialContextValidity.mono_fields header.extended
  refine ⟨prepared, ?_, fields.solvedRequirements.trans (header.valid.ledger.trans aligned.solved), ?_, ?_, ?_⟩
  · rw [fields.signatures, parameters.signatures, aligned.function]
    rfl
  · intro goal member
    rw [fields.assumptions, parameters.assumptions, aligned.function]
    exact member
  · simpa only [RequirementIdsUnique, fields.solvedRequirements] using
      (SelectedCompilationHeaderFacts.scoped_ledger certified).idsUnique
  · rw [stages.evidence selected, aligned.function, view]

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedEvidenceScopedCallerFrames
