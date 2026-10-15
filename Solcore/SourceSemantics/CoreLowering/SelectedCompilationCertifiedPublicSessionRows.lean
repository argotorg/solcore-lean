import Solcore.SourceSemantics.CoreLowering.CertifiedPublicSessionRows
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession

/-! A full eligible cached row and its singleton physical slot identify the
actual first matching public root, including when unrelated keys repeat. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedOrdinaryCatalogReceipts (Catalog Eligible)
open SelectedCompilationPublicSessionState (StartedCall)

abbrev EligibleRow := CertifiedPublicSession.EligibleRow

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {key : SourceCoreIndexedSession.Key}

variable {recipe : SourceCoreIndexedSession.Recipe}

theorem Issued.recover_start_row (issued : Issued recipe)
    {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : issued.State anchor session entries)
    {publicArguments : List SourceCorePublicValues.Value} {options : SourceCoreExecution.RunOptions}
    (call : StartedCall session key publicArguments options) (row : EligibleRow recipe.compiled key) :
    ∃ request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store,
      request.header.named = row.named := by
  apply RecursiveNamedPublicPhysicalFrontdoor.recover_start_at_with issued.prepared
    issued.catalog.inputs issued.catalog.rows state.atRecipe state.history.semantic.current.1 state.atSession
    (fun _ header => header.named = row.named) _ call.started
  intro root selected
  have rootKey : root.key = key := of_decide_eq_true (List.find?_some
    (p := fun candidate : SourceCoreIndexedSession.Root recipe.compiled => decide (candidate.key = key)) selected)
  exact row.selected issued.catalog
    (SourceCoreIndexedSession.Recipe.prepare_roots issued.prepared (List.mem_of_find?_eq_some selected)) rootKey

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
