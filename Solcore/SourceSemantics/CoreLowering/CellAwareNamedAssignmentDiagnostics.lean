import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIssuedAssignmentRecipes
import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticAuthorityReception

/-! The actual named specialization and its issued place table provide reached
assignment diagnostics in the receiving public registry. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedAssignmentDiagnostics
open Core Frontend SourceInference CompatiblePayload
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}

/-- Source identity and diagnostic token identity come from the original
specialization and actual compiler issuance. -/
theorem source_port
    (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key = .ok named.specialized)
    (unique : NodeOccurrencesUnique (source named))
    (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed diagnostics) :
    Nonempty (PreparedAssignmentDiagnosticAuthority.SourcePort whole (source named)
      (fun site root => diagnostics.placeReason named.signature.key site root none)
      (fun site root raw => diagnostics.placeReason named.signature.key site root (some raw))) := by
  obtain ⟨issuer, present, _sameBase, samePlaces⟩ := issued
  refine ⟨⟨named.signature.key, named.specialized, record, rfl, unique, issuer, present, ?_, ?_⟩⟩
  · intro site root
    simp only [SourceCoreDataPlaceFaultSites.Program.placeReason, samePlaces]
  · intro site root raw
    simp only [SourceCoreDataPlaceFaultSites.Program.placeReason, samePlaces]

universe u v

theorem ready
    (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key = .ok named.specialized)
    (unique : NodeOccurrencesUnique (source named))
    (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed diagnostics)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver whole.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt whole.indexed completion.entry
      completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {ambient : AmbientDefinitions whole.compatible.checked.catalog.definitions}
    (functions : FunctionModel whole.compatible.checked.catalog ambient)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u,v} Records) :
    PreparedAssignmentReachedDiagnostics.Ready (values := .initial whole.compatible.checked)
      functions protocol (source named)
      (fun site root => diagnostics.placeReason named.signature.key site root none)
      (fun site root raw => diagnostics.placeReason named.signature.key site root (some raw))
      completion.result.context.registry
      (fun reason token => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token) := by
  obtain ⟨port⟩ := source_port record unique issued
  exact port.ready receiver functions protocol

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedAssignmentDiagnostics
