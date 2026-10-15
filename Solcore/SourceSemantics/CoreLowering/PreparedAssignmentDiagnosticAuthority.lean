import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentReachedDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPlaceReachedDiagnostics

/-! Assignment tokens retain their exact specialized Source and compiler
inventory. Receiving metadata is supplied by the actual public call. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticAuthority
open Core Frontend SourceInference GeneralHeap CompatiblePayload

structure SourcePort (compiled : SourceCoreUnifiedCompilation.Compiled)
    (source : TypedSource)
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word) where
  owner : SourceSpecialization.SpecializationKey
  row : SourceSpecialization.SpecializedFunction
  record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan owner = .ok row
  sourceEq : source = row.function.typedBody
  unique : NodeOccurrencesUnique source
  issuer : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)
  present : compiled.indexed.base.diagnostics = some issuer
  invalidToken : ∀ site root, invalidProjection site root = issuer.program.placeReason owner site root none
  missingToken : ∀ site root raw, missingDefault site root raw = issuer.program.placeReason owner site root (some raw)

universe u v

/-- The dynamic boundary supplies the receiving table for each retained
compiler origin. Public callers construct this from their actual receiver. -/
def Interprets (compiled : SourceCoreUnifiedCompilation.Compiled)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) : Prop :=
  ∀ {source invalidProjection missingDefault},
    SourcePort compiled source invalidProjection missingDefault →
    ∀ {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
      (functions : FunctionModel compiled.compatible.checked.catalog ambient)
      {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records),
    PreparedAssignmentReachedDiagnostics.Ready (values := .initial compiled.compatible.checked)
      functions protocol source invalidProjection missingDefault registry faults

end Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticAuthority
