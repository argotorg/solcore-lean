import Solcore.SourceSemantics.CoreLowering.CompatibleProjectedBitNotStatementHead
import Solcore.SourceSemantics.CoreLowering.ProtectedPlaceReachedDiagnostics

/-! The unary head's preparation is tied to its exact layout site. Diagnostic
laws refer only to genuine reached missing/default and uninitialized phases. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleProjectedBitNotStatements
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open SourceCoreCompatibleDataPlaces ProtectedPlaceReachedDiagnostics
universe u v
variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {certificate : GenericExpressionMeaning.Certificate} {scope : Scope} {administrative : Core.Context}
  {definitions : DataEnvironment} {assignment : AssignmentResolution}

inductive Head.PreparedAt
    (head : Head values source context certificate scope administrative definitions assignment)
    (site : SourceCoreElaboration.ErrorSite) (fuel : Nat) (invalidProjection : Word)
    (missing : TypeSystem.Ty → Word) : Prop where
  | intro (siteEq : head.site = site) (route : Route)
      (described : describe values values.checked.signatures source site assignment = .ok route)
      (preparedBy : prepare values fuel route invalidProjection missing = .ok head.prepared) :
      head.PreparedAt site fuel invalidProjection missing

structure Head.ReachedErrors
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (head : Head values source context certificate scope administrative ambient.definitions assignment)
    (environment : Dynamic.Environment) {initialIndex : ProtectedStateTransition.Index}
    (initial : protocol.State initialIndex) (faults : FunctionCalls.FaultRep)
    {registry : SourceCoreRawMetadata.Registry} : Prop where
  missing : MissingFor values.checked registry functions protocol source head.site assignment.target
    head.prepared head.leaf initial faults
  uninitialized : UninitializedFor values.checked registry functions protocol environment assignment.target
    head.prepared initial faults

end Solcore.SourceSemantics.CoreLowering.CompatibleProjectedBitNotStatements
