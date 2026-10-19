import Solcore.SourceSemantics.CoreLowering.CellAwareScopeGeneralizedReadBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeExpressionBounds

/-! Ordinary expression composition projects the actual generalized-read
post while indirect application retains its stronger materialization witness. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeGeneralizedReadProjection
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (context : SourceSemantics.Context)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  (named : SourceCoreGeneralFunctions.Function)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep)

def Certificate : GenericExpressionMeaning.Certificate := fun scope id lowered =>
  ∃ reasonAt,
    ∃ certificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named invocation.source scope id reasonAt lowered,
      Nonempty (GeneralizedLocalNamedRecipeCompilation.Receipt certificate)

theorem preserves {size : Nat}
    (meaning : CellAwareScopeGeneralizedReadBounds.PreservesAt bridge context model named registry invocation faults size) :
    CellAwareScopeExpressionBounds.PreservesAt bridge context model named registry invocation
      (Certificate (compiled := compiled) named invocation) faults size := by
  intro scope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees typed initial admitted authority physical owner ownerFrame trace
  obtain ⟨reasonAt, certificate, ⟨recipe⟩⟩ := certified
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, _strong, rest⟩ :=
    meaning certificate recipe found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner ownerFrame trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, rest⟩

theorem reflects {size : Nat}
    (meaning : CellAwareScopeGeneralizedReadBounds.ReflectsAt bridge context model named registry invocation faults size) :
    CellAwareScopeExpressionBounds.ReflectsAt bridge context model named registry invocation
      (Certificate (compiled := compiled) named invocation) faults size := by
  intro scope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees typed initial admitted authority physical owner ownerFrame completed
  obtain ⟨reasonAt, certificate, ⟨recipe⟩⟩ := certified
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, _strong, rest⟩ :=
    meaning certificate recipe found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner ownerFrame completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, rest⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeGeneralizedReadProjection
