import Solcore.SourceSemantics.CoreLowering.CellAwareScopePhysical
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftBounds

/-! Ordinary Source execution is lifted at the actual mixed physical state.
A genuine stage rejection retains its reached prefix; all other outcomes
retain the original value or semantic fault and exact heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceLiftBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission (Admission)
open CallableIndexedOwnedAdmittedStagedExpressionBounds (PostAdmission)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (context : SourceSemantics.Context)

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  (named : SourceCoreGeneralFunctions.Function)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (certificate : GenericExpressionMeaning.Certificate)

/-- Source size belongs to the independent ordinary execution. -/
def LiftsAt (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, invocation.source.lookupExpression? id = some node →
    ExpressionHasType invocation.source context id node.type →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical compiled.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed) named.signature.key [] mapping world before store environment →
    ∀ physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
      owner.key.frameLocation = physical.location →
    RecursiveNamedCallBounds.ExpressionOutcome program size context invocation.evidence invocation.source
      environment before id outcome after →
    Staging.Recursive.Lifting.ExpressionLift program registry invocation context environment before id outcome after

def LiftsBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → LiftsAt bridge context model named registry invocation certificate size

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceLiftBounds
