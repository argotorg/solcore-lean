import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CellAllocationReadiness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedFlowOutcomes
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeTypedSourceSites

/-! Common mixed-cell flow bounds retain ordinary control outcomes and exact
generalized descriptor effects. Scoped and function bodies differ only in their
mode; actual compiler trees close these internal recursive contracts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationFlowBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (context : SourceSemantics.Context)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  (index : ActualBodyInvocation.Index compiled)
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.trackedModel compiled.indexed)))
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)
  (scope : SourceCoreLocalCell.Scope) (mode : Bool) (statements : List StatementId)
  (expected : TypeSystem.Ty) (type : Ty) (code : Expr)

/-- Source and native grades remain independent. Every reached branch keeps
its exact mixed heap and restores the caller's lexical observations. -/
def PreservesAt (size : Nat) : Prop :=
  ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical compiled.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.trackedModel compiled.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context index.source →
    invocation.evidence.Covers context →
    context.solvedRequirements = index.compilation.solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements index.source context statements →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
      Admission bridge context initial →
      CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.trackedModel compiled.indexed)
        index.owner index.active mapping world before store environment →
    ∀ physical : CellAwareInvocationPhysical.Physical compiled index context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
      owner.key.frameLocation = physical.location →
      ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {finalContext outcome after},
      Staging.Recursive.Size.StatementsIn program registry mode size invocation context environment before
        statements finalContext outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename embedding) value finalStore ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.trackedModel compiled.indexed))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.trackedModel compiled.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ Post bridge context expected outcome reached

/-- Actual native completion reconstructs the chosen Source branch and its
real allocations, failures and control transfers. -/
def ReflectsAt (size : Nat) : Prop :=
  ∀ {mapping world actualContext environment canonical actual before store embedding value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical compiled.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.trackedModel compiled.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context index.source →
    invocation.evidence.Covers context →
    context.solvedRequirements = index.compilation.solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements index.source context statements →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
      Admission bridge context initial →
      CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.trackedModel compiled.indexed)
        index.owner index.active mapping world before store environment →
    ∀ physical : CellAwareInvocationPhysical.Physical compiled index context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
      owner.key.frameLocation = physical.location →
      ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    EvaluationSize size actual store (code.rename embedding) value finalStore →
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program registry mode sourceSize invocation context environment before
        statements finalContext outcome after ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.trackedModel compiled.indexed))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.trackedModel compiled.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ Post bridge context expected outcome reached

def PreservesAtMost (budget : Nat) : Prop :=
  ∀ size, size ≤ budget → PreservesAt bridge context model index producer registry invocation faults administrative scope mode statements expected type code size

def PreservesBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → PreservesAt bridge context model index producer registry invocation faults administrative scope mode statements expected type code size

def ReflectsAtMost (budget : Nat) : Prop :=
  ∀ size, size ≤ budget → ReflectsAt bridge context model index producer registry invocation faults administrative scope mode statements expected type code size

def ReflectsBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → ReflectsAt bridge context model index producer registry invocation faults administrative scope mode statements expected type code size

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationFlowBounds
