import Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceLiftBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedGeneralizedPrefix
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageBodyLiftBounds

/-! Body lifting starts from independent ordinary Source execution at the actual
mixed physical scope. It records the exact reached prefix of a stage rejection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceBodyLiftBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

def Lifts {administrative : Core.Context}
    (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope) (statements : List StatementId) : Prop :=
    ∀ {size},
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (source named) →
    invocation.evidence.Covers context →
    context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (source named) context statements →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
      named.signature.key [] mapping world before store environment →
    ∀ physical : CellAwareScopePhysical.Physical whole named context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location →
    ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {finalContext outcome after},
    RecursiveNamedCallBounds.FunctionOutcome program size context invocation.evidence invocation.source environment before
      statements finalContext outcome after →
    SelectedCompilationStageBodyLiftBounds.BodyLift program registry true invocation context environment before
      statements finalContext outcome after

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceBodyLiftBounds
