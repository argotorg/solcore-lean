import Solcore.SourceSemantics.CoreLowering.CellAwareScopeExpressionBounds
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedAssociation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureSourceArguments
import Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterMeaning

/-! The application leaf consumes the actual materialized local closure at
its reached argument state. Its caller, frame owner and concrete effects are
retained; the finite expression dispatcher supplies the ordered prefix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission (Admission)
open CallableIndexedOwnedAdmittedStagedExpressionBounds (PostAdmission)
open GeneralizedLocalMaterializedAssociation (Association)
open CallableIndexedOwnedStoredClosureSourceArguments (SourceArguments)
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

/-- The actual Source application begins after all argument effects. -/
def PreservesAt (size : Nat) : Prop :=
  ∀ {scope mapping world environment canonical before store function native bindings parameter result sources values},
  ∀ association : Association compiled mapping world function native bindings parameter result,
    SourceArguments function before sources →
    Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function →
    CallableIndexedParameterMeaning.Arguments model mapping world bindings sources values →
    GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
      (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
      named.signature.key [] mapping world before store environment →
  ∀ physical : CellAwareScopePhysical.Physical compiled named context scope canonical
      mapping world before store environment,
  ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location → association.AtFrame owner.key.frameLocation →
  ∀ {outcome after},
    Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) registry size invocation
      context before (.closure function) sources outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates [native, DataPatternValues.packValues values] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld function.resultType result faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context function.resultType outcome reached

/-- The native payload computation yields its independent Source grade. -/
def ReflectsAt (size : Nat) : Prop :=
  ∀ {scope mapping world environment canonical before store function native bindings parameter result sources values},
  ∀ association : Association compiled mapping world function native bindings parameter result,
    SourceArguments function before sources →
    Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function →
    CallableIndexedParameterMeaning.Arguments model mapping world bindings sources values →
    GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
      (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
      named.signature.key [] mapping world before store environment →
  ∀ physical : CellAwareScopePhysical.Physical compiled named context scope canonical
      mapping world before store environment,
  ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location → association.AtFrame owner.key.frameLocation →
  ∀ {value finalStore},
    EvaluationSize size [native, DataPatternValues.packValues values] store
      CallableIndexedLambdaCalls.applyPayload value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) registry sourceSize invocation
        context before (.closure function) sources outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld function.resultType result faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context function.resultType outcome reached

def PreservesBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → PreservesAt bridge context model named registry invocation faults size

def ReflectsBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → ReflectsAt bridge context model named registry invocation faults size

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeApplicationBounds
