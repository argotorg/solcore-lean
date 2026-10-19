import Solcore.SourceSemantics.CoreLowering.CellAwareScopePhysical
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedRecipeCompilation
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedAssociation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds

/-! Direct generalized reads return the actual retained materialization and
shared frame reference. Indirect sequencing uses this positive witness after
the real argument effects; a plain payload relation is not used to guess it. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeGeneralizedReadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission (Admission)
open CallableIndexedOwnedAdmittedStagedExpressionBounds (PostAdmission)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (context : SourceSemantics.Context)

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  (named : SourceCoreGeneralFunctions.Function)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep)

/-- A successful direct generalized read retains its actual closure and the
same physical frame that the later call must use. Faults need no closure. -/
def StrongResult (mapping : LocationMap) (world : StoreTyping) (location : Core.Location)
    (outcome : Staging.Recursive.Outcome) (value : Value) : Prop :=
  ∀ sourceValue, outcome = .value sourceValue →
    ∃ function native bindings parameter result,
      sourceValue = .closure function ∧ value = .inRight .word native ∧
      ∃ association : GeneralizedLocalMaterializedAssociation.Association compiled
          mapping world function native bindings parameter result,
        association.AtFrame location

theorem StrongResult.extend {mapping world nextMap nextWorld location outcome value}
    (strong : StrongResult (compiled := compiled) mapping world location outcome value)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld) :
    StrongResult (compiled := compiled) nextMap nextWorld location outcome value := by
  intro sourceValue same
  obtain ⟨function, native, bindings, parameter, result, source, output, association, atFrame⟩ := strong sourceValue same
  refine ⟨function, native, bindings, parameter, result, source, output, association.extend maps worlds, ?_⟩
  cases association
  exact atFrame

/-- Source size is the grade of the genuine staged trace. -/
def PreservesAt (size : Nat) : Prop :=
  ∀ {scope id reasonAt lowered},
  ∀ certificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named invocation.source scope id reasonAt lowered,
    GeneralizedLocalNamedRecipeCompilation.Receipt certificate →
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
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) registry size invocation context environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type lowered.type faults outcome value ∧
      StrongResult (compiled := compiled) finalMap finalWorld owner.key.frameLocation outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.type outcome reached

/-- Native size is measured independently; reflection returns the actual
Source grade and the exact staged outcome, including a nested failing scope. -/
def ReflectsAt (size : Nat) : Prop :=
  ∀ {scope id reasonAt lowered},
  ∀ certificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named invocation.source scope id reasonAt lowered,
    GeneralizedLocalNamedRecipeCompilation.Receipt certificate →
  ∀ {node}, invocation.source.lookupExpression? id = some node →
    ExpressionHasType invocation.source context id node.type →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
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
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) registry sourceSize invocation context environment before id outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type lowered.type faults outcome value ∧
      StrongResult (compiled := compiled) finalMap finalWorld owner.key.frameLocation outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.type outcome reached

def PreservesAtMost (budget : Nat) : Prop :=
  ∀ size, size ≤ budget → PreservesAt bridge context model named registry invocation faults size

def PreservesBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → PreservesAt bridge context model named registry invocation faults size

def ReflectsBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → ReflectsAt bridge context model named registry invocation faults size


end Solcore.SourceSemantics.CoreLowering.CellAwareScopeGeneralizedReadBounds
