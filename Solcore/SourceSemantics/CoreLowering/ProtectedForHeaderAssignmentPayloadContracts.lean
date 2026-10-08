import Solcore.SourceSemantics.CoreLowering.ProtectedStateForHeaderReady
import Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderStructuralElimination

/-! Assignment callbacks retain the original actual-state readiness and result.
Only the diagnostic input is parameterized by the selected static payload. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedForHeader.Stateful.WithReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open ProtectedStateTransition
open RecursiveNamedLexicalContracts.Stateful.WithReady
universe u v
variable {Records : Type v}
def AssignmentFaultPreservesWithPayloadAt (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol)
    (assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop)
    {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (certificate : GenericExpressionMeaning.Certificate) (context : SourceSemantics.Context)
    (administrative : Core.Context) (faults : FunctionCalls.FaultRep) (budget : Nat)
    (AP : ∀ {scope assignment operator rhs},
      GenericAssignmentStatements.Head values source context certificate scope administrative ambient.definitions assignment operator rhs → Prop) : Prop :=
  ∀ {scope assignment operator rhs}
    (head : GenericAssignmentStatements.Head values source context certificate scope administrative ambient.definitions assignment operator rhs)
    (_facts : assignmentFacts context assignment operator rhs)
    {mapping world environment canonical actual before store actualContext ξ},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    readiness.Ready context initial →
    AP head →
  ∀ {reason after size},
    SourceExecutionSize.SourcePlaceAssignmentFaults program size context evidence source environment before
      assignment.target operator rhs reason after → size ≤ budget → ∀ next output,
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      FaultTransition readiness initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

def AssignmentReflectsWithPayloadAt (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol)
    (assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop)
    {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (certificate : GenericExpressionMeaning.Certificate) (context : SourceSemantics.Context)
    (administrative : Core.Context) (faults : FunctionCalls.FaultRep) (budget : Nat)
    (AP : ∀ {scope assignment operator rhs},
      GenericAssignmentStatements.Head values source context certificate scope administrative ambient.definitions assignment operator rhs → Prop) : Prop :=
  ∀ {scope assignment operator rhs}
    (head : GenericAssignmentStatements.Head values source context certificate scope administrative ambient.definitions assignment operator rhs)
    (_facts : assignmentFacts context assignment operator rhs)
    {mapping world environment canonical actual before store actualContext ξ},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    readiness.Ready context initial →
    AP head →
  ∀ {next output value finalStore size},
    EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore → size ≤ budget →
    AssignmentResultAt protocol readiness size values.checked registry functions program context evidence source faults
      scope (head.writtenContext actualContext) assignment.target operator rhs environment canonical actual before store mapping world
      initial (next.rename ξ) output value finalStore

end Solcore.SourceSemantics.CoreLowering.ProtectedForHeader.Stateful.WithReady
