import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaSourceDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaJointStaticReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedPointwiseBareAssignmentHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedPointwiseProjectedAssignmentHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalReadiness
import Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderAssignmentPayloadContracts

/-! The selected lambda assignment packet supplies its actual owning Source
occurrence and compiler preparation. Only precise reached table interpretation
and strict expression children are requested at the current admitted state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaAssignmentReadiness
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open ProtectedForHeader.Stateful.WithReady
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {owner : SourceSpecialization.SpecializationKey} {source : TypedSource}
  (issued : IssuedSource compiled owner source)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
  (functions : FunctionModel compiled.compatible.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  (evidence : Dynamic.EvidenceEnvironment)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (unique : NodeOccurrencesUnique source)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {context : SourceSemantics.Context}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {administrative : Core.Context} {faults : FunctionCalls.FaultRep}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {factory : AssignmentDiagnosticOrigins.Factory true diagnosticPolicy source issued.invalidOperand}

/-- The interpretation concerns one actual projected packet at its real input. -/
def ReachedInterpretations (table : SourceCoreFaultSites.Table) : Prop :=
  ∀ {scope assignment operator rhs}
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) source context
      (certificates context) scope administrative ambient.definitions assignment operator rhs)
    {environment : Dynamic.Environment} {index : ProtectedStateTransition.Index}
    (initial : callerProtocol.State index), Admission bridge context initial →
    GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head →
    assignment.target.projections ≠ [] →
    CallableIndexedOwnedPublicPreparedShapeDiagnostics.ReachedTableInterpretation
      compiled.compatible.checked registry functions callerProtocol environment assignment.target head.prepared initial table faults

private theorem operand_law {scope assignment operator rhs}
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) source context
      (certificates context) scope administrative ambient.definitions assignment operator rhs)
    {site : SourceCoreElaboration.ErrorSite}
    (origin : AssignmentDiagnosticOrigins.Occurs source site assignment operator rhs)
    (same : head.invalid = issued.invalidOperand site assignment.target.root operator)
    (included : ∀ reason token, GenericAssignmentDiagnostics.OperandRep issued.assignments reason token → faults reason token) :
    AssignmentOperandDiagnostics.OperandsLaw faults operator head.invalid := by
  exact same.symm ▸ origin.prepared issued.typing.2 issued.assignmentsPrepared included

variable {table : SourceCoreFaultSites.Table}
  (rebuilt : issued.diagnostics.tableForRegistry registry extension = .ok table)
  (interprets : ReachedInterpretations issued bridge functions table)
  (included : ∀ reason token, GenericAssignmentDiagnostics.OperandRep issued.assignments reason token → faults reason token)
  (signatures : context.signatures = compiled.compatible.checked.signatures)

include extension transport faithful observations unique wellFormed issued rebuilt interprets included signatures in
theorem assignment_fault (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (covers : evidence.Covers context) (budget : Nat)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence
        source (certificates context) faults size)) :
    AssignmentFaultPreservesWithPayloadAt callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
      (SourceAssignmentHasType source) (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (ambient := ambient) functions (registry := registry)
      (Program.ofChecked compiled.sourceProgram) evidence source (certificates context) context administrative faults budget
      (fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head) := by
  intro scope assignment operator rhs head typed mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees actualTyped initial admitted payload reason after size trace bounded next output
  have payload' := payload
  cases payload with
  | intro site origin same sourceTyped rightTyped profile fuel prepared =>
    by_cases bare : assignment.target.projections = []
    · exact CallableIndexedOwnedAdmittedPointwiseBareAssignmentHeads.preserves_fault_with_operands
        (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
        bridge functions extension evidence observations head bare environments heaps locals agrees actualTyped initial admitted unique typed
        budget meaning (operand_law issued head origin same included) trace bounded next output
    · exact CallableIndexedOwnedAdmittedPointwiseProjectedAssignmentHeads.preserves_fault_with_diagnostics
        (values := .initial compiled.compatible.checked) (ambient := ambient)
        bridge functions extension evidence transport faithful observations head bare environments heaps locals agrees actualTyped
        initial admitted unique typed wellFormed runtime covers budget meaning
        (issued.shape_errors rebuilt head initial bare origin prepared typed unique signatures
          (interprets head initial admitted payload' bare)) trace bounded next output

include extension transport faithful observations unique wellFormed issued rebuilt interprets included signatures in
theorem assignment_reflection (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (covers : evidence.Covers context) (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence
        source (certificates context) faults size)) :
    AssignmentReflectsWithPayloadAt callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
      (SourceAssignmentHasType source) (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (ambient := ambient) functions (registry := registry)
      (Program.ofChecked compiled.sourceProgram) evidence source (certificates context) context administrative faults budget
      (fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head) := by
  intro scope assignment operator rhs head typed mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees actualTyped initial admitted payload next output value finalStore size evaluated bounded
  have payload' := payload
  have result : CallableIndexedOwnedAdmittedBareAssignmentHeads.ResultAt bridge size compiled.compatible.checked registry functions
      context evidence source faults scope (head.writtenContext actualContext) assignment operator rhs
      environment canonical actual before store mapping world initial (next.rename ξ) output value finalStore := by
    cases payload with
    | intro site origin same sourceTyped rightTyped profile fuel prepared =>
      by_cases bare : assignment.target.projections = []
      · exact CallableIndexedOwnedAdmittedPointwiseBareAssignmentHeads.reflects_with_operands
          (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
          bridge functions extension evidence transport observations head bare environments heaps locals agrees actualTyped initial admitted
          unique typed wellFormed runtime covers budget meaning (operand_law issued head origin same included) evaluated bounded
      · exact CallableIndexedOwnedAdmittedPointwiseProjectedAssignmentHeads.reflects_with_diagnostics
          (values := .initial compiled.compatible.checked) (ambient := ambient)
          bridge functions extension evidence transport faithful observations head bare environments heaps locals agrees actualTyped
          initial admitted unique typed wellFormed runtime covers budget meaning functionTypes
          (issued.shape_errors rebuilt head initial bare origin prepared typed unique signatures
            (interprets head initial admitted payload' bare)) evaluated bounded
  cases result with
  | fault trace same matched heaps maps worlds frame metadata reached related stable =>
    exact .fault trace same matched heaps maps worlds frame metadata ⟨reached, related, stable⟩
  | success trace heaps maps worlds frame metadata count typed reached related admitted smaller remaining =>
    exact .success trace heaps maps worlds frame metadata count typed ⟨reached, related, admitted⟩ smaller remaining

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaAssignmentReadiness
