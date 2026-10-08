import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedPointwiseBareAssignmentHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedProjectedAssignmentHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalReadiness
import Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderAssignmentPayloadContracts
import Solcore.SourceSemantics.CoreLowering.SourceDiagnosticTyping

/-! The actual public Source and issued table provide operand diagnostics.
The joint assignment packet keeps the same selected preparation. Projected
faults use precise table observations at the actual admitted state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedAssignmentReadiness
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open ProtectedForHeader.Stateful.WithReady
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (receipt : CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds.PublicReceipt header)
  {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
  (functions : FunctionModel compiled.compatible.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  (evidence : Dynamic.EvidenceEnvironment)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (unique : NodeOccurrencesUnique header.function.source)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {context : SourceSemantics.Context}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {administrative : Core.Context} {faults : FunctionCalls.FaultRep}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {factory : AssignmentDiagnosticOrigins.Factory true diagnosticPolicy header.function.source
    (GenericAssignmentDiagnostics.token receipt.original.prepared.compilation.own.assignments)}

/-- The fault interpretation is requested only for a projected packet at its
actual admitted input. It retains the selected head, environment and state. -/
def ReachedInterpretations
    (table : SourceCoreFaultSites.Table) : Prop :=
  ∀ {scope assignment operator rhs}
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) header.function.source
      context (certificates context) scope administrative ambient.definitions assignment operator rhs)
    {environment : Dynamic.Environment} {index : ProtectedStateTransition.Index}
    (initial : callerProtocol.State index), Admission bridge context initial →
    GenericForHeader.Structural.PreparedAssignment factory
      (fun site root => receipt.original.prepared.diagnostics.placeReason header.named.signature.key site root none)
      (fun site root rawValue => receipt.original.prepared.diagnostics.placeReason header.named.signature.key site root (some rawValue)) head →
    assignment.target.projections ≠ [] →
    CallableIndexedOwnedPublicPreparedShapeDiagnostics.ReachedTableInterpretation
      compiled.compatible.checked registry functions callerProtocol environment assignment.target head.prepared initial table faults

include wellFormed in
private theorem operand_law {scope assignment operator rhs}
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) header.function.source
      context (certificates context) scope administrative ambient.definitions assignment operator rhs)
    {site : SourceCoreElaboration.ErrorSite}
    (origin : AssignmentDiagnosticOrigins.Occurs header.function.source site assignment operator rhs)
    (same : head.invalid = GenericAssignmentDiagnostics.token receipt.original.prepared.compilation.own.assignments site assignment.target.root operator)
    (included : ∀ reason token, GenericAssignmentDiagnostics.OperandRep receipt.original.prepared.compilation.own.assignments reason token → faults reason token) :
    AssignmentOperandDiagnostics.OperandsLaw faults operator head.invalid := by
  obtain ⟨first, issued⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.assignments_at_header
    receipt.original.prepared receipt.diagnostic receipt.original.aligned
  exact same.symm ▸ origin.prepared (SourceDiagnosticTyping.header_diagnostic_typed header wellFormed).2 issued included

variable {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
  (diagnosticsFound : compiled.indexed.base.diagnostics = some diagnostics)
  {table : SourceCoreFaultSites.Table} (rebuilt : diagnostics.tableForRegistry registry extension = .ok table)
  (interprets : ReachedInterpretations header bridge receipt functions table)
  (included : ∀ reason token, GenericAssignmentDiagnostics.OperandRep receipt.original.prepared.compilation.own.assignments reason token → faults reason token)
  (signatures : context.signatures = compiled.compatible.checked.signatures)

include extension transport faithful observations unique wellFormed receipt diagnosticsFound rebuilt interprets included signatures in
theorem assignment_fault (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context header.function.source)
    (covers : evidence.Covers context) (budget : Nat)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence
        header.function.source (certificates context) faults size)) :
    AssignmentFaultPreservesWithPayloadAt callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
      (SourceAssignmentHasType header.function.source) (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (ambient := ambient) functions (registry := registry)
      (Program.ofChecked compiled.sourceProgram) evidence header.function.source (certificates context) context administrative faults budget
      (fun head => GenericForHeader.Structural.PreparedAssignment factory
        (fun site root => receipt.original.prepared.diagnostics.placeReason header.named.signature.key site root none)
        (fun site root rawValue => receipt.original.prepared.diagnostics.placeReason header.named.signature.key site root (some rawValue)) head) := by
  intro scope assignment operator rhs head typed mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees actualTyped initial admitted payload reason after size trace bounded next output
  have payload' := payload
  cases payload with
  | intro site origin same sourceTyped rightTyped profile fuel prepared =>
    by_cases bare : assignment.target.projections = []
    · exact CallableIndexedOwnedAdmittedPointwiseBareAssignmentHeads.preserves_fault_with_operands
        (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
        bridge functions extension evidence observations head bare environments heaps locals agrees actualTyped initial admitted unique typed
        budget meaning (operand_law header receipt wellFormed head origin same included) trace bounded next output
    · exact CallableIndexedOwnedPublicPreparedProjectedAssignmentHeads.preserves_fault header bridge functions extension evidence transport
        faithful observations head bare environments heaps locals agrees actualTyped initial admitted unique typed wellFormed runtime covers
        receipt diagnosticsFound origin prepared signatures rebuilt (interprets head initial admitted payload' bare)
        budget meaning trace bounded next output

include extension transport faithful observations unique wellFormed receipt diagnosticsFound rebuilt interprets included signatures in
theorem assignment_reflection (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context header.function.source)
    (covers : evidence.Covers context) (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence
        header.function.source (certificates context) faults size)) :
    AssignmentReflectsWithPayloadAt callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
      (SourceAssignmentHasType header.function.source) (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (ambient := ambient) functions (registry := registry)
      (Program.ofChecked compiled.sourceProgram) evidence header.function.source (certificates context) context administrative faults budget
      (fun head => GenericForHeader.Structural.PreparedAssignment factory
        (fun site root => receipt.original.prepared.diagnostics.placeReason header.named.signature.key site root none)
        (fun site root rawValue => receipt.original.prepared.diagnostics.placeReason header.named.signature.key site root (some rawValue)) head) := by
  intro scope assignment operator rhs head typed mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees actualTyped initial admitted payload next output value finalStore size evaluated bounded
  have payload' := payload
  have result : CallableIndexedOwnedAdmittedBareAssignmentHeads.ResultAt bridge size compiled.compatible.checked registry functions
      context evidence header.function.source faults scope (head.writtenContext actualContext) assignment operator rhs
      environment canonical actual before store mapping world initial (next.rename ξ) output value finalStore := by
    cases payload with
    | intro site origin same sourceTyped rightTyped profile fuel prepared =>
      by_cases bare : assignment.target.projections = []
      · exact CallableIndexedOwnedAdmittedPointwiseBareAssignmentHeads.reflects_with_operands
          (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
          bridge functions extension evidence transport observations head bare environments heaps locals agrees actualTyped initial admitted
          unique typed wellFormed runtime covers budget meaning (operand_law header receipt wellFormed head origin same included) evaluated bounded
      · exact CallableIndexedOwnedPublicPreparedProjectedAssignmentHeads.reflects header bridge functions extension evidence transport
          faithful observations head bare environments heaps locals agrees actualTyped initial admitted unique typed wellFormed runtime covers
          receipt diagnosticsFound origin prepared signatures rebuilt (interprets head initial admitted payload' bare)
          budget meaning functionTypes evaluated bounded
  cases result with
  | fault trace same matched heaps maps worlds frame metadata reached related stable =>
    exact .fault trace same matched heaps maps worlds frame metadata ⟨reached, related, stable⟩
  | success trace heaps maps worlds frame metadata count typed reached related admitted smaller remaining =>
    exact .success trace heaps maps worlds frame metadata count typed ⟨reached, related, admitted⟩ smaller remaining

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedAssignmentReadiness
