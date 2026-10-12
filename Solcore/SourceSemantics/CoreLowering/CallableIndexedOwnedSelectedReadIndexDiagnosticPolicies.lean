import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedDiagnosticIssuerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDecodedAssignmentFaults
import Solcore.SourceSemantics.CoreLowering.CompatiblePublicContextualDiagnosticObservations
import Solcore.SourceSemantics.CoreLowering.CompatiblePublicContextualMissingDiagnosticObservations
import Solcore.SourceSemantics.CoreLowering.IndexFaultPostContracts

/-! Actual selected compilation and the literal receiving table construct the
read and mapping-index policies. Each read uses its real Source binder. Each
unavailable index uses the raw mapping metadata and runtime views retained by
its own missing witness. No unrelated token or registered mapping type is
required to decode as this occurrence's error. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedReadIndexDiagnosticPolicies
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open CallableIndexedNamedGeneration
open CallableIndexedOwnedSelectedDiagnosticIssuerReceipts
open CallableIndexedOwnedPublicDecodedAssignmentFaults
open CallableIndexedOwnedPublicFaultReceiverTables

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named} {index : Nat}
  (selected : SelectedReceipt compiled named index)

/-- The actual selected compiler uses this issuer for its expression tokens. -/
def reasonAt : ExpressionId → Word :=
  (lowered compiled selected.diagnostics).reasonAt named.signature.key

/-- Replacing the callable receiver's root table retains expression issuance. -/
theorem reason_eq (id : ExpressionId) :
    reasonAt selected id = selected.diagnostics.program.reasonAt named.signature.key id := by
  unfold reasonAt lowered
  cases compiled.indexed.base.callableContext <;> rfl

/-- The lookup follows from the retained named compilation itself. -/
theorem own_found : selected.diagnostics.program.base.find? named.signature.key =
    some selected.compilation.own := by
  have found := selected.compilation.diagnostic
  change (lowered compiled selected.diagnostics).base.find? named.signature.key =
    some selected.compilation.own at found
  have sameBase : (lowered compiled selected.diagnostics).base =
      selected.diagnostics.program.base := by
    unfold lowered
    cases compiled.indexed.base.callableContext <;> rfl
  rw [sameBase] at found
  exact found

/-- The real public read row constructs inclusion only at a certified local
read and its actual current uninitialized cell. -/
theorem reads {fuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {context : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique (source named))
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics) :
    ReachedLoweredReadOutcomePorts.ReadPolicies fuel values (source named) context
      (reasonAt selected) (faults completion.result.diagnostics) := by
  intro scope id code certificate binding environment heap location cell witness
  obtain ⟨read, _expression, _binder, _span, token, _member, decoded⟩ :=
    CompatiblePublicContextualDiagnosticObservations.receiver_local_read_diagnostic compiled receiver
      selected.found selected.record unique witness.contains witness.localReference (own_found selected)
  apply of_decoded (diagnostic := {
    error := .uninitializedLocal certificate.binder
    site := .occurrence id.occurrence
    span := some certificate.node.span })
  · simpa only [reason_eq selected id, ← token] using decoded
  · exact .readUninitialized location certificate.binder

/-- The exact unavailable mapping supplies its real canonical raw view and
receiving metadata, so the first matching public row is derived internally. -/
theorem missing {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (unique : NodeOccurrencesUnique (source named))
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics) :
    IndexFaultPostContracts.MissingPolicies values (source named) functions
      completion.result.context.registry program context evidence (reasonAt selected)
      (faults completion.result.diagnostics) := by
  intro id base key node baseNode keyNode layout comparison first second header
    mapping world baseSource keySource baseValue environment before middle heap
    keyFound form baseTrace keyTrace rawKey rawValue sources tag entries fallback witness
  have contains : ContainsExpression (source named) node.id node := by
    rw [witness.contains.2]
    exact witness.contains
  have view : CompatiblePublicContextualMissingDiagnosticObservations.CanonicalMappingView
      (source named) base rawKey rawValue := by
    refine ⟨baseNode, lookupExpression?_complete unique witness.baseContains, ?_⟩
    rw [witness.sourceType, SourceCoreRawMetadata.runtimeType, witness.keyView, witness.valueView]
  have decoded :=
    CompatiblePublicContextualMissingDiagnosticObservations.receiver_index_missing_diagnostic
      compiled receiver selected.found selected.record unique contains form view witness.fields.metadata
  apply of_decoded (diagnostic := {
    error := .typeMismatch rawValue none
    site := .occurrence id.occurrence
    span := some node.span })
  · simpa only [witness.contains.2, reason_eq selected id] using decoded
  · exact .missing rawValue

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedReadIndexDiagnosticPolicies
