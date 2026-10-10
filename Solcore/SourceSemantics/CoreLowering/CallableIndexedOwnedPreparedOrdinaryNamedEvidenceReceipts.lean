import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionValues
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallSelectionCertificates

/-! Ordinary selection fixes an empty actual specialization dictionary. The
same Header retains its resolved Row and complete Source dictionary, so these
receipts manufacture the selected empty-evidence condition from compiler
provenance. Other Headers may keep nonempty dictionaries. No body execution
or completed expression Tree is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryNamedEvidenceReceipts
open Core Frontend SourceInference
open RecursiveNamedCatalog CallableIndexedOwnedFunctionValues

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions
    (Program.ofChecked compiled.sourceProgram)}

/-- The actual ordinary selected row and retained resolver fix this Header's
dictionary. Signature/type equality alone does not supply this fact. -/
theorem selected_evidence_empty
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {instantiation : DeclarationInstantiation}
    {index : Nat} {signature : SourceCoreCalls.Signature}
    (plan : compilation.plan = compiled.indexed.base.plan)
    (signatureEq : header.named.signature = signature)
    (selected : SourceCoreFunctions.selectedSignature policy compilation source node instantiation false =
      .ok (index, signature)) :
    header.function.evidence = [] := by
  obtain ⟨actual, record, _matched, closed, _slot⟩ :=
    CallableNamedMetadata.metadata_of_selected_signature selected
  rw [plan, ← signatureEq] at record
  have same : actual = header.named.specialized :=
    Except.ok.inj (record.symm.trans sourceAt.row.record)
  have actualClosed : header.named.specialized.assumptions = [] := same ▸ closed
  have emptyResolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment
      compiled.indexed.base.sourceProgram header.named.signature.key
      header.named.specialized.assumptions = .ok [] := by
    rw [actualClosed]
    rfl
  have rawEmpty : rawD = [] := Except.ok.inj (sourceAt.row.resolved.symm.trans emptyResolved)
  rw [sourceAt.dictionary, sourceAt.retained, rawEmpty]
  rfl

/-- A finite inventory keeps the original full Row, resolver, Source frame and
dictionary identity for each actual Header. This is static provenance. -/
structure SourceReceiptCover : Prop where
  receipts : ∀ header, header ∈ headers →
    ∃ rawD global, NamedSourceAt header rawD global

/-- Construct the existing selected-site condition internally from those real
receipts and the actual ordinary selection. No global emptiness is imposed. -/
theorem SourceReceiptCover.selected_empty
    (cover : SourceReceiptCover (headers := headers))
    (compilation : SourceCoreFunctions.Context)
    (plan : compilation.plan = compiled.indexed.base.plan)
    (source : TypedSource) (admitted : ExpressionId → Prop) :
    RecursiveNamedExpressionCompilerCertificates.SelectedEmptyEvidence headers compilation source admitted := by
  intro _id node _callee _arguments instantiation header policy index signature
    _allowed _found _form selected member _sameInstantiation _sameSlot signatureEq
  obtain ⟨rawD, global, sourceAt⟩ := cover.receipts header member
  exact selected_evidence_empty sourceAt plan signatureEq selected

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryNamedEvidenceReceipts
