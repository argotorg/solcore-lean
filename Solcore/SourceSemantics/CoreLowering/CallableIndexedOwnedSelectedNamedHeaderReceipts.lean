import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedReadIndexDiagnosticPolicies
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaders

/-! A named Header is constructed with the actual selected diagnostic issuer.
The public specialization retains its original Source, resolved dictionary and
substitution order. The second-pass action supplies the fresh compiler packet;
equality of cached native code is never used to identify diagnostic tables.
These static factories do not supply a body execution law or a runtime pool. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedNamedHeaderReceipts
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedSelectedDiagnosticIssuerReceipts
open CallableIndexedOwnedSelectedReadIndexDiagnosticPolicies
open RecursiveNamedPublicSpecializationMeaning

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}

/-- Whole original body typing supplies the issuer's assignment and unary
certificates, including nested bodies and statically typed suffixes. -/
theorem diagnostic_typed (prepared : Prepared compiled row)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution) :
    EmittedDiagnosticTokenPlan.UnaryTyped (source prepared.named) ∧
      AssignmentDiagnosticOrigins.OperandsTyped (source prepared.named) := by
  obtain ⟨types, context, facts, certificate⟩ :=
    (prepared.instantiated wellFormed range).certificate wellFormed
  have typed := SourceDiagnosticTyping.diagnostic_typed_of_certificate certificate.toBodyInstanceTypingCertificate
  change EmittedDiagnosticTokenPlan.UnaryTyped row.function.typedBody ∧
    AssignmentDiagnosticOrigins.OperandsTyped row.function.typedBody at typed
  simpa only [source, prepared.same] using typed

/-- Reuse the real worklist origin and complete resolved evidence. Replace
only the compiler fields with the actual selected second-pass packet. -/
def reissued (prepared : Prepared compiled row)
    (selected : SelectedReceipt compiled prepared.named prepared.index) : Prepared compiled row :=
  { prepared with
    diagnostics := lowered compiled selected.diagnostics
    code := selected.code
    compilation := selected.compilation
    cached := selected.cached }

/-- Both genuine compiler actions extract the same complete statement roots.
The source closure, including its ordered dictionary, is therefore unchanged. -/
theorem reissued_view (prepared : Prepared compiled row)
    (selected : SelectedReceipt compiled prepared.named prepared.index) :
    (reissued prepared selected).view = prepared.view := by
  have roots : selected.compilation.statements = prepared.compilation.statements :=
    Except.ok.inj (selected.compilation.roots.symm.trans prepared.compilation.roots)
  simp only [RecursiveNamedPublicSpecializationMeaning.Prepared.view,
    RecursiveNamedPreparedSourceFrames.view, reissued, roots]

/-- This is an observation of the fresh Header factory's actual policy.
The desired identifier equality is obtained from HeaderAt, not supplied. -/
theorem reason_at (prepared : Prepared compiled row)
    (selected : SelectedReceipt compiled prepared.named prepared.index)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header compiled
      (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt
      (reissued prepared selected) instantiation header) :
    header.reasonAt = reasonAt selected := by
  simpa only [reissued, reasonAt] using aligned.reasonAt

/-- Canonical source metadata uses a freshly selected issuer and the original
evidence-aware Header construction. No synthetic Header or empty dictionary
is inferred from the cached slot. -/
theorem canonical_at_prepared (prepared : Prepared compiled row)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok prepared.named.signature.key) :
    ∃ (selected : SelectedReceipt compiled prepared.named prepared.index)
      (header : CallableIndexedOwnedFunctionValues.Header compiled
        (Program.ofChecked compiled.sourceProgram)),
      RecursiveNamedPreparedHeaders.Prepared.HeaderAt (reissued prepared selected)
        (CallableNamedMetadata.instantiation row) header ∧
      header.function = prepared.view ∧ header.reasonAt = reasonAt selected := by
  obtain ⟨selected⟩ := at_selected prepared.selected (diagnostic_typed prepared wellFormed range)
  obtain ⟨header, aligned⟩ :=
    RecursiveNamedPreparedHeaders.Prepared.canonical_header_with_evidence
      (reissued prepared selected) wellFormed range ordinaryReturn ordinaryParameters target
  exact ⟨selected, header, aligned, aligned.function.trans (reissued_view prepared selected),
    reason_at prepared selected aligned⟩

/-- Retained metadata keeps the original reversed substitution order and
complete resolved dictionary, with the same authentic selected issuer. -/
theorem retained_at_prepared (prepared : Prepared compiled row)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok prepared.named.signature.key) :
    ∃ (selected : SelectedReceipt compiled prepared.named prepared.index)
      (header : CallableIndexedOwnedFunctionValues.Header compiled
        (Program.ofChecked compiled.sourceProgram)),
      RecursiveNamedPreparedHeaders.Prepared.HeaderAt (reissued prepared selected)
        (CallableNamedCanonicalOrder.retainedInstantiation row) header ∧
      header.function = prepared.view ∧ header.reasonAt = reasonAt selected := by
  obtain ⟨selected⟩ := at_selected prepared.selected (diagnostic_typed prepared wellFormed range)
  obtain ⟨header, aligned⟩ :=
    RecursiveNamedPreparedHeaders.Prepared.retained_header_with_evidence
      (reissued prepared selected) wellFormed range ordinaryReturn ordinaryParameters target
  exact ⟨selected, header, aligned, aligned.function.trans (reissued_view prepared selected),
    reason_at prepared selected aligned⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedNamedHeaderReceipts
