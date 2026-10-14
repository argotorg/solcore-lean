import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSourceTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectNamedProfileExtraction

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderFacts
open Core Frontend SourceInference
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}

theorem scoped_ledger (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    ScopedRequirementLedgerWellFormed header.context header.function.source := by
  obtain ⟨_, certificate⟩ := certified
  have original : ScopedRequirementLedgerWellFormed header.function.context header.function.source := by
    simpa only [header.frame.context, header.frame.source] using certificate.requirement_ledger
  exact (RecursiveNamedInitialContextValidity.mono_fields header.extended).scopedRequirementLedger original

theorem runtime_ledger (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    RuntimeRequirementLedgerValid header.context := (scoped_ledger certified).toRuntime

theorem hidden_fresh (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    GenericImperativeMatch.MatchHiddenFresh header.function.source := by
  obtain ⟨_, certificate⟩ := certified
  apply CallableIndexedOwnedLocalIdentityFreshness.match_hidden_fresh
  rw [header.frame.source]
  exact certificate.local_identity_ownership

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderFacts
