import Solcore.SourceSemantics.CoreLowering.SourceDiagnosticTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipal
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodySourceAdmission

/-! Actual operator selection supplies full independent Source body typing and
graph closure. Diagnostic typing follows that real method authority and cached
Source identity; no ordinary Header is inferred from the synthetic function. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SourceDiagnosticTypingOrigins
open Core Frontend SourceInference

variable {program : Program} {body : Dynamic.BodyInstance}
  {context : SourceSemantics.Context} {evidence dictionary : Dynamic.EvidenceEnvironment}
  {traitName methodName : String} {requirements : List RequirementId}

/-- The complete actual method selector produces its own original body
certificate, including all retained Source occurrences. -/
theorem selected_method
    (selected : Dynamic.OperatorMethodSelected program context evidence traitName methodName requirements body dictionary)
    (wellFormed : ProgramWellFormed program) :
    EmittedDiagnosticTokenPlan.UnaryTyped body.source ∧ AssignmentDiagnosticOrigins.OperandsTyped body.source := by
  obtain ⟨types, lexicalContext, facts, certificate, _validity⟩ :=
    CallablePreparedMethodSelection.selected_typed selected wellFormed
  exact SourceDiagnosticTyping.diagnostic_typed_of_certificate certificate

/-- The authentic frame keeps the selected Source at the actual method
closure; dictionary and capture fields remain those of that same frame. -/
theorem method_frame {function : Dynamic.Closure}
    (selected : Dynamic.OperatorMethodSelected program context evidence traitName methodName requirements body dictionary)
    (frame : CallableCoercionMethodFrame.Frame body function)
    (wellFormed : ProgramWellFormed program) :
    EmittedDiagnosticTokenPlan.UnaryTyped function.source ∧ AssignmentDiagnosticOrigins.OperandsTyped function.source := by
  simpa only [frame.source] using selected_method selected wellFormed

/-- The full cached specialization identifies the method principal's exact
compiler Source. Its independent trait selector supplies diagnostic typing. -/
theorem principal {compiled : SourceCoreUnifiedCompilation.Compiled}
    {method : ExecutableImplMethods.CheckedMethod}
    (selected : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    EmittedDiagnosticTokenPlan.UnaryTyped (CallableIndexedNamedGeneration.source selected.named) ∧
    AssignmentDiagnosticOrigins.OperandsTyped (CallableIndexedNamedGeneration.source selected.named) := by
  simpa only [selected.source_eq] using selected_method selected.selected wellFormed

end Solcore.SourceSemantics.CoreLowering.SourceDiagnosticTypingOrigins
