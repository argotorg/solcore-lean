import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBranchingReceipts

/-! A named body's static coverage retains the actual prepared Header and its
accepted compiler action. Terminal, lexical and branching statement receipts
share named entry, application and caller restoration. Branching receipts can
select canonical recursive expression support at the same original body. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodies
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

inductive Compilation (header : Header compiled (Program.ofChecked compiled.sourceProgram)) where
  | terminal (expression : ExpressionId)
      (receipt : Receipt header.policy header.fuel header.function.source
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body)
      (certificate : GenericExpressionMeaning.Certificate)
      (certifies : ∀ child,
        header.policy.lowerExpression receipt.childFuel header.function.source
          (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression header.reasonAt = .ok child →
        certificate (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression child)
  | lexical (receipt : CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.Receipt header)
  | branching (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt header)
  | canonicalBranching (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt header)

structure Body (header : Header compiled (Program.ofChecked compiled.sourceProgram)) where
  row : SourceSpecialization.SpecializedFunction
  prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row
  instantiation : DeclarationInstantiation
  aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header
  layouts : header.layouts = compiled.indexed.layouts
  compilation : Compilation header

/-- Existing accepted terminal bodies retain their exact original receipt. -/
def of_terminal {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal header) : Body header :=
  ⟨terminal.row, terminal.prepared, terminal.instantiation, terminal.aligned, terminal.layouts,
    .terminal terminal.expression terminal.receipt terminal.certificate terminal.certifies⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodies
