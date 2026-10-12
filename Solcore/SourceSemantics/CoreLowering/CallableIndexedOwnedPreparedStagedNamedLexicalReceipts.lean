import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionValues
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalTree

/-! The lexical alternative retains the accepted statement action and exact
body footer of one authentic named Header. This receipt has no semantic
children, Source trace, execution law or completed result. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalReceipts
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CompatibleEncoding (bind_ok)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

def parameterScope (header : Header compiled (Program.ofChecked compiled.sourceProgram)) : SourceCoreLocalCell.Scope :=
  header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))

structure Receipt (header : Header compiled (Program.ofChecked compiled.sourceProgram)) where
  flow : Expr
  accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
    (parameterScope header) header.function.body header.output header.reasonAt true header.escaped = .ok flow
  emitted : header.body = CompatibleStatements.finish header.output flow header.fellThrough header.escaped
  shape : CallableIndexedOwnedPreparedStagedLexicalTree.Shape header.function.source header.function.body
  projection : compiled.compatible.checked.catalog.project header.function.resultType = .ok header.output

/-- Inversion uses the one accepted Header body action, preserving its actual
flow code and diagnostic words. -/
theorem of_accepted {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (parameterScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped =
        .ok header.body)
    (shape : CallableIndexedOwnedPreparedStagedLexicalTree.Shape header.function.source header.function.body)
    (projection : compiled.compatible.checked.catalog.project header.function.resultType = .ok header.output) :
    Nonempty (Receipt header) := by
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, returned⟩ := bind_ok accepted
  exact ⟨⟨flow, generated, (Except.ok.inj returned).symm, shape, projection⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalReceipts
