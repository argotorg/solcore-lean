import Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedPrimitiveMethods

/-! Successful flat inspection retains every original node, even before
occurrence uniqueness has been derived from checking. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPrimitiveMethodNodeFacts
open Frontend SourceInference
open SelectedCompilationAcceptedPrimitiveMethods

theorem nodes_of_accepted {source : TypedSource} {receipt : PLift (Forms source)}
    (accepted : forms? source = some receipt) :
    ∀ node ∈ source.nodes, ∀ expression, node = .expression expression → Form expression.form := by
  unfold forms? at accepted
  simp only [bind, Option.bind] at accepted
  split at accepted
  next => contradiction
  next facts selected => exact facts.down

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPrimitiveMethodNodeFacts
