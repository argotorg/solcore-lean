import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodyPorts

/-! Existing terminal receipts supply the general named body ports. The
adapter makes their unchanged Source context explicit; lexical body receipts
can supply a different final context through the same invocation interface. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedBodyPorts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header OwnedKey)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)} {expression : ExpressionId}
variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
  (selected : stages.Closure header.function child)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Receipt header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body)
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  (certifies : ∀ lowered,
    header.policy.lowerExpression terminal.childFuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression header.reasonAt = .ok lowered →
    certificate (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression lowered)


include selected wellFormed terminal certifies in
theorem preserves (budget : Nat)
    (children : CallableIndexedOwnedPreparedStagedNamedChildBounds.PreservesBelow
      (headers := headers) (keys := keys) header model stages child certificate faults budget) :
    CallableIndexedOwnedPreparedStagedNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header model stages child faults budget := by
  intro mapping world administrative actualContext environment canonical actual before store ξ
    environments heaps locals agrees typed initial admitted owner packet size finalContext bodyOutcome
    outcome after trace matched within
  exact CallableIndexedOwnedPreparedStagedNamedChildBounds.preserves_body
    selected wellFormed terminal certifies environments heaps locals agrees typed initial admitted owner packet
    budget children trace matched within

include selected wellFormed terminal certifies in
theorem reflects (budget : Nat)
    (children : CallableIndexedOwnedPreparedStagedNamedChildBounds.ReflectsBelow
      (headers := headers) (keys := keys) header model stages child certificate faults budget) :
    CallableIndexedOwnedPreparedStagedNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header model stages child faults budget := by
  intro mapping world administrative actualContext environment canonical actual before store ξ
    environments heaps locals agrees typed initial admitted owner packet size value finalStore completed within
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, matched, result⟩ :=
    CallableIndexedOwnedPreparedStagedNamedChildBounds.reflects_body
      selected wellFormed terminal certifies environments heaps locals agrees typed initial admitted owner packet
      budget children completed within
  exact ⟨sourceSize, header.context, _, outcome, after, finalMap, finalWorld, trace, matched, result⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedBodyPorts
