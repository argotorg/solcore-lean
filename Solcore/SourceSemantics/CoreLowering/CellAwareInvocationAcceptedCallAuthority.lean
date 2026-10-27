import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallExpressions

/-! Call authority of a named row's direct calls from a complete inventory. A
direct-call receipt selects a physical global slot; the indexed globals are
the signatures of the indexed functions, and a complete inventory issues a
header for every function index. `of_inventory_at` then supplies the `Port`. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallAuthority
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CellAwareInvocationAcceptedNamedInvocation (rowIndex)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {inputs : List (Input whole)}
  (rows : Inventory inputs)
  (complete : ∀ {index : Nat} {function : SourceCoreGeneralFunctions.Function},
    whole.indexed.base.functions[index]? = some function →
    ∃ input ∈ inputs, input.prepared.index = index ∧ input.prepared.named = function)
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics code)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key =
    .ok named.specialized)

include complete in
/-- Every direct-call receipt of a named row's compiler selects a header of a
complete inventory. -/
theorem ports : CellAwareInvocationAcceptedCallExpressions.Ports (headers := headers rows) generation record := by
  intro rootFuel fuel scope callId callee ids instantiation callCode receipt
  have global : whole.indexed.base.globals[receipt.index]? = some receipt.signature := receipt.global
  rw [CallableIndexedPreparedInventories.cached_globals whole, List.getElem?_map, Option.map_eq_some_iff] at global
  obtain ⟨function, functionFound, signatureEq⟩ := global
  obtain ⟨input, member, slot, namedEq⟩ := complete functionFound
  obtain ⟨issued, retained⟩ := rows.row_at input member
  exact CallableIndexedOwnedPreparedStagedDirectCallAuthority.of_inventory_at receipt rows
    ⟨issued.header, CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory.header_member retained,
      issued.aligned.slot.trans slot,
      (congrArg (·.signature) issued.aligned.named).trans ((congrArg (·.signature) namedEq).trans signatureEq)⟩
    rfl

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallAuthority
