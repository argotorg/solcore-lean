import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDecodedCallFaults
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReceivingFirstCallGateRejection

/-! One literal public diagnostic table interprets semantic assignment/arity
failures and scoped first-call-gate failures. The failure constructor chooses
the view; an equal raw runtime error never changes the original failure tag.
These adapters retain the same payload model, value and reached indices. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDecodedStagedCallFaults
open Core Frontend SourceInference GeneralHeap CompatiblePayload

def faults (table : SourceCoreFaultSites.Table) : RecursiveStageMeaning.FaultRep :=
  fun failure token => match failure with
    | .semantic reason => CallableIndexedOwnedPublicDecodedCallFaults.faults table reason token
    | .stage invocation call reason =>
        CallableIndexedOwnedPreparedReceivingFirstCallGateRejection.stagedFaults table
          (.stage invocation call reason) token

/-- A semantic producer keeps its original tag at this exact public table. -/
theorem of_semantic {table : SourceCoreFaultSites.Table}
    {failure : Staging.Recursive.Failure} {token : Word}
    (represented : CallableIndexedOwnedPublicDecodedCallFaults.stagedSemanticFaults table failure token) :
    faults table failure token := by
  cases failure with
  | semantic reason => exact represented
  | stage invocation call reason => exact False.elim represented

/-- A scoped first-gate producer retains the failing invocation and call. -/
theorem of_first_gate {table : SourceCoreFaultSites.Table}
    {failure : Staging.Recursive.Failure} {token : Word}
    (represented : CallableIndexedOwnedPreparedReceivingFirstCallGateRejection.stagedFaults table failure token) :
    faults table failure token := by
  cases failure with
  | semantic reason => exact False.elim represented
  | stage invocation call reason => exact represented

theorem of_assignment {table : SourceCoreFaultSites.Table} {reason : Dynamic.SemanticFault}
    {token : Word}
    (represented : CallableIndexedOwnedPublicDecodedAssignmentFaults.faults table reason token) :
    faults table (.semantic reason) token :=
  CallableIndexedOwnedPublicDecodedCallFaults.of_assignment represented

theorem of_arity {table : SourceCoreFaultSites.Table} {failure : Staging.Recursive.Failure}
    {token : Word}
    (represented : CallableIndexedOwnedPreparedSecondCallGateRejection.stagedArityFaults table failure token) :
    faults table failure token :=
  of_semantic (CallableIndexedOwnedPublicDecodedCallFaults.of_staged_arity represented)

/-- Every interpretation still supplies the literal decoder equation. -/
theorem decoded {table : SourceCoreFaultSites.Table} {failure : Staging.Recursive.Failure}
    {token : Word} (represented : faults table failure token) :
    ∃ diagnostic, table.diagnostic? token = some diagnostic := by
  cases failure with
  | semantic reason =>
    obtain ⟨diagnostic, lookup, _view⟩ := represented
    exact ⟨diagnostic, lookup⟩
  | stage invocation call reason =>
    obtain ⟨diagnostic, lookup, _view⟩ := represented
    exact ⟨diagnostic, lookup⟩

section Results
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
  {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty} {type : Ty}
  {table : SourceCoreFaultSites.Table} {outcome : Staging.Recursive.Outcome} {value : Value}

theorem semantic_result
    (represented : RecursiveStageMeaning.ResultRepresentsFor model mapping world sourceType type
      (CallableIndexedOwnedPublicDecodedCallFaults.stagedSemanticFaults table) outcome value) :
    RecursiveStageMeaning.ResultRepresentsFor model mapping world sourceType type (faults table) outcome value := by
  cases represented with
  | value payload => exact .value payload
  | fault matched => exact .fault (of_semantic matched)

theorem first_gate_result
    (represented : RecursiveStageMeaning.ResultRepresentsFor model mapping world sourceType type
      (CallableIndexedOwnedPreparedReceivingFirstCallGateRejection.stagedFaults table) outcome value) :
    RecursiveStageMeaning.ResultRepresentsFor model mapping world sourceType type (faults table) outcome value := by
  cases represented with
  | value payload => exact .value payload
  | fault matched => exact .fault (of_first_gate matched)

theorem arity_result
    (represented : RecursiveStageMeaning.ResultRepresentsFor model mapping world sourceType type
      (CallableIndexedOwnedPreparedSecondCallGateRejection.stagedArityFaults table) outcome value) :
    RecursiveStageMeaning.ResultRepresentsFor model mapping world sourceType type (faults table) outcome value := by
  cases represented with
  | value payload => exact .value payload
  | fault matched => exact .fault (of_arity matched)

end Results
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDecodedStagedCallFaults
