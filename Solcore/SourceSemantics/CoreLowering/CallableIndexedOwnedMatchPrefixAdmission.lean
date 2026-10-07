import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMatchAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalReadiness
import Solcore.SourceSemantics.CoreLowering.ProtectedStateScopeReturn

/-! A selected match prefix has one actual protocol post. Genuine Source
hidden and pattern allocations establish its heap typing without an
intermediate protocol state. Lexical restoration retains the actual body post. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMatchPrefixAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

/-- Compose the real Source allocations at the single reached selection
state. The independent case judgment supplies the raw binding types and body. -/
theorem after_arm_prefix {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    {source : TypedSource} {context armContext : SourceSemantics.Context}
    {control : ControlContext} {resolution : MatchResolution} {type : TypeSystem.Ty}
    {caseFacts : List BodyFacts} {value : Dynamic.Value} {hidden : Dynamic.Heap}
    {location : Dynamic.Location} {body : List StatementId}
    {bindings : List (TypedBinder × Dynamic.Value)}
    {environment armEnvironment : Dynamic.Environment}
    (admitted : Admission bridge context first)
    (valueTyped : Dynamic.ValueHasType context initial.heap value type)
    (hiddenAllocated : Dynamic.Heap.Allocates initial.heap type (some value) location hidden)
    (casesTyped : MatchCasesHaveType source control context type resolution.cases caseFacts)
    (selected : Dynamic.MatchCasesSelect context value resolution.cases resolution.defaultBody (.arm body bindings))
    (extended : BindersExtend source.owner context (bindings.map Prod.fst) armContext)
    (allocated : Dynamic.BindersAllocate environment hidden (bindings.map Prod.fst)
      (bindings.map Prod.snd) armEnvironment reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    Admission bridge armContext last ∧
      ∃ final facts, StatementsHaveType source control armContext body final facts := by
  obtain ⟨binders, staticContext, final, facts, valuesTyped, bindersEq,
    staticExtended, bodyTyped, _member, _monomorphic⟩ :=
    Dynamic.MatchCasesSelect.arm_preserves_typing casesTyped valueTyped selected
  have actualExtended : BindersExtend source.owner context (bindings.map Prod.fst) staticContext := by
    rw [bindersEq]
    exact staticExtended
  have contextEq := Dynamic.BindersExtend.functional actualExtended extended
  have hiddenHeap := admitted.heap.allocate (.some valueTyped) hiddenAllocated
  have hiddenValues := valuesTyped.mono (Dynamic.HeapTypesExtend.of_allocation hiddenAllocated)
  have actualValues : Dynamic.ValuesHaveTypes context hidden (bindings.map Prod.snd)
      ((bindings.map Prod.fst).map fun binder => binder.scheme.body) := by
    simpa only [List.map_map, Function.comp_def] using hiddenValues.unzip
  have heapTyped := Dynamic.BindersAllocate.preservesHeapTyping hiddenHeap actualValues allocated
  exact ⟨⟨Dynamic.BindersExtend.control_heap_forward extended heapTyped,
    StableRows.after_administrative (bridge.pool first) (bridge.pool last) admitted.rows frame⟩,
    contextEq ▸ ⟨final, facts, bodyTyped⟩⟩

/-- Real static binder extension removes only the body's local Source
context. The actual returned state's heap, store and rows remain observable. -/
theorem restore_arm {source : TypedSource}
    {scope selectedScope : SourceCoreLocalCell.Scope} {canonical selectedCanonical : Environment}
    (returnTo : ProtectedStateTransition.ReturnTo callerProtocol scope canonical selectedScope selectedCanonical)
    {context armContext : SourceSemantics.Context} {binders : List TypedBinder}
    (extended : BindersExtend source.owner context binders armContext)
    {mapping world heap store}
    (state : callerProtocol.State ⟨selectedScope, mapping, world, heap, store, selectedCanonical⟩)
    (admitted : Admission bridge armContext state) :
    Admission bridge context (returnTo.restore state) :=
  ⟨Dynamic.BindersExtend.control_heap_backward extended admitted.heap,
    StableRows.after_administrative (bridge.pool state) (bridge.pool (returnTo.restore state))
      admitted.rows (.refl _ _)⟩

/-- Default and empty selection retain their original Source context at
the exact restored state. Administrative preservation authenticates rows only. -/
theorem restore_parent
    {scope selectedScope : SourceCoreLocalCell.Scope} {canonical selectedCanonical : Environment}
    (returnTo : ProtectedStateTransition.ReturnTo callerProtocol scope canonical selectedScope selectedCanonical)
    {context : SourceSemantics.Context} {mapping world heap store}
    (state : callerProtocol.State ⟨selectedScope, mapping, world, heap, store, selectedCanonical⟩)
    (admitted : Admission bridge context state) :
    Admission bridge context (returnTo.restore state) :=
  ⟨admitted.heap,
    StableRows.after_administrative (bridge.pool state) (bridge.pool (returnTo.restore state))
      admitted.rows (.refl _ _)⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMatchPrefixAdmission
