import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeTypedSourceSites
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission
import Solcore.SourceSemantics.Dynamic.PatternCompletenessProperties

/-! Original match typing and actual Source allocations establish admission at
the reached hidden-scrutinee and selected-arm states. Pattern bindings come from
Source selection and typing. Administrative effects separately retain all rows
of the actual pool; native representation types supply no Source declarations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMatchAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)

def Typing (source : TypedSource) (context : SourceSemantics.Context)
    (resolution : MatchResolution) : Prop :=
  ∃ control type caseFacts,
    ExpressionHasType source context resolution.scrutinee type ∧
    MatchCasesHaveType source control context type resolution.cases caseFacts ∧
    ∀ body, resolution.defaultBody = some body →
      ∃ final facts, StatementsHaveType source control context body final facts

/-- The real statement judgment supplies the original scrutinee, case and
default typings at the actual lookup; the compiler syntax stays independent. -/
theorem typing_of_head {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {node : StatementNode} {resolution : MatchResolution}
    (unique : NodeOccurrencesUnique source)
    (typed : ProtectedStateImperativeTypedSourceSites.Head source context id)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution) : Typing source context resolution := by
  obtain ⟨control, final, facts, typed⟩ := typed
  obtain ⟨original, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping typed
  have same : original = node :=
    Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  subst original
  rw [form] at formTyped
  cases formTyped with
  | matchWithoutDefault defaultEq scrutinee casesTyped =>
    refine ⟨control, _, _, scrutinee, casesTyped, ?_⟩
    intro body present
    simp [defaultEq] at present
  | matchWithDefault defaultEq scrutinee casesTyped defaultTyped =>
    refine ⟨control, _, _, scrutinee, casesTyped, ?_⟩
    intro body present
    have equal := Option.some.inj (defaultEq.symm.trans present)
    subst body
    exact ⟨_, _, defaultTyped⟩

/-- A selected default keeps the parent Source context and its original body
typing. An absent default cannot satisfy this actual selection receipt. -/
theorem default_typed {source : TypedSource} {context : SourceSemantics.Context}
    {resolution : MatchResolution} {value : Dynamic.Value} {body : List StatementId}
    (typing : Typing source context resolution)
    (selected : Dynamic.MatchCasesSelect context value resolution.cases resolution.defaultBody (.default body)) :
    ProtectedStateImperativeTypedSourceSites.Statements source context body := by
  obtain ⟨control, _type, _caseFacts, _scrutinee, _cases, fallback⟩ := typing
  obtain ⟨final, facts, typed⟩ := fallback body selected.defaultBody_eq
  exact ⟨control, final, facts, typed⟩

universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

/-- The genuine hidden Source allocation supplies deep heap typing. Its
actual marked allocator effects authenticate the same reached pool. -/
theorem after_hidden {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    {context : SourceSemantics.Context} {type : TypeSystem.Ty} {value : Dynamic.Value}
    {location : Dynamic.Location}
    (admitted : Admission bridge context first)
    (valueTyped : Dynamic.ValueHasType context initial.heap value type)
    (allocated : Dynamic.Heap.Allocates initial.heap type (some value) location reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    Admission bridge context last :=
  ⟨admitted.heap.allocate (.some valueTyped) allocated,
    StableRows.after_administrative (bridge.pool first) (bridge.pool last) admitted.rows frame⟩

/-- Pattern selection determines the raw binding row. The actual binder
extension and Source allocation establish the selected body's reached admission
and establish its environment agreement in the same actual arm context. -/
theorem after_arm {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    {source : TypedSource} {context armContext : SourceSemantics.Context}
    {control : ControlContext} {resolution : MatchResolution} {type : TypeSystem.Ty}
    {caseFacts : List BodyFacts} {value : Dynamic.Value} {body : List StatementId}
    {bindings : List (TypedBinder × Dynamic.Value)}
    {environment armEnvironment : Dynamic.Environment}
    (admitted : Admission bridge context first)
    (casesTyped : MatchCasesHaveType source control context type resolution.cases caseFacts)
    (valueTyped : Dynamic.ValueHasType context initial.heap value type)
    (selected : Dynamic.MatchCasesSelect context value resolution.cases resolution.defaultBody (.arm body bindings))
    (extended : BindersExtend source.owner context (bindings.map Prod.fst) armContext)
    (allocated : Dynamic.BindersAllocate environment initial.heap (bindings.map Prod.fst)
      (bindings.map Prod.snd) armEnvironment reached.heap)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    Admission bridge armContext last ∧
      Dynamic.EnvironmentAgrees reached.heap armContext.locals armEnvironment ∧
      ∃ final facts, StatementsHaveType source control armContext body final facts := by
  obtain ⟨binders, staticContext, final, facts, valuesTyped, bindersEq,
    staticExtended, bodyTyped, _member, monomorphic⟩ :=
    Dynamic.MatchCasesSelect.arm_preserves_typing casesTyped valueTyped selected
  have actualExtended : BindersExtend source.owner context (bindings.map Prod.fst) staticContext := by
    rw [bindersEq]
    exact staticExtended
  have contextEq := Dynamic.BindersExtend.functional actualExtended extended
  have actualValues : Dynamic.ValuesHaveTypes context initial.heap (bindings.map Prod.snd)
      ((bindings.map Prod.fst).map fun binder => binder.scheme.body) := by
    simpa only [List.map_map, Function.comp_def] using valuesTyped.unzip
  have heapTyped := Dynamic.BindersAllocate.preservesHeapTyping admitted.heap actualValues allocated
  have actualMono : ∀ binder, binder ∈ bindings.map Prod.fst → binder.scheme.quantified = [] := by
    rw [bindersEq]
    exact monomorphic
  exact ⟨⟨Dynamic.BindersExtend.control_heap_forward extended heapTyped,
    StableRows.after_administrative (bridge.pool first) (bridge.pool last) admitted.rows frame⟩,
    allocated.preservesEnvironmentAgreement extended actualMono locals,
    contextEq ▸ ⟨final, facts, bodyTyped⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMatchAdmission
