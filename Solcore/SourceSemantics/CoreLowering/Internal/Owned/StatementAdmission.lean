import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.DataPlaceKeyOrder
import Solcore.SourceSemantics.Dynamic.WholeLanguagePreservation
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeTypedSourceSites
import Solcore.SourceSemantics.Dynamic.PatternCompletenessProperties
import Solcore.SourceSemantics.CoreLowering.ProtectedStateScopeReturn
import Solcore.SourceSemantics.Staging.SelectedProjectedWritePreservation

/-!
# Owned callables: statement admission

Admission of places, assignments, `for` items and matches.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPlaceAdmission
/-! Genuine Source place typing supplies exactly the ordered key occurrences.
The actual resolution trace establishes deep heap typing at the same reached
getter state; stable rows use only its real administrative preservation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPlaceAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

/-- Members contribute no key expression. Every index retains its original
position, including duplicate expression occurrences. -/
theorem projections_keys_typed {source : TypedSource} {context : SourceSemantics.Context}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection}
    (typing : SourceProjectionsHaveType source context root projections leaf) :
    ∃ originalSourceTypes,
      ExpressionsHaveTypes source context (DataPlaceKeyOrder.sourceKeys projections) originalSourceTypes := by
  cases projections with
  | nil =>
    cases typing
    exact ⟨[], .nil _⟩
  | cons projection rest =>
    cases projection with
    | member name index =>
      cases typing with
      | member _ restTyped => exact projections_keys_typed (projections := rest) restTyped
    | index key =>
      cases typing with
      | index keyTyped restTyped =>
        obtain ⟨types, typed⟩ := projections_keys_typed (projections := rest) restTyped
        exact ⟨_ :: types, .cons keyTyped typed⟩
termination_by projections.length

/-- A genuinely typed target supplies the same ordered key row without a
native type-vector equality. -/
theorem place_keys_typed {source : TypedSource} {context : SourceSemantics.Context}
    {place : PlaceResolution} {type : TypeSystem.Ty}
    (typing : SourcePlaceHasType source context place type) :
    ∃ originalSourceTypes,
      ExpressionsHaveTypes source context (DataPlaceKeyOrder.sourceKeys place.projections) originalSourceTypes := by
  cases typing with
  | intro _ projections _ => exact projections_keys_typed projections

/-- Both Source assignment forms retain their genuine raw target type. -/
theorem assignment_target_typed {source : TypedSource} {context : SourceSemantics.Context}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (typing : SourceAssignmentHasType source context assignment operator rhs) :
    ∃ type, SourcePlaceHasType source context assignment.target type := by
  cases typing <;> exact ⟨_, by assumption⟩

/-- Normalize only an actual ordered key member to its retained Source node.
The original typing row and unique occurrence lookup justify the equality. -/
theorem key_expression_typed {source : TypedSource} {context : SourceSemantics.Context}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection}
    {id : ExpressionId} {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source)
    (typing : SourceProjectionsHaveType source context root projections leaf)
    (member : id ∈ DataPlaceKeyOrder.sourceKeys projections)
    (found : source.lookupExpression? id = some node) :
    ExpressionHasType source context id node.type := by
  obtain ⟨types, original⟩ := projections_keys_typed typing
  exact CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique original member found

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (context : SourceSemantics.Context)

/-- Resolution's actual Source endpoint is also the getter state's Source
heap. The getter's real cumulative frame retains every reached row's history. -/
theorem after_resolution {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    (admitted : Admission bridge context first)
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {place : PlaceResolution}
    {target : Dynamic.ResolvedPlace} {type : TypeSystem.Ty}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (typed : SourcePlaceHasType source context place type)
    (trace : Dynamic.SourcePlaceResolves program context evidence source environment
      initial.heap place target reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    Admission bridge context last := by
  have expressionPreserves : Dynamic.ExpressionExecutionPreserves program context evidence source environment := by
    intro before after id value type covers locals heapTyped typed evaluated
    exact wellFormed.wholeLanguagePreservation.expression context evidence source environment
      before after id value type runtime covers locals heapTyped typed evaluated
  obtain ⟨rootType, _resolved, heapTyped, _extension⟩ :=
    trace.preserves expressionPreserves covers locals admitted.heap typed
  exact ⟨heapTyped,
    StableRows.after_administrative (bridge.pool first) (bridge.pool last) admitted.rows frame⟩

/-- Keep the independent original Source resolution grade and the same actual
reached getter state. -/
theorem after_resolution_sized {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    (admitted : Admission bridge context first)
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {place : PlaceResolution}
    {target : Dynamic.ResolvedPlace} {type : TypeSystem.Ty} {size : Nat}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (typed : SourcePlaceHasType source context place type)
    (trace : SourceExecutionSize.SourcePlaceResolves program size context evidence source environment
      initial.heap place target reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    Admission bridge context last :=
  after_resolution bridge context first last admitted wellFormed runtime covers locals typed trace.sound frame

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPlaceAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAssignmentAdmission
/-! Genuine Source assignment typing and the actual successful write trace
establish admission at the same reached caller state. Faults retain actual
stable rows through administrative preservation without a deep heap claim. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAssignmentAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

/-- Normalize the genuine raw RHS typing to its exact retained occurrence. -/
theorem rhs_typed {source : TypedSource} {context : SourceSemantics.Context}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {node : ExpressionNode} (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? rhs = some node)
    (typed : SourceAssignmentHasType source context assignment operator rhs) :
    ExpressionHasType source context rhs node.type := by
  have original : ∃ type, ExpressionHasType source context rhs type := by
    cases typed <;> exact ⟨_, by assumption⟩
  obtain ⟨type, original⟩ := original
  obtain ⟨actual, contains, sameType⟩ := original.stored_type
  have sameNode : actual = node := Option.some.inj
    ((lookupExpression?_complete unique contains).symm.trans found)
  subst actual
  exact sameType.symm ▸ original

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (context : SourceSemantics.Context)

/-- The authentic successful Source assignment proves deep heap typing.
All stable histories belong to the actual reached pool. -/
theorem after_assignment {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    (admitted : Admission bridge context first)
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {updated : Dynamic.Value}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (typed : SourceAssignmentHasType source context assignment operator rhs)
    (trace : Dynamic.SourcePlaceAssignment program context evidence source
      (Dynamic.AssignmentValueApplies operator) environment initial.heap assignment.target rhs updated reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    Admission bridge context last := by
  have expressionPreserves : Dynamic.ExpressionExecutionPreserves program context evidence source environment := by
    intro before after id value type covers locals heapTyped typed evaluated
    exact wellFormed.wholeLanguagePreservation.expression context evidence source environment
      before after id value type runtime covers locals heapTyped typed evaluated
  have preserved := trace.preserves expressionPreserves covers locals admitted.heap typed
  exact ⟨preserved.1,
    StableRows.after_administrative (bridge.pool first) (bridge.pool last) admitted.rows frame⟩

/-- Keep the original Source grade and actual completed written-prefix state. -/
theorem after_assignment_sized {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    (admitted : Admission bridge context first)
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {updated : Dynamic.Value} {size : Nat}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (typed : SourceAssignmentHasType source context assignment operator rhs)
    (trace : SourceExecutionSize.SourcePlaceAssignment program size context evidence source
      (Dynamic.AssignmentValueApplies operator) environment initial.heap assignment.target rhs updated reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    Admission bridge context last :=
  after_assignment bridge context first last admitted wellFormed runtime covers locals typed trace.sound frame

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAssignmentAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedForItemsAdmission
/-! Actual for-item execution supplies admission at its live final context and
at the original context used after binder restoration. Stable row histories
come from the same reached pool and its real administrative receipt. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedForItemsAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

/-- Source typing and this exact successful trace establish both legitimate
heap contexts. The original prefix's reached state is retained verbatim. -/
theorem after_items {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    {context staticFinalContext runtimeFinalContext : SourceSemantics.Context}
    (admitted : Admission bridge context first)
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment finalEnvironment : Dynamic.Environment} {items : List ForItemForm}
    {control : SourceSemantics.ControlContext}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (typing : ForItemsHaveType source control context items staticFinalContext)
    (trace : Dynamic.ForItemsExecute program context evidence source environment initial.heap
      items runtimeFinalContext finalEnvironment reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    runtimeFinalContext = staticFinalContext ∧ Admission bridge context last ∧
      Admission bridge staticFinalContext last ∧ Dynamic.HeapTypesExtend initial.heap reached.heap ∧
        Dynamic.EnvironmentAgrees reached.heap staticFinalContext.locals finalEnvironment := by
  obtain ⟨same, heapTyped, extension, finalLocals⟩ :=
    trace.preserved wellFormed runtime covers locals admitted.heap typing
  have fields := Dynamic.ForItemsHaveType.runtimeContextFields typing
  have finalTyped := heapTyped.transportClosed fields.signatures runtime.closed
    (fields.targetClosed runtime.closed) runtime.variables_closed
    (fields.targetResidualVariablesOpen runtime.residual_variables_open)
  have rows := StableRows.after_administrative (bridge.pool first) (bridge.pool last) admitted.rows frame
  exact ⟨same, ⟨heapTyped, rows⟩, ⟨finalTyped, rows⟩, extension, finalLocals⟩

/-- Keep the actual Source prefix size independent from every native suffix
budget while establishing admission at the exact reached state. -/
theorem after_items_sized {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    {context staticFinalContext runtimeFinalContext : SourceSemantics.Context}
    (admitted : Admission bridge context first)
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment finalEnvironment : Dynamic.Environment} {items : List ForItemForm}
    {control : SourceSemantics.ControlContext} {size : Nat}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (typing : ForItemsHaveType source control context items staticFinalContext)
    (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment initial.heap
      items runtimeFinalContext finalEnvironment reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    runtimeFinalContext = staticFinalContext ∧ Admission bridge context last ∧
      Admission bridge staticFinalContext last ∧ Dynamic.HeapTypesExtend initial.heap reached.heap ∧
        Dynamic.EnvironmentAgrees reached.heap staticFinalContext.locals finalEnvironment :=
  after_items bridge first last admitted wellFormed runtime covers locals typing trace.sound frame

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedForItemsAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMatchAdmission
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMatchPrefixAdmission
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStagedProjectedAssignmentAdmission
/-! Final projected writes use the actual successful key and RHS endpoints.
Original Source key types are retained independently of native layout types. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStagedProjectedAssignmentAdmission
open Frontend SourceInference Staging.Recursive

/-- The original assignment, ordered key values and actual RHS admission
supply deep heap typing for the real write at the latest root. -/
theorem heap_after_assignment
    {source : TypedSource} {context : SourceSemantics.Context}
    {operator : Syntax.ValueAssignOp}
    {assignment : AssignmentResolution} {rhs : ExpressionId} {node : ExpressionNode}
    {environment : Dynamic.Environment} {before getter middle after : Dynamic.Heap}
    {types : List TypeSystem.Ty} {values : List Dynamic.Value}
    {target : Dynamic.ResolvedPlace} {right updated : Dynamic.Value}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? rhs = some node)
    (typed : SourceAssignmentHasType source context assignment operator rhs)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (row : ExpressionsHaveTypes source context (ProjectedTarget.keys assignment.target.projections) types)
    (keyValues : Dynamic.ValuesHaveTypes context getter values types)
    (getterHeap : Dynamic.HeapWellTyped context getter)
    (getterMetadata : Dynamic.HeapTypesExtend before getter)
    (snapshot : ProjectedTarget.Snapshot environment before getter assignment.target values target)
    (heapTyped : Dynamic.HeapWellTyped context middle)
    (rightTyped : Dynamic.ValueHasType context middle right node.type)
    (rhsMetadata : Dynamic.HeapTypesExtend getter middle)
    (write : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected right replacement)
      middle target updated after) :
    Dynamic.HeapWellTyped context after := by
  cases typed with
  | equal targetTyped rhsTyped _ =>
      obtain ⟨actual, contains, storedType⟩ := rhsTyped.stored_type
      have sameNode : actual = node := Option.some.inj
        ((lookupExpression?_complete unique contains).symm.trans found)
      subst actual
      obtain ⟨root, savedTyped⟩ := SelectedPreservation.projected_target_typed unique locals
        getterHeap getterMetadata targetTyped row keyValues snapshot
      have rightSource := storedType ▸ rightTyped
      exact (SelectedPreservation.projected_write_equal savedTyped
        ⟨rightSource, heapTyped, rhsMetadata⟩ write).1
  | wordCompound kind targetTyped rhsTyped _ =>
      obtain ⟨actual, contains, storedType⟩ := rhsTyped.stored_type
      have sameNode : actual = node := Option.some.inj
        ((lookupExpression?_complete unique contains).symm.trans found)
      subst actual
      obtain ⟨root, savedTyped⟩ := SelectedPreservation.projected_target_typed unique locals
        getterHeap getterMetadata targetTyped row keyValues snapshot
      have rightSource := storedType ▸ rightTyped
      exact (SelectedPreservation.projected_write_compound kind savedTyped
        ⟨rightSource, heapTyped, rhsMetadata⟩ write).1

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStagedProjectedAssignmentAdmission
end
