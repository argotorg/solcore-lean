import Solcore.SourceSemantics.CoreLowering.ProtectedAssignmentStatements
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCallMeaning
import Solcore.SourceSemantics.CoreLowering.TypedScopedStatementMeaning

/-! Fixed lexical scope permits projected assignment, discarded expressions and
ordinary returns. Static named-call trees close all child/body meanings. Actual
installed globals/current history remain a guarded runtime entry condition. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedAssignmentTails
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

inductive Tree (values : ValuesContext) (source : TypedSource) (context : SourceSemantics.Context)
    (certificate : GenericExpressionMeaning.Certificate) (scope : Scope)
    (administrative : Core.Context) (definitions : DataEnvironment) :
    Bool → List StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | nil {mode expected type} (allowed : mode = false ∨ expected = .unit) :
      Tree values source context certificate scope administrative definitions mode [] expected type (LocalLoop.fallthrough type)
  | returnUnit {mode id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt none) :
      Tree values source context certificate scope administrative definitions mode (id :: rest) .unit .unit (LocalLoop.returned .unit)
  | returnValue {mode id node expression expressionNode expected lowered} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression))
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (value : certificate scope expression lowered) :
      Tree values source context certificate scope administrative definitions mode (id :: rest) expected lowered.type
        (LocalLoop.returnValue lowered.type lowered.expression)
  | tail {id node expression expressionNode expected lowered}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (value : certificate scope expression lowered) :
      Tree values source context certificate scope administrative definitions true [id] expected lowered.type
        (LocalLoop.returnValue lowered.type lowered.expression)
  | discard {mode id node expression expressionNode semicolon rest expected lowered type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (value : certificate scope expression lowered)
      (remaining : Tree values source context certificate scope administrative definitions mode rest expected type body) :
      Tree values source context certificate scope administrative definitions mode (id :: rest) expected type
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)

  | assignment {mode id node assignment operator rhs rest expected type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
      (head : GenericAssignmentStatements.Head values source context certificate scope administrative definitions assignment operator rhs)
      (projected : head.prepared.steps ≠ [])
      (remaining : Tree values source context certificate scope administrative definitions mode rest expected type body) :
      Tree values source context certificate scope administrative definitions mode (id :: rest) expected type
        (head.emit body (LocalLoop.controlType type))

/-- The real production callback determines the assignment head and its exact
continuation expression. Only actual key/RHS lowering receipts are requested. -/
theorem Tree.of_assignment_lower {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {reasonAt : ExpressionId → Word}
    {scope : Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {expression : SourceCoreCompatibleDataPlaces.ExpressionLowerer} {fuel : Nat} {site : SourceCoreElaboration.ErrorSite}
    {mode : Bool} {id : StatementId} {node : StatementNode} {rest : List StatementId}
    {expected : TypeSystem.Ty} {type result : Ty} {next code : Expr}
    {invalidProjection invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
    (projected : assignment.target.projections ≠ [])
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = values.checked.signatures)
    (sourceTyped : ∀ binder, SourceCoreCompatibleDataPlaces.rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (writable : ∀ binder, SourceCoreCompatibleDataPlaces.rootBinder source assignment.target.root = .ok binder →
      WritableLocal context assignment.target.root binder.scheme.body)
    (rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    (extract : ∀ child lowered, child ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections →
      expression fuel source scope child reasonAt = .ok lowered → ∃ childNode,
      source.lookupExpression? child = some childNode ∧ certificate scope child lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) definitions)
    (accepted : SourceCoreCompatibleDataPlaces.lower values values.checked.signatures expression fuel source scope site
      assignment operator (some rhs) (LocalLoop.controlType type) next reasonAt invalidProjection invalidOperand missing = .ok code)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code result definitions)
    (tail : Tree values source context certificate scope administrative definitions mode rest expected type next) :
    Tree values source context certificate scope administrative definitions mode (id :: rest) expected type code := by
  obtain ⟨head, same⟩ := GenericAssignmentStatements.Head.of_lower unique signatures sourceTyped writable rightTyped profile extract accepted typed
  have project : ∀ {codes leaf}, GenericAssignmentStatements.Shape values source context certificate scope
      administrative definitions assignment.target head.prepared codes leaf → head.prepared.steps ≠ [] := by
    intro codes leaf shape
    cases shape with
    | bare empty _ => exact False.elim (projected empty)
    | projected layout _ => exact layout.nonempty
  have nonempty := project head.shape
  rw [same]
  exact .assignment found form head nonempty tail

namespace Tree
variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {certificate : GenericExpressionMeaning.Certificate} {scope : Scope} {administrative : Core.Context} {definitions : DataEnvironment}

inductive Errors (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    {mode : Bool} → {statements : List StatementId} → {expected : TypeSystem.Ty} → {type : Ty} → {code : Expr} →
      Tree values source context certificate scope administrative definitions mode statements expected type code → Prop where
  | nil {mode : Bool} {expected : TypeSystem.Ty} {type : Ty} {allowed : mode = false ∨ expected = .unit} :
      Errors registry faults (.nil (type := type) allowed)
  | returnUnit {mode id node rest} {found : source.lookupStatement? id = some node}
      {form : node.form = .returnStmt none} :
      Errors registry faults (.returnUnit (mode := mode) rest found form)
  | returnValue {mode id node expression expressionNode expected lowered rest}
      {found : source.lookupStatement? id = some node} {form : node.form = .returnStmt (some expression)}
      {expressionFound : source.lookupExpression? expression = some expressionNode}
      {valueType : expressionNode.type = expected} {value : certificate scope expression lowered} :
      Errors registry faults (.returnValue (mode := mode) rest found form expressionFound valueType value)
  | tail {id node expression expressionNode expected lowered}
      {found : source.lookupStatement? id = some node} {form : node.form = .expression expression false}
      {expressionFound : source.lookupExpression? expression = some expressionNode}
      {valueType : expressionNode.type = expected} {value : certificate scope expression lowered} :
      Errors registry faults (.tail found form expressionFound valueType value)
  | discard {mode id node expression expressionNode semicolon rest expected lowered type body}
      {found : source.lookupStatement? id = some node} {form : node.form = .expression expression semicolon}
      {notTail : (!semicolon && mode && rest.isEmpty) = false}
      {expressionFound : source.lookupExpression? expression = some expressionNode} {value : certificate scope expression lowered}
      {remaining : Tree values source context certificate scope administrative definitions mode rest expected type body}
      (remainingErrors : Errors registry faults remaining) :
      Errors registry faults (.discard found form notTail expressionFound value remaining)
  | assignment {mode id node assignment operator rhs rest expected type body}
      {found : source.lookupStatement? id = some node} {form : node.form = .assignValue assignment operator rhs}
      {head : GenericAssignmentStatements.Head values source context certificate scope administrative definitions assignment operator rhs}
      {projected : head.prepared.steps ≠ []}
      {remaining : Tree values source context certificate scope administrative definitions mode rest expected type body}
      (headErrors : head.Errors registry faults) (remainingErrors : Errors registry faults remaining) :
      Errors registry faults (.assignment found form head projected remaining)
end Tree

section Source
variable {program : Program} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {mode : Bool} {id : StatementId} {node : StatementNode} {rest : List StatementId} {outcome : Dynamic.ControlOutcome}

private theorem nil_executes (mode : Bool) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) :
    Executes mode program context evidence source environment heap [] context (.fallthrough environment) heap := by
  cases mode <;> exact .control .nil

private theorem return_unit_view
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .returnStmt none)
    (trace : Executes mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    finalContext = context ∧ outcome = .returned .unit ∧ after = before := by
  have notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
    intro _ _ expression; simp [form]
  cases source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique contains notTail executed with ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.returnUnit unique contains form head; cases impossible
    · exact ScalarStatementViews.returnUnit unique contains form head
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique contains notTail failed with ⟨_, head⟩ | ⟨_, _, _, head, _⟩
    · exact False.elim (ScalarStatementViews.returnUnit_cannot_fault unique contains form head)
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.returnUnit unique contains form head; cases impossible

private theorem return_value_view {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .returnStmt (some expression))
    (trace : Executes mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    finalContext = context ∧ ∃ expressionOutcome,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before expression expressionOutcome after ∧
      outcome = (match expressionOutcome with | .value value => .returned value | .fault reason => .fault reason) := by
  have notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
    intro _ _ expression; simp [form]
  cases source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique contains notTail executed with ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, _, impossible, _⟩ := ScalarStatementViews.returnValue unique contains form head; cases impossible
    · obtain ⟨same, value, rfl, child⟩ := ScalarStatementViews.returnValue unique contains form head
      exact ⟨same, _, .value child, rfl⟩
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique contains notTail failed with ⟨same, head⟩ | ⟨_, _, _, head, _⟩
    · exact ⟨same, _, .fault (ScalarStatementViews.returnValue_fault unique contains form head), rfl⟩
    · obtain ⟨_, _, impossible, _⟩ := ScalarStatementViews.returnValue unique contains form head; cases impossible

private theorem tail_view {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .expression expression false)
    (trace : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before [id] finalContext outcome after) :
    finalContext = context ∧ ∃ expressionOutcome,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before expression expressionOutcome after ∧
      outcome = (match expressionOutcome with | .value value => .returned value | .fault reason => .fault reason) := by
  have shape : ∀ other, ContainsStatement source id other → other = node := by
    intro other present
    exact Option.some.inj ((lookupStatement?_complete unique present).symm.trans (lookupStatement?_complete unique contains))
  cases trace with
  | control executed => cases executed with
    | tailExpression present same child =>
      rw [shape _ present, form] at same
      cases same
      exact ⟨rfl, _, .value child, rfl⟩
    | singleton present notTail _ =>
      have eq := shape _ present; subst_vars
      exact False.elim (notTail expression form)
  | fault failed => cases failed with
    | tailExpression present same child =>
      rw [shape _ present, form] at same
      cases same
      exact ⟨rfl, _, .fault child, rfl⟩
    | singleton head =>
      exact ⟨rfl, _, .fault (ScalarStatementViews.expression_fault unique contains form head), rfl⟩

theorem discard_view {expression : ExpressionId} {semi : Bool}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .expression expression semi) (guard : (!semi && mode && rest.isEmpty) = false)
    (trace : Executes mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    (∃ reason, finalContext = context ∧ outcome = .fault reason ∧
      Dynamic.ExpressionFaults program context evidence source environment before expression reason after) ∨
    (∃ value middle, Dynamic.ExpressionEvaluates program context evidence source environment before expression value middle ∧
      Executes mode program context evidence source environment middle rest finalContext outcome after) := by
  cases source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique contains (not_tail form guard) executed with ⟨_, _, _, head, tail⟩ | ⟨head, terminal⟩
    · obtain ⟨rfl, same, value, child⟩ := ScalarStatementViews.expression unique contains form head
      cases same
      exact .inr ⟨value, _, child, by cases mode <;> exact .control tail⟩
    · obtain ⟨_, rfl, _, _⟩ := ScalarStatementViews.expression unique contains form head
      cases terminal
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique contains (not_tail form guard) failed with ⟨same, head⟩ | ⟨_, _, _, head, tail⟩
    · exact .inl ⟨_, same, rfl, ScalarStatementViews.expression_fault unique contains form head⟩
    · obtain ⟨rfl, same, value, child⟩ := ScalarStatementViews.expression unique contains form head
      cases same
      exact .inr ⟨value, _, child, by cases mode <;> exact .fault tail⟩
end Source

variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {certificate : GenericExpressionMeaning.Certificate} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (preservation : ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults entry)
  (reflection : ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults entry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include extension transport preservation faithful observations unique in
/-- The entire finite source sequence determines a native execution. No child
execution or universal child meaning is a certificate premise. -/
theorem Tree.preserves {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree values source context certificate scope administrative ambient.definitions mode statements expected type code)
    (errors : Tree.Errors registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (trace : Executes mode program context evidence source environment before statements finalContext outcome after) :
    finalContext = context ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction errors generalizing mapping world actual before after store ξ outcome finalContext actualContext with
  | @nil mode expected type allowed =>
    cases source_view trace with
    | control executed =>
      obtain ⟨rfl, rfl, rfl⟩ := ScalarStatementViews.nil_view mode executed
      exact ⟨rfl, _, store, mapping, world, LocalLoop.fallthrough_evaluates _ _ _, .fallthrough environment,
        heaps, .refl _, .refl _, .refl _ _, .refl _⟩
    | fault failed => exact False.elim (ScalarStatementViews.nil_cannot_fault mode failed)
  | @returnUnit mode id node rest found form =>
    obtain ⟨rfl, rfl, rfl⟩ := return_unit_view unique (lookupStatement?_sound found) form trace
    exact ⟨rfl, _, store, mapping, world, LocalLoop.returned_evaluates .unit, .returned .unit,
      heaps, .refl _, .refl _, .refl _ _, .refl _⟩
  | @returnValue mode id node expression expressionNode expected lowered rest found form expressionFound valueType child =>
    obtain ⟨rfl, expressionOutcome, childTrace, rfl⟩ := return_value_view unique (lookupStatement?_sound found) form trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
      preservation child expressionFound
        environments heaps locals agrees actualTyped installed childTrace
    cases represented with
    | value payload =>
      exact ⟨rfl, _, finalStore, finalMap, finalWorld, by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_success _ evaluated,
        .returned (valueType ▸ payload), finalHeaps, maps, worlds, frame, metadata⟩
    | fault matched =>
      exact ⟨rfl, _, finalStore, finalMap, finalWorld, by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_failure _ evaluated,
        .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
  | @tail id node expression expressionNode expected lowered found form expressionFound valueType child =>
    obtain ⟨rfl, expressionOutcome, childTrace, rfl⟩ := tail_view unique (lookupStatement?_sound found) form trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
      preservation child expressionFound
        environments heaps locals agrees actualTyped installed childTrace
    cases represented with
    | value payload =>
      exact ⟨rfl, _, finalStore, finalMap, finalWorld, by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_success _ evaluated,
        .returned (valueType ▸ payload), finalHeaps, maps, worlds, frame, metadata⟩
    | fault matched =>
      exact ⟨rfl, _, finalStore, finalMap, finalWorld, by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_failure _ evaluated,
        .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
  | @discard mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining remainingErrors ih =>
    rcases discard_view unique (lookupStatement?_sound found) form guard trace with ⟨reason, rfl, rfl, failed⟩ | ⟨sourceValue, middle, childTrace, tail⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        preservation child expressionFound
          environments heaps locals agrees actualTyped installed (.fault failed)
      cases represented with
      | fault matched =>
        exact ⟨rfl, _, finalStore, finalMap, finalWorld, by rw [LoopRenaming.discard]; exact LocalSequence.discard_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        preservation child expressionFound
          environments heaps locals agrees actualTyped installed (.value childTrace)
      cases represented with
      | @value _ coreValue payload =>
        obtain ⟨same, value, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
          ih (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds))
            (transport.extend installed firstMaps firstWorlds firstFrame firstMetadata) tail
        refine ⟨same, value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata⟩
        rw [LoopRenaming.discard]
        rw [GenericExpressionMeaning.rename_prefix] at second
        exact LocalSequence.discard_success _ first second

  | @assignment mode id node assignment operator rhs rest expected type body found form head projected remaining headErrors remainingErrors ih =>
    have go {middleContext : SourceSemantics.Context} {next : Dynamic.Environment} {middle : Dynamic.Heap}
        (first : Dynamic.StatementExecutes program context evidence source environment before id middleContext (.fallthrough next) middle)
        (tail : Executes mode program middleContext evidence source next middle rest finalContext outcome after) :
        finalContext = context ∧ ∃ value finalStore finalMap finalWorld,
          Evaluates actual store ((head.emit body (LocalLoop.controlType type)).rename ξ) value finalStore ∧
          FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
          CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
          LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
          AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
      obtain ⟨rfl, same, updated, assigned⟩ := ScalarStatementViews.assignValue unique (lookupStatement?_sound found) form first
      cases same
      obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, frame, metadata, count, typed, observed, continuation⟩ :=
        ProtectedAssignmentStatements.Head.preserves_prefix functions extension program evidence transport preservation faithful observations
          head projected environments heaps locals agrees actualTyped installed assigned
      obtain ⟨same, value, finalStore, finalMap, finalWorld, completed, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata⟩ :=
        ih (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees slots) typed observed tail
      exact ⟨same, value, finalStore, finalMap, finalWorld,
        (continuation body (LocalLoop.controlType type)).wrap (by simpa only [DataPlaceChildExpressions.rename_prefix, count,
          SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using completed),
        represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata⟩
    cases source_view trace with
    | control executed =>
      rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _; simp [form]) executed with
        ⟨_, _, _, first, tail⟩ | ⟨first, terminal⟩
      · exact go first (by cases mode <;> exact .control tail)
      · obtain ⟨_, rfl, _⟩ := ScalarStatementViews.assignValue unique (lookupStatement?_sound found) form first
        cases terminal
    | fault failed =>
      rcases ScalarStatementViews.cons_fault_view mode unique (lookupStatement?_sound found) (by intro _ _; simp [form]) failed with
        ⟨rfl, first⟩ | ⟨_, _, _, first, tail⟩
      · obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata, observed⟩ :=
          ProtectedAssignmentStatements.Head.preserves_fault functions extension program evidence transport preservation faithful observations
            head projected environments heaps locals agrees actualTyped installed headErrors
            (ScalarStatementViews.assignValue_fault unique (lookupStatement?_sound found) form first) body (LocalLoop.controlType type)
        exact ⟨rfl, _, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
      · exact go first (by cases mode <;> exact .fault tail)

include extension transport reflection preservation faithful observations functionTypes in
/-- Every completed generated flow constructs its independent source trace.
The returned expression trace is derived from the actual native subtree. -/
theorem Tree.reflects {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree values source context certificate scope administrative ambient.definitions mode statements expected type code)
    (errors : Tree.Errors registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Executes mode program context evidence source environment before statements context outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction errors generalizing mapping world actual before store finalStore ξ value actualContext with
  | @nil mode expected type allowed =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LocalLoop.fallthrough_evaluates type actual store)
    exact ⟨_, before, mapping, world, nil_executes mode program context evidence source environment before, .fallthrough environment, heaps,
      .refl _, .refl _, .refl _ _, .refl _⟩
  | @returnUnit mode id node rest found form =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LocalLoop.returned_evaluates (.unit : Evaluates actual store .unit .unit store))
    exact ⟨_, before, mapping, world,
      terminal_intro mode rest (lookupStatement?_sound found) (by intro expression; simp [form]) (.returnUnit (lookupStatement?_sound found) form) (.returned _),
      .returned .unit, heaps, .refl _, .refl _, .refl _ _, .refl _⟩
  | @returnValue mode id node expression expressionNode expected lowered rest found form expressionFound valueType child =>
    rw [LoopRenaming.returnValue] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        reflection child expressionFound
          environments heaps locals agrees actualTyped installed childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalLoop.returnValue_failure _ childEvaluation)
          exact ⟨_, after, finalMap, finalWorld, head_fault mode rest (.returnValue (lookupStatement?_sound found) form failed),
            .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        reflection child expressionFound
          environments heaps locals agrees actualTyped installed childEvaluation
      cases represented with
      | value payload =>
        cases trace with
        | value childTrace =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalLoop.returnValue_success _ childEvaluation)
          exact ⟨_, after, finalMap, finalWorld,
            terminal_intro mode rest (lookupStatement?_sound found) (by intro expression; simp [form]) (.returnValue (lookupStatement?_sound found) form childTrace) (.returned _),
            .returned (valueType ▸ payload), finalHeaps, maps, worlds, frame, metadata⟩
  | @tail id node expression expressionNode expected lowered found form expressionFound valueType child =>
    rw [LoopRenaming.returnValue] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        reflection child expressionFound
          environments heaps locals agrees actualTyped installed childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalLoop.returnValue_failure _ childEvaluation)
          exact ⟨_, after, finalMap, finalWorld, .fault (.tailExpression (lookupStatement?_sound found) form failed),
            .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        reflection child expressionFound
          environments heaps locals agrees actualTyped installed childEvaluation
      cases represented with
      | value payload =>
        cases trace with
        | value childTrace =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalLoop.returnValue_success _ childEvaluation)
          exact ⟨_, after, finalMap, finalWorld, .control (.tailExpression (lookupStatement?_sound found) form childTrace),
            .returned (valueType ▸ payload), finalHeaps, maps, worlds, frame, metadata⟩
  | @discard mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining remainingErrors ih =>
    rw [LoopRenaming.discard] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        reflection child expressionFound
          environments heaps locals agrees actualTyped installed childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalSequence.discard_failure _ childEvaluation)
          exact ⟨_, after, finalMap, finalWorld, head_fault mode rest (.expression (lookupStatement?_sound found) form failed),
            .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        reflection child expressionFound
          environments heaps locals agrees actualTyped installed childEvaluation
      cases represented with
      | @value _ coreValue payload =>
        cases trace with
        | value childTrace =>
          obtain ⟨outcome, after, finalMap, finalWorld, tail, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
            ih (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees _)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds))
              (transport.extend installed firstMaps firstWorlds firstFrame firstMetadata)
              (by simpa only [GenericExpressionMeaning.rename_prefix] using branch)
          exact ⟨outcome, after, finalMap, finalWorld,
            prepend (lookupStatement?_sound found) (not_tail form guard) (.expression (lookupStatement?_sound found) form childTrace) tail,
            represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata⟩



  | @assignment mode id node assignment operator rhs rest expected type body found form head projected remaining headErrors remainingErrors ih =>
    rcases ProtectedAssignmentStatements.Head.reflects functions extension program evidence transport preservation reflection faithful observations
      head projected environments heaps locals agrees actualTyped installed functionTypes headErrors evaluated with
      ⟨reason, token, after, finalMap, finalWorld, trace, rfl, matched, finalHeaps, maps, worlds, frame, metadata, observed⟩ |
      ⟨updated, middle, written, middleMap, middleWorld, slots, trace, middleHeaps, maps, worlds, frame, metadata, count, typed, observed, continuation⟩
    · exact ⟨.fault reason, after, finalMap, finalWorld,
        head_fault mode rest (.assignValue (lookupStatement?_sound found) form trace), .fault matched,
        finalHeaps, maps, worlds, frame, metadata⟩
    · obtain ⟨outcome, after, finalMap, finalWorld, tail, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata⟩ :=
        ih (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees slots) typed observed
          (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using continuation)
      exact ⟨outcome, after, finalMap, finalWorld,
        prepend (lookupStatement?_sound found) (by intro _ _; simp [form]) (.assignValue (lookupStatement?_sound found) form trace) tail,
        represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedAssignmentTails

namespace Solcore.SourceSemantics.CoreLowering.NamedAssignmentStatementTail
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open TypedScopedStatements

abbrev Tree {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
    (bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (fuel : Nat) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word)
    (scope : SourceCoreLocalCell.Scope) (administrative : Core.Context) :=
  ProtectedAssignmentTails.Tree values source context
    (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt) scope administrative ambient.definitions

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

include extension faithful observations runtimeViews valid unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Static named argument/body trees and the real installed entry close the
entire projected assignment and fixed-scope tail. All fault prefixes are
included; no runtime child/body meaning is an external premise. -/
theorem Tree.preserves {mode : Bool} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree bodies compilation fuel source context solved reasonAt scope administrative mode statements expected type code)
    (errors : ProtectedAssignmentTails.Tree.Errors registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
    (trace : Executes mode program context evidence source environment before statements finalContext outcome after) :
    finalContext = context ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
        scope finalMap finalWorld after finalStore canonical := by
  have transport := NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix
  obtain ⟨same, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    ProtectedAssignmentTails.Tree.preserves functions extension program evidence unique transport
      (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing unique owners)
      faithful observations tree errors environments heaps locals agrees actualTyped installed trace
  exact ⟨same, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
    transport.extend installed maps worlds frame metadata⟩

include extension faithful observations runtimeViews valid unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Actual completed Core code supplies key, getter, RHS and tail outcomes in
source order. Installed closure payloads and frame history are retained from
the real administrative preservation receipts. -/
theorem Tree.reflects {mode : Bool} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree bodies compilation fuel source context solved reasonAt scope administrative mode statements expected type code)
    (errors : ProtectedAssignmentTails.Tree.Errors registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Executes mode program context evidence source environment before statements context outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
        scope finalMap finalWorld after finalStore canonical := by
  have transport := NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    ProtectedAssignmentTails.Tree.reflects functions extension program evidence transport
      (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing unique owners)
      (NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing)
      faithful observations runtimeViews tree errors environments heaps locals agrees actualTyped installed evaluated
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
    transport.extend installed maps worlds frame metadata⟩
end Solcore.SourceSemantics.CoreLowering.NamedAssignmentStatementTail
