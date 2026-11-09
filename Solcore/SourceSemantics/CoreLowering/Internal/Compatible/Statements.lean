import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionConstructors
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LiteralsAndStagedValues
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.LoopRenaming
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.CoreEvaluation
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.LoopLayouts
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionIndices
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MappingsAndEquality
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceMappings
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.BasicExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.FunctionCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedParameters

/-!
# Compatible profile: statements and named bodies

Trees, certificates and meaning of statements, bindings and initialized declarations, and of named bodies and parameters.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleStatementTree
/-! A fixed-scope function sequence with ordinary compatible expressions.
The static source spine retains raw result types and independent expression
 typing. Unreachable suffixes of explicit returns need no execution certificate.
Let bindings, assignments, scoped statements and calls are separate extensions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleStatements
open Core Frontend SourceInference
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

inductive Syntax (source : TypedSource) (context : SourceSemantics.Context) :
    List StatementId → TypeSystem.Ty → Prop where
  | nil : Syntax source context [] .unit
  | returnUnit {id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt none)
      (sourceType : node.type = .unit) : Syntax source context (id :: rest) .unit
  | returnValue {id node expression expressionNode expected} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression))
      (sourceType : node.type = expected) (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (value : CompatibleExpressionConstructors.Syntax source expression) : Syntax source context (id :: rest) expected
  | tail {id node expression expressionNode expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
      (sourceType : node.type = expected) (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (value : CompatibleExpressionConstructors.Syntax source expression) : Syntax source context [id] expected
  | discard {id node expression expressionNode semicolon rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && rest.isEmpty) = false)
      (sourceType : node.type = if semicolon then .unit else expressionNode.type)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (value : CompatibleExpressionConstructors.Syntax source expression)
      (remaining : Syntax source context rest expected) : Syntax source context (id :: rest) expected

inductive Tree (readFuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) :
    List StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | nil : Tree readFuel values source context solved reasonAt scope [] .unit .unit (LocalLoop.fallthrough .unit)
  | returnUnit {id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt none) :
      Tree readFuel values source context solved reasonAt scope (id :: rest) .unit .unit (LocalLoop.returned .unit)
  | returnValue {id node expression expressionNode expected lowered} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression))
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (value : CompatibleExpressionConstructors.Tree readFuel values source context solved reasonAt scope expression lowered) :
      Tree readFuel values source context solved reasonAt scope (id :: rest) expected lowered.type
        (LocalLoop.returnValue lowered.type lowered.expression)
  | tail {id node expression expressionNode expected lowered}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (value : CompatibleExpressionConstructors.Tree readFuel values source context solved reasonAt scope expression lowered) :
      Tree readFuel values source context solved reasonAt scope [id] expected lowered.type
        (LocalLoop.returnValue lowered.type lowered.expression)
  | discard {id node expression expressionNode semicolon rest expected lowered type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && rest.isEmpty) = false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (value : CompatibleExpressionConstructors.Tree readFuel values source context solved reasonAt scope expression lowered)
      (remaining : Tree readFuel values source context solved reasonAt scope rest expected type body) :
      Tree readFuel values source context solved reasonAt scope (id :: rest) expected type
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)

/-- The final function wrapper used by the actual general statement compiler. -/
def finish (type : Ty) (flow : Expr) (fellThrough escaped : Word) : Expr :=
  LocalControl.finish type (LocalLoop.toControl type flow escaped)
    (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough))

end Solcore.SourceSemantics.CoreLowering.CompatibleStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleStatementCertificates
/-! Static extraction from the production statement traversal. The generic
extraction callback is discharged by the actual contextual expression compiler
below; neither theorem assumes a child runtime execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleStatements
open Core Frontend SourceInference
open CompatibleEncoding (bind_ok)

private theorem read_found {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
      simp only [found] at accepted
      obtain ⟨projected, _, same⟩ := bind_ok accepted
      cases same
      rfl

private theorem ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

/-- A successful traversal plus independent raw source syntax/typing supplies
all expression and sequencing certificates, including early-return suffixes. -/
theorem tree_of_flow {readFuel : Nat} {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement}
    {reasonAt : ExpressionId → Word} {scope : Scope} {policy : SourceCoreLoops.Policy}
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (expressions : ∀ {fuel id node lowered}, CompatibleExpressionConstructors.Syntax source id →
      source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      CompatibleExpressionConstructors.Tree readFuel values source context solved reasonAt scope id lowered)
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context statements expected)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true selfReason = .ok code) :
    Tree readFuel values source context solved reasonAt scope statements expected type code := by
  induction syntaxTree generalizing fuel type code with
  | nil =>
    have same : type = .unit := (Except.ok.inj projection).symm
    subst type
    simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
    cases accepted
    exact .nil
  | @returnUnit id node rest found form sourceType =>
    have same : type = .unit := (Except.ok.inj projection).symm
    subst type
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      cases accepted
      exact .returnUnit rest found form
  | @returnValue id node expression expressionNode expected rest found form sourceType expressionFound valueType typed syntaxValue =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have same := ensure_same checkedType
      subst type
      cases accepted
      exact .returnValue rest found form expressionFound valueType (expressions syntaxValue expressionFound typed generated)
  | @tail id node expression expressionNode expected found form sourceType expressionFound valueType typed syntaxValue =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      simp only [Bool.not_false, List.isEmpty_nil, Bool.and_self, ↓reduceIte] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have same := ensure_same checkedType
      subst type
      cases accepted
      exact .tail found form expressionFound valueType (expressions syntaxValue expressionFound typed generated)
  | @discard id node expression expressionNode semicolon rest expected found form notTail sourceType expressionFound typed syntaxValue remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      simp only [Bool.and_true, notTail, Bool.false_eq_true, ↓reduceIte] at accepted
      cases semicolon <;> simp only [Bool.false_eq_true, ↓reduceIte] at accepted
      all_goals
        obtain ⟨checked, _, accepted⟩ := bind_ok accepted
        cases checked
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        exact .discard found form notTail expressionFound (expressions syntaxValue expressionFound typed generated)
          (ih projection generatedBody)

/-- The actual function wrapper retains the extracted flow certificate. -/
theorem tree_of_body {readFuel : Nat} {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement}
    {reasonAt : ExpressionId → Word} {scope : Scope} {policy : SourceCoreLoops.Policy}
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (expressions : ∀ {fuel id node lowered}, CompatibleExpressionConstructors.Syntax source id →
      source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      CompatibleExpressionConstructors.Tree readFuel values source context solved reasonAt scope id lowered)
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context statements expected)
    {fuel : Nat} {type : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code) :
    ∃ flow, code = finish type flow fellThrough escaped ∧
      Tree readFuel values source context solved reasonAt scope statements expected type flow := by
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, same⟩ := bind_ok accepted
  cases same
  exact ⟨flow, rfl, tree_of_flow readPolicy expressions syntaxTree projection generated⟩

/-- Production contextual lowering discharges every child certificate. The
remaining assumptions are static source grammar, typing, and policy receipts. -/
theorem tree_of_contextual_body
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {policy : SourceCoreLoops.Policy}
    (ordinary : CompatibleExpressionConstructors.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (readExpression : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (readStatement : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (lowerExpression : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression program representation
      signatures locals parents assignments diagnostics compilation native parent skipInitializer)
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {fellThrough escaped : Word}
    (syntaxTree : Syntax source context statements expected)
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code) :
    ∃ flow, code = finish type flow fellThrough escaped ∧
      Tree readFuel values source context compilation.solvedRequirements reasonAt scope statements expected type flow := by
  apply tree_of_body readStatement ?_ syntaxTree projection accepted
  intro budget id node lowered syntaxValue found typed generated
  rw [lowerExpression] at generated
  exact CompatibleExpressionConstructors.tree_of_contextual ordinary unique closed residual declarations
    syntaxValue found typed readExpression lowerRead leafLowerer generated

end Solcore.SourceSemantics.CoreLowering.CompatibleStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleStatementMeaning
/-! Finite semantics of fixed-scope compatible function sequences. The child
expression theorem is supplied by the concrete expression tree, rather than a
caller-provided runtime induction hypothesis. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleStatements
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

inductive FlowRep {values : ValuesContext} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (mapping : LocationMap) (world : StoreTyping)
    (faults : FunctionCalls.FaultRep) : TypeSystem.Ty → Ty → Dynamic.ControlOutcome → Value → Prop where
  | fallthrough (environment : Dynamic.Environment) : FlowRep functions mapping world faults .unit .unit
      (.fallthrough environment) (LocalLoop.fallthroughValue .unit)
  | returned {expected type sourceValue value}
      (payload : ValueRep values.checked registry functions mapping world expected sourceValue value type) :
      FlowRep functions mapping world faults expected type (.returned sourceValue) (LocalLoop.returnedValue value)
  | fault {expected type reason token} (matched : faults reason token) :
      FlowRep functions mapping world faults expected type (.fault reason) (.inLeft (LocalLoop.controlType type) (.word token))

private theorem not_tail {node : StatementNode} {id : ExpressionId} {semi : Bool} {rest : List StatementId}
    (form : node.form = .expression id semi) (guard : (!semi && rest.isEmpty) = false) :
    true = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
  intro _ empty expression impossible
  rw [form] at impossible
  cases impossible
  simp [empty] at guard

section Source
variable {program : Program} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : StatementId} {node : StatementNode} {rest : List StatementId} {outcome : Dynamic.ControlOutcome}

private theorem terminal_intro
    (contains : ContainsStatement source id node) (notTail : ∀ expression, node.form ≠ .expression expression false)
    (head : Dynamic.StatementExecutes program context evidence source environment before id context outcome after)
    (terminal : Dynamic.TerminalControl outcome) :
    Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) context outcome after := by
  cases rest with
  | nil => exact .control (.singleton contains notTail head)
  | cons => exact .control (.terminal head terminal)

private theorem head_fault
    {reason : Dynamic.SemanticFault}
    (head : Dynamic.StatementFaults program context evidence source environment before id reason after) :
    Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) context (.fault reason) after := by
  cases rest with
  | nil => exact .fault (.singleton head)
  | cons => exact .fault (.head head)

private theorem prepend
    {middle : Dynamic.Heap}
    (contains : ContainsStatement source id node)
    (notTail : true = true → rest = [] → ∀ expression, node.form ≠ .expression expression false)
    (head : Dynamic.StatementExecutes program context evidence source environment before id context (.fallthrough environment) middle)
    (tail : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment middle rest context outcome after) :
    Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) context outcome after := by
  cases rest with
  | nil => cases tail with
    | control executed => cases executed; exact .control (.singleton contains (notTail rfl rfl) head)
    | fault failed => cases failed
  | cons => cases tail with
    | control executed => exact .control (.cons head executed)
    | fault failed => exact .fault (.tail head failed)

private theorem return_unit_view
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .returnStmt none)
    (trace : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) finalContext outcome after) :
    finalContext = context ∧ outcome = .returned .unit ∧ after = before := by
  have notTail : true = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
    intro _ _ expression; simp [form]
  cases trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view true unique contains notTail executed with ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.returnUnit unique contains form head; cases impossible
    · exact ScalarStatementViews.returnUnit unique contains form head
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view true unique contains notTail failed with ⟨_, head⟩ | ⟨_, _, _, head, _⟩
    · exact False.elim (ScalarStatementViews.returnUnit_cannot_fault unique contains form head)
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.returnUnit unique contains form head; cases impossible

private theorem return_value_view {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .returnStmt (some expression))
    (trace : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) finalContext outcome after) :
    finalContext = context ∧ ∃ expressionOutcome,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before expression expressionOutcome after ∧
      outcome = (match expressionOutcome with | .value value => .returned value | .fault reason => .fault reason) := by
  have notTail : true = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
    intro _ _ expression; simp [form]
  cases trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view true unique contains notTail executed with ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, _, impossible, _⟩ := ScalarStatementViews.returnValue unique contains form head; cases impossible
    · obtain ⟨same, value, rfl, child⟩ := ScalarStatementViews.returnValue unique contains form head
      exact ⟨same, _, .value child, rfl⟩
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view true unique contains notTail failed with ⟨same, head⟩ | ⟨_, _, _, head, _⟩
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

private theorem discard_view {expression : ExpressionId} {semi : Bool}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .expression expression semi) (guard : (!semi && rest.isEmpty) = false)
    (trace : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) finalContext outcome after) :
    (∃ reason, finalContext = context ∧ outcome = .fault reason ∧
      Dynamic.ExpressionFaults program context evidence source environment before expression reason after) ∨
    (∃ value middle, Dynamic.ExpressionEvaluates program context evidence source environment before expression value middle ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment middle rest finalContext outcome after) := by
  cases trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view true unique contains (not_tail form guard) executed with ⟨_, _, _, head, tail⟩ | ⟨head, terminal⟩
    · obtain ⟨rfl, same, value, child⟩ := ScalarStatementViews.expression unique contains form head
      cases same
      exact .inr ⟨value, _, child, .control tail⟩
    · obtain ⟨_, rfl, _, _⟩ := ScalarStatementViews.expression unique contains form head
      cases terminal
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view true unique contains (not_tail form guard) failed with ⟨same, head⟩ | ⟨_, _, _, head, tail⟩
    · exact .inl ⟨_, same, rfl, ScalarStatementViews.expression_fault unique contains form head⟩
    · obtain ⟨rfl, same, value, child⟩ := ScalarStatementViews.expression unique contains form head
      cases same
      exact .inr ⟨value, _, child, .fault tail⟩
end Source

variable {readFuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))

include extension contextValid unique uninitialized in
/-- The entire finite source sequence determines a native execution. No child
execution or universal child meaning is a certificate premise. -/
theorem Tree.preserves [FunctionCalls.FaultTokens faults] {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree readFuel values source context solved reasonAt scope statements expected type code)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (trace : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before statements finalContext outcome after) :
    finalContext = context ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction tree generalizing mapping world actual before after store ξ outcome finalContext with
  | nil =>
    cases trace with
    | control executed =>
      cases executed
      exact ⟨rfl, _, store, mapping, world, LocalLoop.fallthrough_evaluates _ _ _, .fallthrough environment,
        heaps, .refl _, .refl _, .refl _ _, .refl _⟩
    | fault failed => cases failed
  | returnUnit rest found form =>
    obtain ⟨rfl, rfl, rfl⟩ := return_unit_view unique (lookupStatement?_sound found) form trace
    exact ⟨rfl, _, store, mapping, world, LocalLoop.returned_evaluates .unit, .returned .unit,
      heaps, .refl _, .refl _, .refl _ _, .refl _⟩
  | @returnValue id node expression expressionNode expected lowered rest found form expressionFound valueType child =>
    obtain ⟨rfl, expressionOutcome, childTrace, rfl⟩ := return_value_view unique (lookupStatement?_sound found) form trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
      CompatibleExpressionConstructors.preserves functions extension program evidence contextValid unique uninitialized child expressionFound
        environments heaps locals agrees childTrace
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
      CompatibleExpressionConstructors.preserves functions extension program evidence contextValid unique uninitialized child expressionFound
        environments heaps locals agrees childTrace
    cases represented with
    | value payload =>
      exact ⟨rfl, _, finalStore, finalMap, finalWorld, by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_success _ evaluated,
        .returned (valueType ▸ payload), finalHeaps, maps, worlds, frame, metadata⟩
    | fault matched =>
      exact ⟨rfl, _, finalStore, finalMap, finalWorld, by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_failure _ evaluated,
        .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
  | @discard id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining ih =>
    rcases discard_view unique (lookupStatement?_sound found) form guard trace with ⟨reason, rfl, rfl, failed⟩ | ⟨sourceValue, middle, childTrace, tail⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        CompatibleExpressionConstructors.preserves functions extension program evidence contextValid unique uninitialized child expressionFound
          environments heaps locals agrees (.fault failed)
      cases represented with
      | fault matched =>
        exact ⟨rfl, _, finalStore, finalMap, finalWorld, by rw [LoopRenaming.discard]; exact LocalSequence.discard_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        CompatibleExpressionConstructors.preserves functions extension program evidence contextValid unique uninitialized child expressionFound
          environments heaps locals agrees (.value childTrace)
      cases represented with
      | @value _ coreValue payload =>
        obtain ⟨same, value, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
          ih (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue) tail
        refine ⟨same, value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata⟩
        rw [LoopRenaming.discard]
        rw [GenericExpressionMeaning.rename_prefix] at second
        exact LocalSequence.discard_success _ first second

include extension contextValid uninitialized in
/-- Every completed generated flow constructs its independent source trace.
The returned expression trace is derived from the actual native subtree. -/
theorem Tree.reflects [FunctionCalls.FaultTokens faults] {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree readFuel values source context solved reasonAt scope statements expected type code)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before statements context outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction tree generalizing mapping world actual before store finalStore ξ value with
  | nil =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LocalLoop.fallthrough_evaluates .unit actual store)
    exact ⟨_, before, mapping, world, .control .nil, .fallthrough environment, heaps,
      .refl _, .refl _, .refl _ _, .refl _⟩
  | returnUnit rest found form =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LocalLoop.returned_evaluates (.unit : Evaluates actual store .unit .unit store))
    exact ⟨_, before, mapping, world,
      terminal_intro (lookupStatement?_sound found) (by intro expression; simp [form]) (.returnUnit (lookupStatement?_sound found) form) (.returned _),
      .returned .unit, heaps, .refl _, .refl _, .refl _ _, .refl _⟩
  | @returnValue id node expression expressionNode expected lowered rest found form expressionFound valueType child =>
    rw [LoopRenaming.returnValue] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        CompatibleExpressionConstructors.reflects functions extension program evidence contextValid uninitialized child expressionFound
          environments heaps locals agrees childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalLoop.returnValue_failure _ childEvaluation)
          exact ⟨_, after, finalMap, finalWorld, head_fault (.returnValue (lookupStatement?_sound found) form failed),
            .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        CompatibleExpressionConstructors.reflects functions extension program evidence contextValid uninitialized child expressionFound
          environments heaps locals agrees childEvaluation
      cases represented with
      | value payload =>
        cases trace with
        | value childTrace =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalLoop.returnValue_success _ childEvaluation)
          exact ⟨_, after, finalMap, finalWorld,
            terminal_intro (lookupStatement?_sound found) (by intro expression; simp [form]) (.returnValue (lookupStatement?_sound found) form childTrace) (.returned _),
            .returned (valueType ▸ payload), finalHeaps, maps, worlds, frame, metadata⟩
  | @tail id node expression expressionNode expected lowered found form expressionFound valueType child =>
    rw [LoopRenaming.returnValue] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        CompatibleExpressionConstructors.reflects functions extension program evidence contextValid uninitialized child expressionFound
          environments heaps locals agrees childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalLoop.returnValue_failure _ childEvaluation)
          exact ⟨_, after, finalMap, finalWorld, .fault (.tailExpression (lookupStatement?_sound found) form failed),
            .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        CompatibleExpressionConstructors.reflects functions extension program evidence contextValid uninitialized child expressionFound
          environments heaps locals agrees childEvaluation
      cases represented with
      | value payload =>
        cases trace with
        | value childTrace =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalLoop.returnValue_success _ childEvaluation)
          exact ⟨_, after, finalMap, finalWorld, .control (.tailExpression (lookupStatement?_sound found) form childTrace),
            .returned (valueType ▸ payload), finalHeaps, maps, worlds, frame, metadata⟩
  | @discard id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining ih =>
    rw [LoopRenaming.discard] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        CompatibleExpressionConstructors.reflects functions extension program evidence contextValid uninitialized child expressionFound
          environments heaps locals agrees childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalSequence.discard_failure _ childEvaluation)
          exact ⟨_, after, finalMap, finalWorld, head_fault (.expression (lookupStatement?_sound found) form failed),
            .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        CompatibleExpressionConstructors.reflects functions extension program evidence contextValid uninitialized child expressionFound
          environments heaps locals agrees childEvaluation
      cases represented with
      | @value _ coreValue payload =>
        cases trace with
        | value childTrace =>
          obtain ⟨outcome, after, finalMap, finalWorld, tail, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
            ih (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees _)
              (by simpa only [GenericExpressionMeaning.rename_prefix] using branch)
          exact ⟨outcome, after, finalMap, finalWorld,
            prepend (lookupStatement?_sound found) (not_tail form guard) (.expression (lookupStatement?_sound found) form childTrace) tail,
            represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata⟩

/-- Final language outcomes, with Unit fallthrough distinguished in the source
trace. No transfer outcome is admitted by this fixed-scope grammar. -/
inductive BodyRep {values : ValuesContext} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (mapping : LocationMap) (world : StoreTyping)
    (faults : FunctionCalls.FaultRep) : TypeSystem.Ty → Ty → Dynamic.ControlOutcome → Value → Prop where
  | fallthrough (environment : Dynamic.Environment) : BodyRep functions mapping world faults .unit .unit
      (.fallthrough environment) (.inRight .word .unit)
  | returned {expected type sourceValue value}
      (payload : ValueRep values.checked registry functions mapping world expected sourceValue value type) :
      BodyRep functions mapping world faults expected type (.returned sourceValue) (.inRight .word value)
  | fault {expected type reason token} (matched : faults reason token) :
      BodyRep functions mapping world faults expected type (.fault reason) (.inLeft type (.word token))

private theorem finish_rename (type : Ty) (flow : Expr) (fellThrough escaped : Word) (ξ : Renaming) :
    (finish type flow fellThrough escaped).rename ξ = finish type (flow.rename ξ) fellThrough escaped := by
  unfold finish
  split <;> simp [LocalControl.finish, LocalLoop.toControl, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.rename, Renaming.lift]

private theorem finish_from_flow {mapping : LocationMap} {world : StoreTyping}
    {environment : Environment} {before after : Store} {expected : TypeSystem.Ty} {type : Ty}
    {outcome : Dynamic.ControlOutcome} {flow : Expr} {value : Value}
    (fellThrough escaped : Word)
    (represented : FlowRep (registry := registry) functions mapping world faults expected type outcome value)
    (evaluated : Evaluates environment before flow value after) :
    ∃ result, Evaluates environment before (finish type flow fellThrough escaped) result after ∧
      BodyRep (registry := registry) functions mapping world faults expected type outcome result := by
  cases represented with
  | fallthrough sourceEnvironment =>
    exact ⟨_, LocalControl.finish_fallthrough .unit (LocalLoop.toControl_normal _ escaped evaluated) (by simpa [LanguageResult.success, Expr.weakenAt] using (show Evaluates (.unit :: .inLeft .unit .unit :: environment) after (.inRight .word .unit) (.inRight .word .unit) after from .inRight .unit)) ,
      .fallthrough sourceEnvironment⟩
  | returned payload =>
    exact ⟨_, LocalControl.finish_returned _ (LocalLoop.toControl_normal _ escaped evaluated), .returned payload⟩
  | fault matched =>
    exact ⟨_, LocalControl.finish_failure _ (LocalLoop.toControl_failure _ escaped evaluated), .fault matched⟩

private theorem finish_input {environment : Environment} {before after : Store} {type : Ty}
    {flow : Expr} {fellThrough escaped : Word} {result : Value}
    (evaluated : Evaluates environment before (finish type flow fellThrough escaped) result after) :
    ∃ value middle, Evaluates environment before flow value middle := by
  cases evaluated with
  | caseLeft control branch | caseRight control branch =>
    cases control with
    | caseLeft input branch | caseRight input branch => exact ⟨_, _, input⟩

include extension contextValid unique uninitialized in
/-- Finite preservation for the complete production function wrapper. -/
theorem Tree.body_preserves [FunctionCalls.FaultTokens faults] {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {flow : Expr}
    (tree : Tree readFuel values source context solved reasonAt scope statements expected type flow)
    (fellThrough escaped : Word)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (trace : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before statements finalContext outcome after) :
    finalContext = context ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((finish type flow fellThrough escaped).rename ξ) value finalStore ∧
      BodyRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨same, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    tree.preserves functions extension program evidence contextValid unique uninitialized environments heaps locals agrees trace
  obtain ⟨result, completed, related⟩ := finish_from_flow functions fellThrough escaped represented evaluated
  exact ⟨same, result, finalStore, finalMap, finalWorld, by rw [finish_rename]; exact completed,
    related, finalHeaps, maps, worlds, frame, metadata⟩

include extension contextValid uninitialized in
/-- Completed full-body execution reflects into the independent source function
sequence, with the same final heap and all administrative-frame obligations. -/
theorem Tree.body_reflects [FunctionCalls.FaultTokens faults] {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {flow : Expr}
    (tree : Tree readFuel values source context solved reasonAt scope statements expected type flow)
    (fellThrough escaped : Word)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual store ((finish type flow fellThrough escaped).rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before statements context outcome after ∧
      BodyRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  rw [finish_rename] at evaluated
  obtain ⟨flowValue, middleStore, flowEvaluation⟩ := finish_input evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    tree.reflects functions extension program evidence contextValid uninitialized environments heaps locals agrees flowEvaluation
  obtain ⟨result, completed, related⟩ := finish_from_flow functions fellThrough escaped represented flowEvaluation
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated completed
  exact ⟨outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, frame, metadata⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleStatementBindingTree
/-! Ordinary uninitialized lexical bindings before a fixed-scope compatible
body. Each binding retains the actual indexed allocator receipts. Generalized
bindings and initializer evaluation are separate extensions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleStatementBindings
open Core Frontend SourceInference
abbrev Scope := SourceCoreLocalCell.Scope
abbrev ValuesContext := SourceCoreCompatibleValues.Context

def request (source : TypedSource) (scope : Scope) (binder : TypedBinder) (payload : Ty) :
    SourceCoreSourceCells.Request := ⟨source, scope, Renaming.id, binder, payload, none⟩

inductive Syntax (source : TypedSource) (finalContext : SourceSemantics.Context) :
    SourceSemantics.Context → List StatementId → TypeSystem.Ty → Prop where
  | body {statements expected} (syntaxTree : CompatibleStatements.Syntax source finalContext statements expected) :
      Syntax source finalContext finalContext statements expected
  | uninitialized {context nextContext id node binder rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : Syntax source finalContext nextContext rest expected) :
      Syntax source finalContext context (id :: rest) expected

inductive Tree (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (readFuel : Nat) (values : ValuesContext) (source : TypedSource)
    (finalContext : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) :
    SourceSemantics.Context → Scope → List StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | body {scope statements expected type code}
      (body : CompatibleStatements.Tree readFuel values source finalContext solved reasonAt scope statements expected type code) :
      Tree layouts owner active frame globals onError readFuel values source finalContext solved reasonAt
        finalContext scope statements expected type code
  | uninitialized {context nextContext scope id node binder rest expected type body payload}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (projected : values.checked.catalog.project binder.scheme.body = .ok payload)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (request source scope binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (request source scope binder payload))
      (same : annotation.original = allocation.expression)
      (remaining : Tree layouts owner active frame globals onError readFuel values source finalContext solved reasonAt
        nextContext ((binder.id, payload) :: scope) rest expected type body) :
      Tree layouts owner active frame globals onError readFuel values source finalContext solved reasonAt
        context scope (id :: rest) expected type (.letE annotation.expression body)
end Solcore.SourceSemantics.CoreLowering.CompatibleStatementBindings
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleStatementBindingCertificates
/-! Successful production traversal extracts the marked binding spine. The
expression callback is static certificate extraction, never a runtime premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleStatementBindings
open Core Frontend SourceInference
open CompatibleEncoding (bind_ok)

private theorem read_found {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
      simp only [found] at accepted
      obtain ⟨projected, _, same⟩ := bind_ok accepted
      cases same
      rfl

/-- Native binder admission retains its original source projection. -/
theorem binder_projected {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {scope : Scope} {binder : TypedBinder} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.lowerBinder checked source scope binder = .ok type) :
    checked.catalog.project binder.scheme.body = .ok type := by
  unfold SourceCoreCompatibleDataExpressions.lowerBinder at accepted
  by_cases owner : binder.id.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · by_cases mono : binder.scheme.quantified.isEmpty = true
    · by_cases requirements : binder.schemeRequirements.isEmpty = true
      · by_cases staged : (binder.comptime && !checked.catalog.callableContracts) = true
        · simp [owner, mono, requirements, staged, throw, bind, Except.bind] at accepted
        · by_cases duplicate : scope.any (fun entry => decide (entry.1 = binder.id)) = true
          · simp [owner, mono, requirements, staged, duplicate, throw, bind, Except.bind] at accepted
          · apply CompatibleExpressionReads.projectType_of_accepted
            simpa [owner, mono, requirements, staged, duplicate, throw, bind, Except.bind] using accepted
      · simp [owner, mono, requirements, throw, bind, Except.bind] at accepted
    · simp [owner, mono, throw, bind, Except.bind] at accepted

/-- The actual source declaration is retained when the lexical scope grows. -/
theorem scope_bind {source : TypedSource} {scope : Scope} {context nextContext : SourceSemantics.Context}
    {binder : TypedBinder} (payload : Ty)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
    (extended : BinderExtends source.owner context binder nextContext) :
    CompatibleExpressionReads.ScopeDeclarations source ((binder.id, payload) :: scope) nextContext := by
  cases extended
  intro id declared index type selected authentic
  by_cases same : binder.id = id
  · subst id
    have identical : binder = declared := Except.ok.inj (declaration.symm.trans authentic)
    subst declared
    exact .head
  · simp only [SourceCoreLocalCell.lookup?, same, ↓reduceIte] at selected
    cases previous : SourceCoreLocalCell.lookup? scope id with
    | none => simp [previous] at selected
    | some entry =>
      exact .tail same (declarations _ _ _ _ previous authentic)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource} {finalContext : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {policy : SourceCoreLoops.Policy}

/-- Arbitrarily many ordinary uninitialized lets are extracted from the real
compiler, including each actual marker/snapshot allocator receipt. -/
theorem tree_of_flow
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ {scope fuel id node lowered},
      CompatibleExpressionReads.ScopeDeclarations source scope finalContext → CompatibleExpressionConstructors.Syntax source id →
      source.lookupExpression? id = some node → ExpressionHasType source finalContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      CompatibleExpressionConstructors.Tree readFuel values source finalContext solved reasonAt scope id lowered)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source finalContext context statements expected)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true selfReason = .ok code) :
    Tree layouts owner active frame globals onError readFuel values source finalContext solved reasonAt
      context scope statements expected type code := by
  induction syntaxTree generalizing scope fuel code with
  | body syntaxTree => exact .body (CompatibleStatements.tree_of_flow readPolicy (expressions declarations) syntaxTree projection accepted)
  | @uninitialized context nextContext id node binder rest expected found form declaration monomorphic extended ordinary remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨body, generated, accepted⟩ := bind_ok accepted
      simp only [SourceCoreSourceCells.letUninitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ :=
        CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      exact .uninitialized found form monomorphic extended ordinary (binder_projected (binderPolicy scope binder monomorphic ▸ projected))
        allocation annotation same (ih (scope_bind payload declarations declaration extended) projection generated)

/-- The complete production body wrapper keeps the extracted binding spine. -/
theorem tree_of_body
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ {scope fuel id node lowered},
      CompatibleExpressionReads.ScopeDeclarations source scope finalContext → CompatibleExpressionConstructors.Syntax source id →
      source.lookupExpression? id = some node → ExpressionHasType source finalContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      CompatibleExpressionConstructors.Tree readFuel values source finalContext solved reasonAt scope id lowered)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source finalContext context statements expected)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code) :
    ∃ flow, code = CompatibleStatements.finish type flow fellThrough escaped ∧
      Tree layouts owner active frame globals onError readFuel values source finalContext solved reasonAt
        context scope statements expected type flow := by
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, same⟩ := bind_ok accepted
  cases same
  exact ⟨flow, rfl, tree_of_flow readPolicy binderPolicy allocationPolicy expressions syntaxTree declarations projection generated⟩
/-- Production contextual expression extraction discharges the static child
callback. Scope extension uses authenticated raw declarations, not equality of
native projected types. -/
theorem tree_of_contextual_body
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel : Nat} {scope : Scope} {context : SourceSemantics.Context}
    (ordinary : CompatibleExpressionConstructors.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (closed : finalContext.typeVariables = []) (residual : finalContext.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (readExpression : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (readStatement : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (representationBinder : representation.expressions.lowerBinder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked)
    (lowerBinder : policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder representation locals compilation.owner [])
    (sourceCells : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (lowerExpression : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression program representation
      signatures locals parents assignments diagnostics compilation native parent skipInitializer)
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {fellThrough escaped : Word}
    (syntaxTree : Syntax source finalContext context statements expected)
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code) :
    ∃ flow, code = CompatibleStatements.finish type flow fellThrough escaped ∧
      Tree layouts owner active frame globals onError readFuel values source finalContext compilation.solvedRequirements reasonAt
        context scope statements expected type flow := by
  apply tree_of_body readStatement ?_ sourceCells ?_ syntaxTree declarations projection accepted
  · intro scope binder mono
    simp only [lowerBinder, SourceCoreGeneralFunctions.contextualBinder, mono, List.isEmpty_nil,
      ↓reduceIte, representationBinder]
  · intro currentScope budget id node lowered currentDeclarations syntaxValue found typed generated
    rw [lowerExpression] at generated
    exact CompatibleExpressionConstructors.tree_of_contextual ordinary unique closed residual currentDeclarations
      syntaxValue found typed readExpression lowerRead leafLowerer generated

end Solcore.SourceSemantics.CoreLowering.CompatibleStatementBindings
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleStatementBindingMeaning
/-! Real indexed allocation of ordinary uninitialized bindings, followed by a
concrete compatible statement tree. Administrative snapshots and markers stay
in the native heap, while exactly one source location is added per binding. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleStatementBindings
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedAllocationCompletion CoreProof

private theorem extended_eq {owner : Resolved.DeclarationId} {context left right : SourceSemantics.Context}
    {binder : TypedBinder} (first : BinderExtends owner context binder left)
    (second : BinderExtends owner context binder right) : left = right := by
  cases first; cases second; rfl

private theorem locals_allocate {owner : Resolved.DeclarationId} {context nextContext : SourceSemantics.Context}
    {binder : TypedBinder} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {location : Dynamic.Location}
    (extended : BinderExtends owner context binder nextContext) (mono : binder.scheme.quantified = [])
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body none location after) :
    Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) := by
  cases extended
  exact .cons allocated.reads_new rfl (.ordinary mono rfl) (locals.mono (.of_allocation allocated))

private theorem prepend {program : Program} {context nextContext finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment nextEnvironment : Dynamic.Environment}
    {before middle after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {binder : TypedBinder}
    {rest : List StatementId} {outcome : Dynamic.ControlOutcome}
    (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
    (head : Dynamic.StatementExecutes program context evidence source environment before id nextContext (.fallthrough nextEnvironment) middle)
    (tail : Dynamic.FunctionStatementsExecuteOutcome program nextContext evidence source nextEnvironment middle rest finalContext outcome after) :
    Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) finalContext outcome after := by
  cases rest with
  | nil => cases tail with
    | control executed => cases executed; exact .control (.singleton (lookupStatement?_sound found) (by intro expression; simp [form]) head)
    | fault failed => cases failed
  | cons => cases tail with
    | control executed => exact .control (.cons head executed)
    | fault failed => exact .fault (.tail head failed)

private theorem source_view {program : Program} {context nextContext finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {binder : TypedBinder}
    {rest : List StatementId} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder none) (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (trace : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) finalContext outcome after) :
    ∃ location middle, Dynamic.Heap.Allocates before binder.scheme.body none location middle ∧
      Dynamic.FunctionStatementsExecuteOutcome program nextContext evidence source ((binder.id, location) :: environment)
        middle rest finalContext outcome after := by
  have contains := lookupStatement?_sound found
  have notTail : true = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
    intro _ _ expression; simp [form]
  cases trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view true unique contains notTail executed with ⟨_, _, _, head, tail⟩ | ⟨head, terminal⟩
    · obtain ⟨extension, location, same, allocated⟩ := ScalarStatementViews.letUninitialized unique contains form head
      cases extended_eq extended extension
      cases same
      exact ⟨location, _, allocated, .control tail⟩
    · obtain ⟨_, _, same, _⟩ := ScalarStatementViews.letUninitialized unique contains form head
      cases same; cases terminal
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view true unique contains notTail failed with ⟨_, head⟩ | ⟨_, _, _, head, tail⟩
    · exact False.elim (ScalarStatementViews.letUninitialized_cannot_fault unique contains form mono head)
    · obtain ⟨extension, location, same, allocated⟩ := ScalarStatementViews.letUninitialized unique contains form head
      cases extended_eq extended extension
      cases same
      exact ⟨location, _, allocated, .fault tail⟩

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource} {finalContext : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}

include definitions registered in
/-- The complete marked allocation is derived from receipts and live lexical
slots. There is no initializer expression and no child evaluation premise. -/
private theorem allocate {context nextContext : SourceSemantics.Context} {scope : Scope} {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projection : values.checked.catalog.project binder.scheme.body = .ok payload)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (request source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (request source scope binder payload))
    (same : annotation.original = allocation.expression)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body none location after) :
    ∃ captured,
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inLeft payload .unit]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates actual store (annotation.expression.rename ξ) nextRef nextStore ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree ξ.lift (nextRef :: canonical) (nextRef :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: actual) (OptionalCell.referenceType payload :: actualContext) ambient.definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore := by
  have referenceAt : canonical[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals
      (request source scope binder payload)]? = some (.cellRef frame.type contextLocation) := by
    have named : SourceCoreCallableIndexedAllocationFrames.isNamedInput (request source scope binder payload) = false := ordinary
    change canonical[scope.length + (if SourceCoreCallableIndexedAllocationFrames.isNamedInput
      (request source scope binder payload) then 0 else 1) + globals]? = _
    rw [named]
    exact reference
  obtain ⟨captured, evaluated, nextHeaps, nextReference, preservation⟩ :=
    CallableIndexedOrdinaryAllocation.preserves allocation annotation same definitions registered environments
      (show EnvironmentsAgree Renaming.id canonical canonical from fun found => found) heaps referenceAt read
      (.absent rfl) (.uninitialized projection) allocated
  refine ⟨captured, CallableIndexedAllocationRenaming.transport allocation annotation same (Or.inl rfl) evaluated agrees,
    CallableIndexedOrdinaryAllocation.bind_environment environments nextReference,
    nextHeaps, locals_allocate extended mono locals allocated, agrees.lift _,
    .cons (.cellRef nextReference.typed) (actualTyped.weaken ⟨_, rfl⟩), ?_, ?_, preservation⟩
  · have index : ((binder.id, payload) :: scope).length + 1 + globals = (scope.length + 1 + globals) + 1 := by simp; omega
    rw [index]
    exact reference
  · exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp read).1).trans read

variable (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved finalContext evidence)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))

include definitions registered extension contextValid uninitialized in
/-- Every independent finite source trace through the binding prefix and its
concrete body is preserved under the real full native definition table. -/
theorem Tree.preserves [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source finalContext solved reasonAt
      context scope statements expected type code)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome} {resultContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (trace : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before statements resultContext outcome after) :
    resultContext = finalContext ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      CompatibleStatements.FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction tree generalizing mapping world environment canonical actual before after store ξ actualContext outcome resultContext with
  | body body => exact body.preserves functions extension program evidence contextValid unique uninitialized environments heaps locals agrees trace
  | @uninitialized context nextContext scope id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail ih =>
    obtain ⟨location, middle, allocated, tailTrace⟩ := source_view unique found form mono extended trace
    obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation⟩ :=
      allocate functions definitions registered mono extended ordinary projected allocation annotation same
        environments heaps locals agrees actualTyped reference read allocated
    obtain ⟨sameContext, value, finalStore, finalMap, finalWorld, completed, represented, finalHeaps, maps, worlds, finalFrame, metadata⟩ :=
      ih nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead tailTrace
    exact ⟨sameContext, value, finalStore, finalMap, finalWorld, .letE allocationEval completed, represented, finalHeaps,
      (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
      (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
      preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation allocated).trans metadata⟩

include definitions registered extension contextValid uninitialized in
/-- Reflection constructs the independent source allocations from a completed
native run; no prior source trace or child expression execution is supplied. -/
theorem Tree.reflects [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source finalContext solved reasonAt
      context scope statements expected type code)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before statements finalContext outcome after ∧
      CompatibleStatements.FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction tree generalizing mapping world environment canonical actual before store ξ actualContext with
  | body body => exact body.reflects functions extension program evidence contextValid uninitialized environments heaps locals agrees evaluated
  | @uninitialized context nextContext scope id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail ih =>
    obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation⟩ :=
      allocate functions definitions registered mono extended ordinary projected allocation annotation same
        environments heaps locals agrees actualTyped reference read Dynamic.Heap.Allocates.append
    have continuation := (ContinuationAgreement.letE allocationEval).unwrap evaluated
    obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, finalFrame, metadata⟩ :=
      ih nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead continuation
    exact ⟨outcome, after, finalMap, finalWorld,
      prepend found form (.letUninitialized (lookupStatement?_sound found) form mono extended .append) trace,
      represented, finalHeaps,
      (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
      (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
      preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans metadata⟩
private theorem finish_rename (type : Ty) (flow : Expr) (fellThrough escaped : Word) (ξ : Renaming) :
    (CompatibleStatements.finish type flow fellThrough escaped).rename ξ = CompatibleStatements.finish type (flow.rename ξ) fellThrough escaped := by
  unfold CompatibleStatements.finish
  split <;> simp [LocalControl.finish, LocalLoop.toControl, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.rename, Renaming.lift]

private theorem finish_from_flow {mapping : LocationMap} {world : StoreTyping}
    {environment : Environment} {before after : Store} {expected : TypeSystem.Ty} {type : Ty}
    {outcome : Dynamic.ControlOutcome} {flow : Expr} {value : Value}
    (fellThrough escaped : Word)
    (represented : CompatibleStatements.FlowRep (registry := registry) functions mapping world faults expected type outcome value)
    (evaluated : Evaluates environment before flow value after) :
    ∃ result, Evaluates environment before (CompatibleStatements.finish type flow fellThrough escaped) result after ∧
      CompatibleStatements.BodyRep (registry := registry) functions mapping world faults expected type outcome result := by
  cases represented with
  | fallthrough sourceEnvironment =>
    exact ⟨_, LocalControl.finish_fallthrough .unit (LocalLoop.toControl_normal _ escaped evaluated) (by simpa [LanguageResult.success, Expr.weakenAt] using (show Evaluates (.unit :: .inLeft .unit .unit :: environment) after (.inRight .word .unit) (.inRight .word .unit) after from .inRight .unit)) ,
      .fallthrough sourceEnvironment⟩
  | returned payload =>
    exact ⟨_, LocalControl.finish_returned _ (LocalLoop.toControl_normal _ escaped evaluated), .returned payload⟩
  | fault matched =>
    exact ⟨_, LocalControl.finish_failure _ (LocalLoop.toControl_failure _ escaped evaluated), .fault matched⟩

private theorem finish_input {environment : Environment} {before after : Store} {type : Ty}
    {flow : Expr} {fellThrough escaped : Word} {result : Value}
    (evaluated : Evaluates environment before (CompatibleStatements.finish type flow fellThrough escaped) result after) :
    ∃ value middle, Evaluates environment before flow value middle := by
  cases evaluated with
  | caseLeft control branch | caseRight control branch =>
    cases control with
    | caseLeft input branch | caseRight input branch => exact ⟨_, _, input⟩

include definitions registered extension contextValid uninitialized in
/-- Every independent finite source trace through the binding prefix and its
concrete body is preserved under the real full native definition table. -/
theorem Tree.body_preserves [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source finalContext solved reasonAt
      context scope statements expected type code)
    (fellThrough escaped : Word)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome} {resultContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (trace : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before statements resultContext outcome after) :
    resultContext = finalContext ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((CompatibleStatements.finish type code fellThrough escaped).rename ξ) value finalStore ∧
      CompatibleStatements.BodyRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨same, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    tree.preserves functions definitions registered extension program evidence contextValid uninitialized unique
      environments heaps locals agrees actualTyped reference read trace
  obtain ⟨result, completed, related⟩ := finish_from_flow functions fellThrough escaped represented evaluated
  exact ⟨same, result, finalStore, finalMap, finalWorld, by rw [finish_rename]; exact completed,
    related, finalHeaps, maps, worlds, frame, metadata⟩

include definitions registered extension contextValid uninitialized in
/-- Reflection constructs the independent source allocations from a completed
native run; no prior source trace or child expression execution is supplied. -/
theorem Tree.body_reflects [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source finalContext solved reasonAt
      context scope statements expected type code)
    (fellThrough escaped : Word)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (evaluated : Evaluates actual store ((CompatibleStatements.finish type code fellThrough escaped).rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before statements finalContext outcome after ∧
      CompatibleStatements.BodyRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  rw [finish_rename] at evaluated
  obtain ⟨flowValue, middleStore, flowEvaluation⟩ := finish_input evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    tree.reflects functions definitions registered extension program evidence contextValid uninitialized
      environments heaps locals agrees actualTyped reference read flowEvaluation
  obtain ⟨result, completed, related⟩ := finish_from_flow functions fellThrough escaped represented flowEvaluation
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated completed
  exact ⟨outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, frame, metadata⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleStatementBindings
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleStatementInitializedTree
/-! One ordinary initialized let before an authenticated binding sequence.
The initializer belongs to the old lexical context. The payload slot is an
administrative result binder, and the new source cell exists only on success. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleStatementInitialized
open Core Frontend SourceInference
abbrev Scope := SourceCoreLocalCell.Scope
abbrev ValuesContext := SourceCoreCompatibleValues.Context

def request (source : TypedSource) (scope : Scope) (binder : TypedBinder) (payload : Ty) :
    SourceCoreSourceCells.Request :=
  ⟨source, scope, Renaming.comp (Renaming.insertion 0) Renaming.id, binder, payload, some (.var 0)⟩

def sequence (type : Ty) (initializer allocation body : Expr) : Expr :=
  LanguageResult.bind (LocalLoop.controlType type) initializer (.letE allocation (body.weakenAt 1))

inductive Syntax (source : TypedSource) (context nextContext finalContext : SourceSemantics.Context)
    (id : StatementId) (rest : List StatementId) (expected : TypeSystem.Ty) : Prop where
  | initialized {node binder initializer initializerNode}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initializerTyped : ExpressionHasType source context initializer initializerNode.type)
      (initializerSyntax : CompatibleExpressionConstructors.Syntax source initializer)
      (remaining : CompatibleStatementBindings.Syntax source finalContext nextContext rest expected) :
      Syntax source context nextContext finalContext id rest expected

inductive Tree (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (readFuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context nextContext finalContext : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) (id : StatementId) (rest : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) : Expr → Prop where
  | initialized {node binder initializer initializerNode lowered body}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initial : CompatibleExpressionConstructors.Tree readFuel values source context solved reasonAt scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (request source scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (request source scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      (remaining : CompatibleStatementBindings.Tree layouts owner active frame globals onError readFuel values source
        finalContext solved reasonAt nextContext ((binder.id, lowered.type) :: scope) rest expected type body) :
      Tree layouts owner active frame globals onError readFuel values source context nextContext finalContext solved reasonAt
        scope id rest expected type (sequence type lowered.expression annotation.expression body)
end Solcore.SourceSemantics.CoreLowering.CompatibleStatementInitialized
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleStatementInitializedCertificates
/-! Static extraction follows the actual initialized-let branch. The accepted
initializer precedes its marked allocation; the tail scope receives the new
reference only after that initializer's successful result binder. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleStatementInitialized
open Core Frontend SourceInference
open CompatibleEncoding (bind_ok)

private theorem read_found {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
      simp only [found] at accepted
      obtain ⟨projected, _, same⟩ := bind_ok accepted
      cases same
      rfl

private theorem ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource}
  {context nextContext finalContext : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {policy : SourceCoreLoops.Policy}

/-- Actual successful lowering closes all allocator receipt obligations. The
remaining expression callbacks are static, separately discharged below. -/
theorem tree_of_flow
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ sourceContext, sourceContext = context ∨ sourceContext = finalContext →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      CompatibleExpressionConstructors.Syntax source id → source.lookupExpression? id = some node →
      ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      CompatibleExpressionConstructors.Tree readFuel values source sourceContext solved reasonAt scope id lowered)
    {scope : Scope} {id : StatementId} {rest : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context nextContext finalContext id rest expected)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope (id :: rest) type reasonAt true selfReason = .ok code) :
    Tree layouts owner active frame globals onError readFuel values source context nextContext finalContext solved reasonAt
      scope id rest expected type code := by
  cases syntaxTree with
  | @initialized node binder initializer initializerNode found form declaration mono extended ordinary initializerFound sourceType typed initializerSyntax remaining =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have identical := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := ensure_same checkedType
      subst payload
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      simp only [mono, List.isEmpty_nil, ↓reduceIte] at accepted
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      exact .initialized found form mono extended ordinary initializerFound sourceType
        (expressions context (.inl rfl) declarations initializerSyntax initializerFound typed generated)
        allocation annotation same
        (CompatibleStatementBindings.tree_of_flow readPolicy binderPolicy allocationPolicy (expressions finalContext (.inr rfl))
          remaining (CompatibleStatementBindings.scope_bind lowered.type declarations declaration extended) projection generatedBody)

/-- The production final-result wrapper preserves the extracted structure. -/
theorem tree_of_body
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ sourceContext, sourceContext = context ∨ sourceContext = finalContext →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      CompatibleExpressionConstructors.Syntax source id → source.lookupExpression? id = some node →
      ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      CompatibleExpressionConstructors.Tree readFuel values source sourceContext solved reasonAt scope id lowered)
    {scope : Scope} {id : StatementId} {rest : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context nextContext finalContext id rest expected)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope (id :: rest) type reasonAt fellThrough escaped = .ok code) :
    ∃ flow, code = CompatibleStatements.finish type flow fellThrough escaped ∧
      Tree layouts owner active frame globals onError readFuel values source context nextContext finalContext solved reasonAt
        scope id rest expected type flow := by
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, same⟩ := bind_ok accepted
  cases same
  exact ⟨flow, rfl, tree_of_flow readPolicy binderPolicy allocationPolicy expressions syntaxTree declarations projection generated⟩

/-- Exact contextual expression compilation closes both initializer and tail
static callbacks at their respective source lexical contexts. -/
theorem tree_of_contextual_body
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel : Nat} {scope : Scope}
    (ordinary : CompatibleExpressionConstructors.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (closed : ∀ sourceContext, sourceContext = context ∨ sourceContext = finalContext → sourceContext.typeVariables = [])
    (residual : ∀ sourceContext, sourceContext = context ∨ sourceContext = finalContext → sourceContext.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (readExpression : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (readStatement : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (representationBinder : representation.expressions.lowerBinder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked)
    (lowerBinder : policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder representation locals compilation.owner [])
    (sourceCells : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (lowerExpression : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression program representation
      signatures locals parents assignments diagnostics compilation native parent skipInitializer)
    {id : StatementId} {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {fellThrough escaped : Word}
    (syntaxTree : Syntax source context nextContext finalContext id rest expected)
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope (id :: rest) type reasonAt fellThrough escaped = .ok code) :
    ∃ flow, code = CompatibleStatements.finish type flow fellThrough escaped ∧
      Tree layouts owner active frame globals onError readFuel values source context nextContext finalContext compilation.solvedRequirements reasonAt
        scope id rest expected type flow := by
  apply tree_of_body readStatement ?_ sourceCells ?_ syntaxTree declarations projection accepted
  · intro scope binder mono
    simp only [lowerBinder, SourceCoreGeneralFunctions.contextualBinder, mono, List.isEmpty_nil,
      ↓reduceIte, representationBinder]
  · intro sourceContext reachable currentScope budget id node lowered currentDeclarations syntaxValue found typed generated
    rw [lowerExpression] at generated
    exact CompatibleExpressionConstructors.tree_of_contextual ordinary unique (closed _ reachable) (residual _ reachable) currentDeclarations
      syntaxValue found typed readExpression lowerRead leafLowerer generated
end Solcore.SourceSemantics.CoreLowering.CompatibleStatementInitialized
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleStatementInitializedMeaning
/-! Initialization runs in the old scope before any binder allocation. Its
failure keeps that context and its exact heap effects. Success creates the real
indexed marker/snapshot/payload prefix and then runs the certified tail. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleStatementInitialized
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedAllocationCompletion CoreProof

private theorem extended_eq {owner : Resolved.DeclarationId} {context left right : SourceSemantics.Context}
    {binder : TypedBinder} (first : BinderExtends owner context binder left)
    (second : BinderExtends owner context binder right) : left = right := by
  cases first; cases second; rfl

private theorem prepend {program : Program} {context nextContext finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment nextEnvironment : Dynamic.Environment}
    {before middle after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {binder : TypedBinder}
    {initializer : ExpressionId} {rest : List StatementId} {outcome : Dynamic.ControlOutcome}
    (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
    (head : Dynamic.StatementExecutes program context evidence source environment before id nextContext (.fallthrough nextEnvironment) middle)
    (tail : Dynamic.FunctionStatementsExecuteOutcome program nextContext evidence source nextEnvironment middle rest finalContext outcome after) :
    Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) finalContext outcome after := by
  cases rest with
  | nil => cases tail with
    | control executed => cases executed; exact .control (.singleton (lookupStatement?_sound found) (by intro expression; simp [form]) head)
    | fault failed => cases failed
  | cons => cases tail with
    | control executed => exact .control (.cons head executed)
    | fault failed => exact .fault (.tail head failed)

private theorem fault_intro {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {binder : TypedBinder} {initializer : ExpressionId}
    (rest : List StatementId) {reason : Dynamic.SemanticFault}
    (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
    (mono : binder.scheme.quantified = [])
    (failed : Dynamic.ExpressionFaults program context evidence source environment before initializer reason after) :
    Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) context (.fault reason) after := by
  have head := Dynamic.StatementFaults.letInitializer (lookupStatement?_sound found) form mono failed
  cases rest with
  | nil => exact .fault (.singleton head)
  | cons => exact .fault (.head head)

private theorem source_view {program : Program} {context nextContext finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {binder : TypedBinder}
    {initializer : ExpressionId} {rest : List StatementId} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder (some initializer)) (mono : binder.scheme.quantified = [])
    (extended : BinderExtends source.owner context binder nextContext)
    (trace : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) finalContext outcome after) :
    (∃ reason, finalContext = context ∧ outcome = .fault reason ∧
      Dynamic.ExpressionFaults program context evidence source environment before initializer reason after) ∨
    (∃ value location middle allocatedHeap,
      Dynamic.ExpressionEvaluates program context evidence source environment before initializer value middle ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location allocatedHeap ∧
      Dynamic.FunctionStatementsExecuteOutcome program nextContext evidence source ((binder.id, location) :: environment)
        allocatedHeap rest finalContext outcome after) := by
  have contains := lookupStatement?_sound found
  have notTail : true = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
    intro _ _ expression; simp [form]
  cases trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view true unique contains notTail executed with ⟨_, _, _, head, tail⟩ | ⟨head, terminal⟩
    · obtain ⟨extension, location, value, middle, same, initial, allocated⟩ := ScalarStatementViews.letInitialized unique contains form mono head
      cases extended_eq extended extension
      cases same
      exact .inr ⟨value, location, middle, _, initial, allocated, .control tail⟩
    · obtain ⟨_, _, _, _, same, _, _⟩ := ScalarStatementViews.letInitialized unique contains form mono head
      cases same; cases terminal
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view true unique contains notTail failed with ⟨same, head⟩ | ⟨_, _, _, head, tail⟩
    · exact .inl ⟨_, same, rfl, ScalarStatementViews.letInitialized_fault unique contains form mono head⟩
    · obtain ⟨extension, location, value, middle, same, initial, allocated⟩ := ScalarStatementViews.letInitialized unique contains form mono head
      cases extended_eq extended extension
      cases same
      exact .inr ⟨value, location, middle, _, initial, allocated, .fault tail⟩

private theorem sequence_rename (type : Ty) (initializer allocation body : Expr) (ξ : Renaming) :
    (sequence type initializer allocation body).rename ξ =
      LanguageResult.bind (LocalLoop.controlType type) (initializer.rename ξ)
        (.letE (allocation.rename ξ.lift) (body.rename (Renaming.comp (Renaming.insertion 0) ξ).lift)) := by
  rw [LoopStatements.rename_insert_lift]
  simp [sequence, LanguageResult.bind, Expr.rename, Renaming.lift, LoopRenaming.weakenOne]

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource}
  {context nextContext finalContext : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}

include definitions registered in
private theorem allocate {scope : Scope} {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (request source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (request source scope binder payload))
    (same : annotation.original = allocation.expression)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : ValueRep values.checked registry functions mapping world binder.scheme.body sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body (some sourceValue) location after) :
    ∃ captured,
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit value]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates (value :: actual) store (annotation.expression.rename ξ.lift) nextRef nextStore ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift (nextRef :: canonical) (nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: value :: actual)
        (OptionalCell.referenceType payload :: payload :: actualContext) ambient.definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore := by
  have canonicalLayout : EnvironmentsAgree (request source scope binder payload).references canonical (value :: canonical) := fun found => found
  have referenceAt : (value :: canonical)[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals
      (request source scope binder payload)]? = some (.cellRef frame.type contextLocation) := by
    have named : SourceCoreCallableIndexedAllocationFrames.isNamedInput (request source scope binder payload) = false := ordinary
    change (value :: canonical)[Renaming.comp (Renaming.insertion 0) Renaming.id
      (scope.length + (if SourceCoreCallableIndexedAllocationFrames.isNamedInput (request source scope binder payload) then 0 else 1) + globals)]? = _
    rw [named]
    exact reference
  obtain ⟨captured, evaluated, nextHeaps, nextReference, preservation⟩ :=
    CallableIndexedOrdinaryAllocation.preserves allocation annotation same definitions registered environments
      canonicalLayout heaps referenceAt read (.initialized rfl rfl) (.initialized represented) allocated
  have nextLocals : Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) := by
    cases extended
    exact .cons allocated.reads_new rfl (.ordinary mono rfl) (locals.mono (.of_allocation allocated))
  have inserted : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical (value :: actual) := fun found => agrees found
  refine ⟨captured, CallableIndexedAllocationRenaming.transport allocation annotation same (Or.inr rfl) evaluated (agrees.lift value),
    CallableIndexedOrdinaryAllocation.bind_environment environments nextReference, nextHeaps, nextLocals, inserted.lift _,
    .cons (.cellRef nextReference.typed) (.cons (represented.runtime_hasType.weaken ⟨_, rfl⟩) (actualTyped.weaken ⟨_, rfl⟩)), ?_, ?_, preservation⟩
  · have index : ((binder.id, payload) :: scope).length + 1 + globals = (scope.length + 1 + globals) + 1 := by simp; omega
    rw [index]
    exact reference
  · exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp read).1).trans read

variable (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (initialValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (finalValid : CompatibleExpressionLiterals.ContextValid solved finalContext evidence)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))

include definitions registered extension initialValid finalValid uninitialized in
/-- Initialization failure preserves its exact old-context effects. Success
allocates only afterward, then uses the concrete remaining binding tree. -/
theorem Tree.preserves [FunctionCalls.FaultTokens faults] {scope : Scope} {id : StatementId} {rest : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source context nextContext finalContext solved reasonAt
      scope id rest expected type code) (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome} {resultContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (trace : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) resultContext outcome after) :
    (resultContext = context ∨ resultContext = finalContext) ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      CompatibleStatements.FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  cases tree with
  | @initialized node binder initializer initializerNode lowered body found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining =>
    rw [sequence_rename]
    rcases source_view unique found form mono extended trace with ⟨reason, rfl, rfl, failed⟩ |
        ⟨sourceValue, location, middle, allocatedHeap, initialTrace, allocated, tailTrace⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, initialEval, represented, finalHeaps, maps, worlds, preservation, metadata⟩ :=
        CompatibleExpressionConstructors.preserves functions extension program evidence initialValid unique uninitialized initial initialFound
          environments heaps locals agrees (.fault failed)
      cases represented with
      | fault matched => exact ⟨.inl rfl, _, finalStore, finalMap, finalWorld, LanguageResult.bind_failure _ initialEval,
          .fault matched, finalHeaps, maps, worlds, preservation, metadata⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
        CompatibleExpressionConstructors.preserves functions extension program evidence initialValid unique uninitialized initial initialFound
          environments heaps locals agrees (.value initialTrace)
      cases represented with
      | value payload =>
        have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame⟩ :=
          allocate functions definitions registered mono extended ordinary allocation annotation same (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead allocated
        obtain ⟨sameContext, result, finalStore, finalMap, finalWorld, completed, related, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata⟩ :=
          remaining.preserves functions definitions registered extension program evidence finalValid uninitialized unique
            nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead tailTrace
        exact ⟨.inr sameContext, result, finalStore, finalMap, finalWorld,
          LanguageResult.bind_success _ initialEval (.letE allocationEval completed), related, finalHeaps,
          maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
          worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
          preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation allocated).trans finalMetadata)⟩

include definitions registered extension initialValid finalValid uninitialized in
/-- Every completed generated expression determines whether initialization
failed in the old scope or the allocated binding's tail ran in the new scope. -/
theorem Tree.reflects [FunctionCalls.FaultTokens faults] {scope : Scope} {id : StatementId} {rest : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source context nextContext finalContext solved reasonAt
      scope id rest expected type code)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ resultContext outcome after finalMap finalWorld,
      (resultContext = context ∨ resultContext = finalContext) ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) resultContext outcome after ∧
      CompatibleStatements.FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  cases tree with
  | @initialized node binder initializer initializerNode lowered body found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining =>
    rw [sequence_rename] at evaluated
    have input : ∃ input middle, Evaluates actual store (lowered.expression.rename ξ) input middle := by
      cases evaluated with
      | caseLeft initial branch | caseRight initial branch => exact ⟨_, _, initial⟩
    obtain ⟨input, middleStore, initialEval⟩ := input
    obtain ⟨sourceOutcome, middle, middleMap, middleWorld, initialTrace, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
      CompatibleExpressionConstructors.reflects functions extension program evidence initialValid uninitialized initial initialFound
        environments heaps locals agrees initialEval
    cases represented with
    | fault matched =>
      cases initialTrace with | fault failed =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LanguageResult.bind_failure _ initialEval)
        exact ⟨context, _, middle, middleMap, middleWorld, .inl rfl, fault_intro rest found form mono failed,
          .fault matched, middleHeaps, maps, worlds, preservation, metadata⟩
    | value payload =>
      cases initialTrace with | value initialTrace =>
        have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame⟩ :=
          allocate functions definitions registered mono extended ordinary allocation annotation same (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead .append
        have tailEval := (ContinuationAgreement.letE allocationEval).unwrap ((ContinuationAgreement.bind initialEval).unwrap evaluated)
        obtain ⟨outcome, after, finalMap, finalWorld, trace, related, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata⟩ :=
          remaining.reflects functions definitions registered extension program evidence finalValid uninitialized
            nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead tailEval
        exact ⟨finalContext, outcome, after, finalMap, finalWorld, .inr rfl,
          prepend found form (.letInitialized (lookupStatement?_sound found) form initialTrace mono extended .append) trace,
          related, finalHeaps,
          maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
          worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
          preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans finalMetadata)⟩
private theorem finish_rename (type : Ty) (flow : Expr) (fellThrough escaped : Word) (ξ : Renaming) :
    (CompatibleStatements.finish type flow fellThrough escaped).rename ξ = CompatibleStatements.finish type (flow.rename ξ) fellThrough escaped := by
  unfold CompatibleStatements.finish
  split <;> simp [LocalControl.finish, LocalLoop.toControl, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.rename, Renaming.lift]

private theorem finish_from_flow {mapping : LocationMap} {world : StoreTyping}
    {environment : Environment} {before after : Store} {expected : TypeSystem.Ty} {type : Ty}
    {outcome : Dynamic.ControlOutcome} {flow : Expr} {value : Value}
    (fellThrough escaped : Word)
    (represented : CompatibleStatements.FlowRep (registry := registry) functions mapping world faults expected type outcome value)
    (evaluated : Evaluates environment before flow value after) :
    ∃ result, Evaluates environment before (CompatibleStatements.finish type flow fellThrough escaped) result after ∧
      CompatibleStatements.BodyRep (registry := registry) functions mapping world faults expected type outcome result := by
  cases represented with
  | fallthrough sourceEnvironment =>
    exact ⟨_, LocalControl.finish_fallthrough .unit (LocalLoop.toControl_normal _ escaped evaluated) (by simpa [LanguageResult.success, Expr.weakenAt] using (show Evaluates (.unit :: .inLeft .unit .unit :: environment) after (.inRight .word .unit) (.inRight .word .unit) after from .inRight .unit)) ,
      .fallthrough sourceEnvironment⟩
  | returned payload =>
    exact ⟨_, LocalControl.finish_returned _ (LocalLoop.toControl_normal _ escaped evaluated), .returned payload⟩
  | fault matched =>
    exact ⟨_, LocalControl.finish_failure _ (LocalLoop.toControl_failure _ escaped evaluated), .fault matched⟩

private theorem finish_input {environment : Environment} {before after : Store} {type : Ty}
    {flow : Expr} {fellThrough escaped : Word} {result : Value}
    (evaluated : Evaluates environment before (CompatibleStatements.finish type flow fellThrough escaped) result after) :
    ∃ value middle, Evaluates environment before flow value middle := by
  cases evaluated with
  | caseLeft control branch | caseRight control branch =>
    cases control with
    | caseLeft input branch | caseRight input branch => exact ⟨_, _, input⟩

include definitions registered extension initialValid finalValid uninitialized in
/-- Initialization failure preserves its exact old-context effects. Success
allocates only afterward, then uses the concrete remaining binding tree. -/
theorem Tree.body_preserves [FunctionCalls.FaultTokens faults] {scope : Scope} {id : StatementId} {rest : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source context nextContext finalContext solved reasonAt
      scope id rest expected type code) (fellThrough escaped : Word) (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome} {resultContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (trace : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) resultContext outcome after) :
    (resultContext = context ∨ resultContext = finalContext) ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((CompatibleStatements.finish type code fellThrough escaped).rename ξ) value finalStore ∧
      CompatibleStatements.BodyRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨reached, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    tree.preserves functions definitions registered extension program evidence initialValid finalValid uninitialized unique
      environments heaps locals agrees actualTyped reference read unmapped trace
  obtain ⟨result, completed, related⟩ := finish_from_flow functions fellThrough escaped represented evaluated
  exact ⟨reached, result, finalStore, finalMap, finalWorld, by rw [finish_rename]; exact completed,
    related, finalHeaps, maps, worlds, frame, metadata⟩

include definitions registered extension initialValid finalValid uninitialized in
/-- Every completed generated expression determines whether initialization
failed in the old scope or the allocated binding's tail ran in the new scope. -/
theorem Tree.body_reflects [FunctionCalls.FaultTokens faults] {scope : Scope} {id : StatementId} {rest : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source context nextContext finalContext solved reasonAt
      scope id rest expected type code) (fellThrough escaped : Word)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store ((CompatibleStatements.finish type code fellThrough escaped).rename ξ) value finalStore) :
    ∃ resultContext outcome after finalMap finalWorld,
      (resultContext = context ∨ resultContext = finalContext) ∧
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) resultContext outcome after ∧
      CompatibleStatements.BodyRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  rw [finish_rename] at evaluated
  obtain ⟨flowValue, middleStore, flowEvaluation⟩ := finish_input evaluated
  obtain ⟨resultContext, outcome, after, finalMap, finalWorld, reached, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    tree.reflects functions definitions registered extension program evidence initialValid finalValid uninitialized
      environments heaps locals agrees actualTyped reference read unmapped flowEvaluation
  obtain ⟨result, completed, related⟩ := finish_from_flow functions fellThrough escaped represented flowEvaluation
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated completed
  exact ⟨resultContext, outcome, after, finalMap, finalWorld, reached, trace, related, finalHeaps, maps, worlds, frame, metadata⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleStatementInitialized
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleStatementMixedTree
/-! Arbitrarily mixed ordinary lexical bindings. Initializers belong to the
context before their binding; a failed initializer ends at that context. The
terminal fixed-scope statement tree closes every child semantic obligation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleStatementMixed
open Core Frontend SourceInference
abbrev Scope := SourceCoreLocalCell.Scope
abbrev ValuesContext := SourceCoreCompatibleValues.Context

abbrev absentRequest (source : TypedSource) (scope : Scope) (binder : TypedBinder) (payload : Ty) :
    SourceCoreSourceCells.Request := ⟨source, scope, Renaming.id, binder, payload, none⟩

abbrev initializedRequest := CompatibleStatementInitialized.request
abbrev sequence := CompatibleStatementInitialized.sequence

inductive Syntax (source : TypedSource) :
    SourceSemantics.Context → List StatementId → TypeSystem.Ty → Prop where
  | body {context statements expected} (syntaxTree : CompatibleStatements.Syntax source context statements expected) :
      Syntax source context statements expected
  | uninitialized {context nextContext id node binder rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : Syntax source nextContext rest expected) :
      Syntax source context (id :: rest) expected

  | initialized {context nextContext id node binder initializer initializerNode rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initializerTyped : ExpressionHasType source context initializer initializerNode.type)
      (initializerSyntax : CompatibleExpressionConstructors.Syntax source initializer)
      (remaining : Syntax source nextContext rest expected) :
      Syntax source context (id :: rest) expected

inductive Tree (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (readFuel : Nat) (values : ValuesContext) (source : TypedSource)
    (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) :
    SourceSemantics.Context → Scope → List StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | body {context scope statements expected type code}
      (body : CompatibleStatements.Tree readFuel values source context solved reasonAt scope statements expected type code) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt
        context scope statements expected type code
  | uninitialized {context nextContext scope id node binder rest expected type body payload}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (projected : values.checked.catalog.project binder.scheme.body = .ok payload)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
      (same : annotation.original = allocation.expression)
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt
        nextContext ((binder.id, payload) :: scope) rest expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt
        context scope (id :: rest) expected type (.letE annotation.expression body)
  | initialized {context nextContext scope id node binder initializer initializerNode lowered body rest expected type}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initial : CompatibleExpressionConstructors.Tree readFuel values source context solved reasonAt scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      (remaining : Tree layouts owner active frame globals onError readFuel values source
        solved reasonAt nextContext ((binder.id, lowered.type) :: scope) rest expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt
        context scope (id :: rest) expected type (sequence type lowered.expression annotation.expression body)

/-- The lexical environment at the actual stopping point, recording only the
bindings whose initializers completed and whose source cells were allocated. -/
inductive Reached (owner : Resolved.DeclarationId) :
    SourceSemantics.Context → Scope → Dynamic.Environment →
    SourceSemantics.Context → Scope → Dynamic.Environment → Prop where
  | here {context scope environment} : Reached owner context scope environment context scope environment
  | bind {context nextContext finalContext scope finalScope environment finalEnvironment binder payload location}
      (extended : BinderExtends owner context binder nextContext)
      (remaining : Reached owner nextContext ((binder.id, payload) :: scope) ((binder.id, location) :: environment)
        finalContext finalScope finalEnvironment) :
      Reached owner context scope environment finalContext finalScope finalEnvironment

end Solcore.SourceSemantics.CoreLowering.CompatibleStatementMixed
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleStatementMixedCertificates
/-! Successful production traversal extracts the marked binding spine. The
expression callback is static certificate extraction, never a runtime premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleStatementMixed
open Core Frontend SourceInference
open CompatibleEncoding (bind_ok)

private theorem read_found {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
      simp only [found] at accepted
      obtain ⟨projected, _, same⟩ := bind_ok accepted
      cases same
      rfl

open CompatibleStatementBindings (binder_projected scope_bind)

private theorem ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {policy : SourceCoreLoops.Policy}

/-- Arbitrarily mixed ordinary lets are extracted from the real
compiler, including each actual marker/snapshot allocator receipt. -/
theorem tree_of_flow
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → CompatibleExpressionConstructors.Syntax source id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      CompatibleExpressionConstructors.Tree readFuel values source sourceContext solved reasonAt scope id lowered)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context statements expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true selfReason = .ok code) :
    Tree layouts owner active frame globals onError readFuel values source solved reasonAt
      context scope statements expected type code := by
  induction syntaxTree generalizing scope fuel code with
  | body syntaxTree => exact .body (CompatibleStatements.tree_of_flow readPolicy (expressions _ closed residual declarations) syntaxTree projection accepted)
  | @uninitialized context nextContext id node binder rest expected found form declaration monomorphic extended ordinary remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨body, generated, accepted⟩ := bind_ok accepted
      simp only [SourceCoreSourceCells.letUninitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ :=
        CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      exact .uninitialized found form monomorphic extended ordinary (binder_projected (binderPolicy scope binder monomorphic ▸ projected))
        allocation annotation same (ih (by cases extended; exact closed) (by cases extended; exact residual)
          (scope_bind payload declarations declaration extended) projection generated)

  | @initialized context nextContext id node binder initializer initializerNode rest expected found form declaration mono extended ordinary initializerFound sourceType typed initializerSyntax remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have identical := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := ensure_same checkedType
      subst payload
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      simp only [mono, List.isEmpty_nil, ↓reduceIte] at accepted
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      exact .initialized found form mono extended ordinary initializerFound sourceType
        (expressions context closed residual declarations initializerSyntax initializerFound typed generated)
        allocation annotation same
        (ih (by cases extended; exact closed) (by cases extended; exact residual)
          (scope_bind lowered.type declarations declaration extended) projection generatedBody)

/-- The complete production body wrapper keeps the extracted binding spine. -/
theorem tree_of_body
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → CompatibleExpressionConstructors.Syntax source id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      CompatibleExpressionConstructors.Tree readFuel values source sourceContext solved reasonAt scope id lowered)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context statements expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code) :
    ∃ flow, code = CompatibleStatements.finish type flow fellThrough escaped ∧
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt
        context scope statements expected type flow := by
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, same⟩ := bind_ok accepted
  cases same
  exact ⟨flow, rfl, tree_of_flow readPolicy binderPolicy allocationPolicy expressions syntaxTree closed residual declarations projection generated⟩
/-- Production contextual expression extraction discharges the static child
callback. Scope extension uses authenticated raw declarations, not equality of
native projected types. -/
theorem tree_of_contextual_body
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel : Nat} {scope : Scope} {context : SourceSemantics.Context}
    (ordinary : CompatibleExpressionConstructors.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (readExpression : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (readStatement : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (representationBinder : representation.expressions.lowerBinder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked)
    (lowerBinder : policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder representation locals compilation.owner [])
    (sourceCells : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (lowerExpression : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression program representation
      signatures locals parents assignments diagnostics compilation native parent skipInitializer)
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {fellThrough escaped : Word}
    (syntaxTree : Syntax source context statements expected)
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code) :
    ∃ flow, code = CompatibleStatements.finish type flow fellThrough escaped ∧
      Tree layouts owner active frame globals onError readFuel values source compilation.solvedRequirements reasonAt
        context scope statements expected type flow := by
  apply tree_of_body readStatement ?_ sourceCells ?_ syntaxTree closed residual declarations projection accepted
  · intro scope binder mono
    simp only [lowerBinder, SourceCoreGeneralFunctions.contextualBinder, mono, List.isEmpty_nil,
      ↓reduceIte, representationBinder]
  · intro sourceContext contextClosed contextResidual currentScope budget id node lowered currentDeclarations syntaxValue found typed generated
    rw [lowerExpression] at generated
    exact CompatibleExpressionConstructors.tree_of_contextual ordinary unique contextClosed contextResidual currentDeclarations
      syntaxValue found typed readExpression lowerRead leafLowerer generated

end Solcore.SourceSemantics.CoreLowering.CompatibleStatementMixed
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleStatementMixedMeaning
/-! Mixed ordinary lexical prefixes preserve the actual stopping context.
Every child expression and terminal statement body is interpreted by its
concrete static tree, with no semantic child/body premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleStatementMixed
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedAllocationCompletion CoreProof

private theorem extended_eq {owner : Resolved.DeclarationId} {context left right : SourceSemantics.Context}
    {binder : TypedBinder} (first : BinderExtends owner context binder left)
    (second : BinderExtends owner context binder right) : left = right := by
  cases first; cases second; rfl

private theorem locals_allocate {owner : Resolved.DeclarationId} {context nextContext : SourceSemantics.Context}
    {binder : TypedBinder} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {location : Dynamic.Location}
    (extended : BinderExtends owner context binder nextContext) (mono : binder.scheme.quantified = [])
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body none location after) :
    Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) := by
  cases extended
  exact .cons allocated.reads_new rfl (.ordinary mono rfl) (locals.mono (.of_allocation allocated))

private theorem prepend_absent {program : Program} {context nextContext finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment nextEnvironment : Dynamic.Environment}
    {before middle after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {binder : TypedBinder}
    {rest : List StatementId} {outcome : Dynamic.ControlOutcome}
    (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
    (head : Dynamic.StatementExecutes program context evidence source environment before id nextContext (.fallthrough nextEnvironment) middle)
    (tail : Dynamic.FunctionStatementsExecuteOutcome program nextContext evidence source nextEnvironment middle rest finalContext outcome after) :
    Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) finalContext outcome after := by
  cases rest with
  | nil => cases tail with
    | control executed => cases executed; exact .control (.singleton (lookupStatement?_sound found) (by intro expression; simp [form]) head)
    | fault failed => cases failed
  | cons => cases tail with
    | control executed => exact .control (.cons head executed)
    | fault failed => exact .fault (.tail head failed)

private theorem source_view_absent {program : Program} {context nextContext finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {binder : TypedBinder}
    {rest : List StatementId} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder none) (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (trace : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) finalContext outcome after) :
    ∃ location middle, Dynamic.Heap.Allocates before binder.scheme.body none location middle ∧
      Dynamic.FunctionStatementsExecuteOutcome program nextContext evidence source ((binder.id, location) :: environment)
        middle rest finalContext outcome after := by
  have contains := lookupStatement?_sound found
  have notTail : true = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
    intro _ _ expression; simp [form]
  cases trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view true unique contains notTail executed with ⟨_, _, _, head, tail⟩ | ⟨head, terminal⟩
    · obtain ⟨extension, location, same, allocated⟩ := ScalarStatementViews.letUninitialized unique contains form head
      cases extended_eq extended extension
      cases same
      exact ⟨location, _, allocated, .control tail⟩
    · obtain ⟨_, _, same, _⟩ := ScalarStatementViews.letUninitialized unique contains form head
      cases same; cases terminal
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view true unique contains notTail failed with ⟨_, head⟩ | ⟨_, _, _, head, tail⟩
    · exact False.elim (ScalarStatementViews.letUninitialized_cannot_fault unique contains form mono head)
    · obtain ⟨extension, location, same, allocated⟩ := ScalarStatementViews.letUninitialized unique contains form head
      cases extended_eq extended extension
      cases same
      exact ⟨location, _, allocated, .fault tail⟩

private theorem prepend_initialized {program : Program} {context nextContext finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment nextEnvironment : Dynamic.Environment}
    {before middle after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {binder : TypedBinder}
    {initializer : ExpressionId} {rest : List StatementId} {outcome : Dynamic.ControlOutcome}
    (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
    (head : Dynamic.StatementExecutes program context evidence source environment before id nextContext (.fallthrough nextEnvironment) middle)
    (tail : Dynamic.FunctionStatementsExecuteOutcome program nextContext evidence source nextEnvironment middle rest finalContext outcome after) :
    Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) finalContext outcome after := by
  cases rest with
  | nil => cases tail with
    | control executed => cases executed; exact .control (.singleton (lookupStatement?_sound found) (by intro expression; simp [form]) head)
    | fault failed => cases failed
  | cons => cases tail with
    | control executed => exact .control (.cons head executed)
    | fault failed => exact .fault (.tail head failed)

private theorem fault_intro {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {binder : TypedBinder} {initializer : ExpressionId}
    (rest : List StatementId) {reason : Dynamic.SemanticFault}
    (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
    (mono : binder.scheme.quantified = [])
    (failed : Dynamic.ExpressionFaults program context evidence source environment before initializer reason after) :
    Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) context (.fault reason) after := by
  have head := Dynamic.StatementFaults.letInitializer (lookupStatement?_sound found) form mono failed
  cases rest with
  | nil => exact .fault (.singleton head)
  | cons => exact .fault (.head head)

private theorem source_view_initialized {program : Program} {context nextContext finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {node : StatementNode} {binder : TypedBinder}
    {initializer : ExpressionId} {rest : List StatementId} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder (some initializer)) (mono : binder.scheme.quantified = [])
    (extended : BinderExtends source.owner context binder nextContext)
    (trace : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before (id :: rest) finalContext outcome after) :
    (∃ reason, finalContext = context ∧ outcome = .fault reason ∧
      Dynamic.ExpressionFaults program context evidence source environment before initializer reason after) ∨
    (∃ value location middle allocatedHeap,
      Dynamic.ExpressionEvaluates program context evidence source environment before initializer value middle ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location allocatedHeap ∧
      Dynamic.FunctionStatementsExecuteOutcome program nextContext evidence source ((binder.id, location) :: environment)
        allocatedHeap rest finalContext outcome after) := by
  have contains := lookupStatement?_sound found
  have notTail : true = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
    intro _ _ expression; simp [form]
  cases trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view true unique contains notTail executed with ⟨_, _, _, head, tail⟩ | ⟨head, terminal⟩
    · obtain ⟨extension, location, value, middle, same, initial, allocated⟩ := ScalarStatementViews.letInitialized unique contains form mono head
      cases extended_eq extended extension
      cases same
      exact .inr ⟨value, location, middle, _, initial, allocated, .control tail⟩
    · obtain ⟨_, _, _, _, same, _, _⟩ := ScalarStatementViews.letInitialized unique contains form mono head
      cases same; cases terminal
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view true unique contains notTail failed with ⟨same, head⟩ | ⟨_, _, _, head, tail⟩
    · exact .inl ⟨_, same, rfl, ScalarStatementViews.letInitialized_fault unique contains form mono head⟩
    · obtain ⟨extension, location, value, middle, same, initial, allocated⟩ := ScalarStatementViews.letInitialized unique contains form mono head
      cases extended_eq extended extension
      cases same
      exact .inr ⟨value, location, middle, _, initial, allocated, .fault tail⟩

private theorem sequence_rename (type : Ty) (initializer allocation body : Expr) (ξ : Renaming) :
    (CompatibleStatementInitialized.sequence type initializer allocation body).rename ξ =
      LanguageResult.bind (LocalLoop.controlType type) (initializer.rename ξ)
        (.letE (allocation.rename ξ.lift) (body.rename (Renaming.comp (Renaming.insertion 0) ξ).lift)) := by
  rw [LoopStatements.rename_insert_lift]
  simp [CompatibleStatementInitialized.sequence, LanguageResult.bind, Expr.rename, Renaming.lift, LoopRenaming.weakenOne]

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}

include definitions registered in
/-- The complete marked allocation is derived from receipts and live lexical
slots. There is no initializer expression and no child evaluation premise. -/
private theorem allocate_absent {context nextContext : SourceSemantics.Context} {scope : Scope} {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projection : values.checked.catalog.project binder.scheme.body = .ok payload)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body none location after) :
    ∃ captured,
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inLeft payload .unit]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates actual store (annotation.expression.rename ξ) nextRef nextStore ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree ξ.lift (nextRef :: canonical) (nextRef :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: actual) (OptionalCell.referenceType payload :: actualContext) ambient.definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore := by
  have referenceAt : canonical[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals
      (absentRequest source scope binder payload)]? = some (.cellRef frame.type contextLocation) := by
    have named : SourceCoreCallableIndexedAllocationFrames.isNamedInput (absentRequest source scope binder payload) = false := ordinary
    change canonical[scope.length + (if SourceCoreCallableIndexedAllocationFrames.isNamedInput
      (absentRequest source scope binder payload) then 0 else 1) + globals]? = _
    rw [named]
    exact reference
  obtain ⟨captured, evaluated, nextHeaps, nextReference, preservation⟩ :=
    CallableIndexedOrdinaryAllocation.preserves allocation annotation same definitions registered environments
      (show EnvironmentsAgree Renaming.id canonical canonical from fun found => found) heaps referenceAt read
      (.absent rfl) (.uninitialized projection) allocated
  refine ⟨captured, CallableIndexedAllocationRenaming.transport allocation annotation same (Or.inl rfl) evaluated agrees,
    CallableIndexedOrdinaryAllocation.bind_environment environments nextReference,
    nextHeaps, locals_allocate extended mono locals allocated, agrees.lift _,
    .cons (.cellRef nextReference.typed) (actualTyped.weaken ⟨_, rfl⟩), ?_, ?_, preservation⟩
  · have index : ((binder.id, payload) :: scope).length + 1 + globals = (scope.length + 1 + globals) + 1 := by simp; omega
    rw [index]
    exact reference
  · exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp read).1).trans read

variable {context nextContext : SourceSemantics.Context}

include definitions registered in
private theorem allocate_initialized {scope : Scope} {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (initializedRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : ValueRep values.checked registry functions mapping world binder.scheme.body sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body (some sourceValue) location after) :
    ∃ captured,
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit value]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates (value :: actual) store (annotation.expression.rename ξ.lift) nextRef nextStore ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical) ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift (nextRef :: canonical) (nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: value :: actual)
        (OptionalCell.referenceType payload :: payload :: actualContext) ambient.definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore := by
  have canonicalLayout : EnvironmentsAgree (initializedRequest source scope binder payload).references canonical (value :: canonical) := fun found => found
  have referenceAt : (value :: canonical)[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals
      (initializedRequest source scope binder payload)]? = some (.cellRef frame.type contextLocation) := by
    have named : SourceCoreCallableIndexedAllocationFrames.isNamedInput (initializedRequest source scope binder payload) = false := ordinary
    change (value :: canonical)[Renaming.comp (Renaming.insertion 0) Renaming.id
      (scope.length + (if SourceCoreCallableIndexedAllocationFrames.isNamedInput (initializedRequest source scope binder payload) then 0 else 1) + globals)]? = _
    rw [named]
    exact reference
  obtain ⟨captured, evaluated, nextHeaps, nextReference, preservation⟩ :=
    CallableIndexedOrdinaryAllocation.preserves allocation annotation same definitions registered environments
      canonicalLayout heaps referenceAt read (.initialized rfl rfl) (.initialized represented) allocated
  have nextLocals : Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) := by
    cases extended
    exact .cons allocated.reads_new rfl (.ordinary mono rfl) (locals.mono (.of_allocation allocated))
  have inserted : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical (value :: actual) := fun found => agrees found
  refine ⟨captured, CallableIndexedAllocationRenaming.transport allocation annotation same (Or.inr rfl) evaluated (agrees.lift value),
    CallableIndexedOrdinaryAllocation.bind_environment environments nextReference, nextHeaps, nextLocals, inserted.lift _,
    .cons (.cellRef nextReference.typed) (.cons (represented.runtime_hasType.weaken ⟨_, rfl⟩) (actualTyped.weaken ⟨_, rfl⟩)), ?_, ?_, preservation⟩
  · have index : ((binder.id, payload) :: scope).length + 1 + globals = (scope.length + 1 + globals) + 1 := by simp; omega
    rw [index]
    exact reference
  · exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp read).1).trans read

/-- Lexical state at the last completed binding, before the terminal body or
failed initializer. The final heap still validates that source environment. -/
def LexicalResult (checked : SourceCoreCompatibleCatalog.Checked) (definitions : DataEnvironment)
    (mapping : LocationMap) (world : StoreTyping) (administrative : Core.Context)
    (owner : Resolved.DeclarationId) (context : SourceSemantics.Context) (scope : Scope)
    (environment : Dynamic.Environment) (resultContext : SourceSemantics.Context) (after : Dynamic.Heap) : Prop :=
  ∃ resultScope resultEnvironment canonical,
    Reached owner context scope environment resultContext resultScope resultEnvironment ∧
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative
      resultScope resultEnvironment canonical definitions ∧
    Dynamic.EnvironmentAgrees after resultContext.locals resultEnvironment

private theorem LexicalResult.bind {checked : SourceCoreCompatibleCatalog.Checked} {definitions : DataEnvironment}
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {owner : Resolved.DeclarationId} {context nextContext resultContext : SourceSemantics.Context}
    {scope : Scope} {environment : Dynamic.Environment} {after : Dynamic.Heap} {binder : TypedBinder} {payload : Ty}
    {location : Dynamic.Location}
    (extended : BinderExtends owner context binder nextContext)
    (result : LexicalResult checked definitions mapping world administrative owner nextContext
      ((binder.id, payload) :: scope) ((binder.id, location) :: environment) resultContext after) :
    LexicalResult checked definitions mapping world administrative owner context scope environment resultContext after := by
  obtain ⟨resultScope, resultEnvironment, canonical, reached, environments, locals⟩ := result
  exact ⟨resultScope, resultEnvironment, canonical, .bind extended reached, environments, locals⟩

private theorem valid_extend {solved : List SolvedRequirement} {evidence : Dynamic.EvidenceEnvironment}
    {owner : Resolved.DeclarationId} {context nextContext : SourceSemantics.Context} {binder : TypedBinder}
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (extended : BinderExtends owner context binder nextContext) :
    CompatibleExpressionLiterals.ContextValid solved nextContext evidence := by
  cases extended
  exact ⟨valid.ledger, valid.valid.transport rfl rfl rfl, valid.covers⟩

variable (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))

include definitions registered extension uninitialized in
/-- Every independent finite source trace through the binding prefix and its
concrete body is preserved under the real full native definition table. -/
theorem Tree.preserves [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt
      context scope statements expected type code)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome} {resultContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (trace : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before statements resultContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      CompatibleStatements.FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  induction tree generalizing mapping world environment canonical actual before after store ξ actualContext outcome resultContext with
  | body body =>
    obtain ⟨rfl, value, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, preservation, metadata⟩ :=
      body.preserves functions extension program evidence contextValid unique uninitialized environments heaps locals agrees trace
    exact ⟨value, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, preservation, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  | @uninitialized context nextContext scope id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail ih =>
    obtain ⟨location, middle, allocated, tailTrace⟩ := source_view_absent unique found form mono extended trace
    obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation⟩ :=
      allocate_absent functions definitions registered mono extended ordinary projected allocation annotation same
        environments heaps locals agrees actualTyped reference read allocated
    obtain ⟨value, finalStore, finalMap, finalWorld, completed, represented, finalHeaps, maps, worlds, finalFrame, metadata, lexical⟩ :=
      ih (valid_extend contextValid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
        (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 tailTrace
    exact ⟨value, finalStore, finalMap, finalWorld, .letE allocationEval completed, represented, finalHeaps,
      (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
      (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
      preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation allocated).trans metadata, lexical.bind extended⟩
  | @initialized context nextContext scope id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining ih =>
    rw [sequence_rename]
    rcases source_view_initialized unique found form mono extended trace with ⟨reason, rfl, rfl, failed⟩ |
        ⟨sourceValue, location, middle, allocatedHeap, initialTrace, allocated, tailTrace⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, initialEval, represented, finalHeaps, maps, worlds, preservation, metadata⟩ :=
        CompatibleExpressionConstructors.preserves functions extension program evidence contextValid unique uninitialized initial initialFound
          environments heaps locals agrees (.fault failed)
      cases represented with
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LanguageResult.bind_failure _ initialEval,
          .fault matched, finalHeaps, maps, worlds, preservation, metadata, _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
        CompatibleExpressionConstructors.preserves functions extension program evidence contextValid unique uninitialized initial initialFound
          environments heaps locals agrees (.value initialTrace)
      cases represented with
      | value payload =>
        have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame⟩ :=
          allocate_initialized functions definitions registered mono extended ordinary allocation annotation same (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead allocated
        obtain ⟨result, finalStore, finalMap, finalWorld, completed, related, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, lexical⟩ :=
          ih (valid_extend contextValid extended)
            nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1 tailTrace
        exact ⟨result, finalStore, finalMap, finalWorld,
          LanguageResult.bind_success _ initialEval (.letE allocationEval completed), related, finalHeaps,
          maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
          worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
          preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation allocated).trans finalMetadata), lexical.bind extended⟩
include definitions registered extension uninitialized in
/-- Reflection constructs the independent source allocations from a completed
native run; no prior source trace or child expression execution is supplied. -/
theorem Tree.reflects [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt
      context scope statements expected type code)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ resultContext outcome after finalMap finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before statements resultContext outcome after ∧
      CompatibleStatements.FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  induction tree generalizing mapping world environment canonical actual before store ξ actualContext with
  | body body =>
    obtain ⟨outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata⟩ :=
      body.reflects functions extension program evidence contextValid uninitialized environments heaps locals agrees evaluated
    exact ⟨_, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata,
      _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  | @uninitialized context nextContext scope id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail ih =>
    obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation⟩ :=
      allocate_absent functions definitions registered mono extended ordinary projected allocation annotation same
        environments heaps locals agrees actualTyped reference read Dynamic.Heap.Allocates.append
    have continuation := (ContinuationAgreement.letE allocationEval).unwrap evaluated
    obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, finalFrame, metadata, lexical⟩ :=
      ih (valid_extend contextValid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
        (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 continuation
    exact ⟨resultContext, outcome, after, finalMap, finalWorld,
      prepend_absent found form (.letUninitialized (lookupStatement?_sound found) form mono extended .append) trace,
      represented, finalHeaps,
      (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
      (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
      preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans metadata, lexical.bind extended⟩
  | @initialized context nextContext scope id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining ih =>
    rw [sequence_rename] at evaluated
    have input : ∃ input middle, Evaluates actual store (lowered.expression.rename ξ) input middle := by
      cases evaluated with
      | caseLeft initial branch | caseRight initial branch => exact ⟨_, _, initial⟩
    obtain ⟨input, middleStore, initialEval⟩ := input
    obtain ⟨sourceOutcome, middle, middleMap, middleWorld, initialTrace, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
      CompatibleExpressionConstructors.reflects functions extension program evidence contextValid uninitialized initial initialFound
        environments heaps locals agrees initialEval
    cases represented with
    | fault matched =>
      cases initialTrace with | fault failed =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LanguageResult.bind_failure _ initialEval)
        exact ⟨context, _, middle, middleMap, middleWorld, fault_intro rest found form mono failed,
          .fault matched, middleHeaps, maps, worlds, preservation, metadata, _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    | value payload =>
      cases initialTrace with | value initialTrace =>
        have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame⟩ :=
          allocate_initialized functions definitions registered mono extended ordinary allocation annotation same (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead .append
        have tailEval := (ContinuationAgreement.letE allocationEval).unwrap ((ContinuationAgreement.bind initialEval).unwrap evaluated)
        obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, lexical⟩ :=
          ih (valid_extend contextValid extended)
            nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1 tailEval
        exact ⟨resultContext, outcome, after, finalMap, finalWorld,
          prepend_initialized found form (.letInitialized (lookupStatement?_sound found) form initialTrace mono extended .append) trace,
          related, finalHeaps,
          maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
          worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
          preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans finalMetadata), lexical.bind extended⟩
private theorem finish_rename (type : Ty) (flow : Expr) (fellThrough escaped : Word) (ξ : Renaming) :
    (CompatibleStatements.finish type flow fellThrough escaped).rename ξ = CompatibleStatements.finish type (flow.rename ξ) fellThrough escaped := by
  unfold CompatibleStatements.finish
  split <;> simp [LocalControl.finish, LocalLoop.toControl, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.rename, Renaming.lift]

private theorem finish_from_flow {mapping : LocationMap} {world : StoreTyping}
    {environment : Environment} {before after : Store} {expected : TypeSystem.Ty} {type : Ty}
    {outcome : Dynamic.ControlOutcome} {flow : Expr} {value : Value}
    (fellThrough escaped : Word)
    (represented : CompatibleStatements.FlowRep (registry := registry) functions mapping world faults expected type outcome value)
    (evaluated : Evaluates environment before flow value after) :
    ∃ result, Evaluates environment before (CompatibleStatements.finish type flow fellThrough escaped) result after ∧
      CompatibleStatements.BodyRep (registry := registry) functions mapping world faults expected type outcome result := by
  cases represented with
  | fallthrough sourceEnvironment =>
    exact ⟨_, LocalControl.finish_fallthrough .unit (LocalLoop.toControl_normal _ escaped evaluated) (by simpa [LanguageResult.success, Expr.weakenAt] using (show Evaluates (.unit :: .inLeft .unit .unit :: environment) after (.inRight .word .unit) (.inRight .word .unit) after from .inRight .unit)) ,
      .fallthrough sourceEnvironment⟩
  | returned payload =>
    exact ⟨_, LocalControl.finish_returned _ (LocalLoop.toControl_normal _ escaped evaluated), .returned payload⟩
  | fault matched =>
    exact ⟨_, LocalControl.finish_failure _ (LocalLoop.toControl_failure _ escaped evaluated), .fault matched⟩

private theorem finish_input {environment : Environment} {before after : Store} {type : Ty}
    {flow : Expr} {fellThrough escaped : Word} {result : Value}
    (evaluated : Evaluates environment before (CompatibleStatements.finish type flow fellThrough escaped) result after) :
    ∃ value middle, Evaluates environment before flow value middle := by
  cases evaluated with
  | caseLeft control branch | caseRight control branch =>
    cases control with
    | caseLeft input branch | caseRight input branch => exact ⟨_, _, input⟩

include definitions registered extension uninitialized in
/-- Initialization failure preserves its exact old-context effects. Success
allocates only afterward, then uses the concrete remaining binding tree. -/
theorem Tree.body_preserves [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt
      context scope statements expected type code)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence) (fellThrough escaped : Word) (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome} {resultContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (trace : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before statements resultContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((CompatibleStatements.finish type code fellThrough escaped).rename ξ) value finalStore ∧
      CompatibleStatements.BodyRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    tree.preserves functions definitions registered extension program evidence uninitialized contextValid unique
      environments heaps locals agrees actualTyped reference read unmapped trace
  obtain ⟨result, completed, related⟩ := finish_from_flow functions fellThrough escaped represented evaluated
  exact ⟨result, finalStore, finalMap, finalWorld, by rw [finish_rename]; exact completed,
    related, finalHeaps, maps, worlds, frame, metadata, lexical⟩

include definitions registered extension uninitialized in
/-- Every completed generated expression determines whether initialization
failed in the old scope or the allocated binding's tail ran in the new scope. -/
theorem Tree.body_reflects [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt
      context scope statements expected type code)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence) (fellThrough escaped : Word)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store ((CompatibleStatements.finish type code fellThrough escaped).rename ξ) value finalStore) :
    ∃ resultContext outcome after finalMap finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before statements resultContext outcome after ∧
      CompatibleStatements.BodyRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  rw [finish_rename] at evaluated
  obtain ⟨flowValue, middleStore, flowEvaluation⟩ := finish_input evaluated
  obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    tree.reflects functions definitions registered extension program evidence uninitialized contextValid
      environments heaps locals agrees actualTyped reference read unmapped flowEvaluation
  obtain ⟨result, completed, related⟩ := finish_from_flow functions fellThrough escaped represented flowEvaluation
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated completed
  exact ⟨resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, frame, metadata, lexical⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleStatementMixed
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndexLookup
/-! General mapping keys use the existing prepared comparator. Full payloads
supply structural equality observations; callable leaves separately authenticate
identities. The actual captured environment remains typed throughout allocation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndex
open Core Frontend CompatiblePayload CompatibleMapping CompatibleEquality DataEquality
open GeneralHeap ReadOnly CompatibleExpressionPrimitives

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping}

private theorem observed_entries (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    {identities : Dynamic.Value → Word → Prop}
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    {keyType valueType : Ty} (projected : keyType = prepared.type)
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)} {entries : OrderedMapping.Entries}
    (related : EntriesRep checked registry functions mapping world sourceKey sourceValue sources entries keyType valueType) :
    CoreLowering.OrderedMapping.EntriesRel (CompatibleMappingComparison.KeyRep prepared registry identities)
      (Payload registry functions mapping world sourceValue valueType) sources entries := by
  subst keyType
  induction sources generalizing entries with
  | nil => cases related; exact .nil
  | cons head tail ih => cases related with
    | entry key value rest => exact .cons (CompatibleEquality.ValueRep.observation functionLeaves key) value (ih rest)

/-- Finite lookup for every represented key type, using actual prepared code. -/
theorem lookup_meaning (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    {layout : Core.OrderedMapping.Layout} (keyType : layout.keyType = prepared.type)
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {header : Word} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header layout entries fallback)
    {sourceLookup : Dynamic.Value} {key : Value}
    (keyRep : Payload registry functions mapping world sourceKey layout.keyType sourceLookup key)
    (environment : Environment) (store : Store) (missingBase : Word) (mappingExpression keyExpression : Expr)
    (mappingSelected : Selects environment mappingExpression (Transport.carrier header fallback layout entries))
    (keySelected : Selects environment keyExpression key) :
    ∃ result, ReadResult checked registry functions mapping world sourceValue sourceLookup sources layout.valueType missingBase header result ∧
      Evaluates environment store (SourceCoreMappingWithDefault.lookup layout missingBase prepared.expression mappingExpression keyExpression) result
        (Transport.lookupStore prepared layout environment store header fallback entries key) := by
  obtain ⟨equal, correct⟩ := CompatibleMappingComparison.exists_predicate_correct prepared registry faithful
  have fullCorrect : CoreLowering.OrderedMapping.KeyEqualityCorrect (Payload registry functions mapping world sourceKey layout.keyType) equal := by
    refine ⟨fun left right => correct.equivalent ?_ ?_⟩
    · simpa only [keyType] using CompatibleEquality.ValueRep.observation functionLeaves left
    · simpa only [keyType] using CompatibleEquality.ValueRep.observation functionLeaves right
  have observed : CompatibleMappingComparison.KeyRep prepared registry identities sourceLookup key := by
    simpa only [keyType] using CompatibleEquality.ValueRep.observation functionLeaves keyRep
  have evaluated := Transport.lookup_evaluates prepared layout keyType faithful equal correct observed
    (observed_entries prepared functionLeaves keyType fields.stored) environment store missingBase header fallback
    mappingExpression keyExpression mappingSelected keySelected
  obtain ⟨found, sourceLookup⟩ := lookup_total sourceLookup sources
  cases sourceLookup with
  | found found =>
    obtain ⟨value, located, represented⟩ := lookup_preserves fullCorrect keyRep fields.stored found
    exact ⟨_, .found found represented, by simpa only [located, SourceCoreMappingWithDefault.selectedValue, Option.or] using evaluated⟩
  | absent absent =>
    have missing := CoreLowering.OrderedMapping.absent_related fullCorrect keyRep (entries_related fields.stored) absent
    rw [missing] at evaluated
    cases fields.default with
    | absent noDefault projected wf => exact ⟨_, .missing absent noDefault, evaluated⟩
    | present defaulted represented => exact ⟨_, .default absent defaulted represented, evaluated⟩

private theorem closed_hasType {expression : Expr} {type : Ty} {definitions : DataEnvironment}
    (typed : HasType [] expression type definitions) (context : Core.Context) : HasType context expression type definitions := by
  have extended := typed.rename (mapping := Renaming.id) (target := context) (by intro index type found; cases found)
  simpa using extended

/-- Comparator closure allocations preserve the source heap and every existing
administrative cell. The captured actual slots must all be typed. -/
theorem lookup_preserves_heap (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    {layout : Core.OrderedMapping.Layout} (keyType : layout.keyType = prepared.type)
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {header : Word} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header layout entries fallback)
    {sourceLookup : Dynamic.Value} {key : Value}
    (keyRep : Payload registry functions mapping world sourceKey layout.keyType sourceLookup key)
    {environment : Environment} {context : Core.Context} {heap : Dynamic.Heap} {store : Store}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked registry functions mapping world heap store)
    (missingBase : Word) :
    ∃ result finalStore futureWorld,
      ReadResult checked registry functions mapping futureWorld sourceValue sourceLookup sources layout.valueType missingBase header result ∧
      Evaluates (key :: Transport.carrier header fallback layout entries :: environment) store
        (SourceCoreMappingWithDefault.lookup layout missingBase prepared.expression (.var 1) (.var 0)) result finalStore ∧
      CompatibleAmbientHeap.HeapRepresents checked registry functions mapping futureWorld heap finalStore ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping finalStore := by
  obtain ⟨result, meaning, evaluated⟩ := lookup_meaning prepared faithful functionLeaves keyType fields keyRep
    (key :: Transport.carrier header fallback layout entries :: environment) store missingBase (.var 1) (.var 0) (.var rfl) (.var rfl)
  have nativeTyped := fields.represents.runtime_hasType
  have actualTyped := RuntimeEnvironmentHasTypes.cons keyRep.runtime_hasType (.cons nativeTyped environmentTyped)
  have helperTyped : HasType (layout.keyType :: SourceCoreMappingWithDefault.type layout :: context)
      (SourceCoreMappingWithDefault.lookup layout missingBase prepared.expression (.var 1) (.var 0))
      (LanguageResult.resultType layout.valueType) ambient.definitions := by
    apply SourceCoreMappingWithDefault.lookup_hasType missingBase (fields.registered.extend_definitions ambient.basePrefix)
    · simpa only [Core.OrderedMapping.Layout.comparisonType, SourceCoreCompatibleDataEquality.comparatorType, SourceCoreDataEquality.comparatorType, keyType] using closed_hasType (prepared.typed.extend_definitions ambient.basePrefix) _
    · exact .var rfl
    · exact .var rfl
  obtain ⟨suffix, appended, _⟩ := Transport.lookupStore_extension prepared layout
    (key :: Transport.carrier header fallback layout entries :: environment) store header fallback entries key
  obtain ⟨futureWorld, extension, futureHeaps, resultTyped, unchanged⟩ :=
    DataMappingHeap.evaluation_preserves_frame heaps actualTyped helperTyped evaluated appended
  exact ⟨result, _, futureWorld, CompatibleExpressionIndices.extend_read_result meaning extension, evaluated, futureHeaps, extension, unchanged⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndex
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndexTerminal
/-! General index decisions retain the source mapping metadata. Callable type
views and identity observations are supplied by the function model, independently
of native type projection. No extra Core instruction is needed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndex
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleMapping
open CompatibleExpressionIndices

/-- The final helper creates a source decision and typed administrative suffix.
The key guard follows retained raw types and the authenticated function model. -/
theorem finish_with_diagnostics {values : ValuesContext} {source : TypedSource} {id base : ExpressionId}
    {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
    (header : Header values source id base node baseNode layout comparison first second)
    (sourceType : baseNode.type = .mapping keyNode.type node.type)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {functions : FunctionModel values.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop}
    (faithful : DataEquality.IdentityFaithful identities)
    (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
    (functionTypes : FunctionRuntimeViews functions)
    {baseSource keySource : Dynamic.Value} {baseValue keyValue : Value}
    (baseRep : ValueRep values.checked registry functions mapping world baseNode.type baseSource baseValue first.type)
    (keyRep : ValueRep values.checked registry functions mapping world keyNode.type keySource keyValue second.type)
    {environment : Environment} {context : Core.Context} {heap : Dynamic.Heap} {store : Store}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store)
    (reason : Word) {faults : FunctionCalls.FaultRep}
    (missing : MissingPolicy (keyNode := keyNode) (registry := registry) header functions mapping world
      baseSource keySource baseValue reason faults) :
    ∃ outcome result finalStore futureWorld,
      Terminal baseSource keySource outcome ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        mapping futureWorld node.type layout.valueType faults outcome result ∧
      Evaluates (keyValue :: baseValue :: environment) store
        (SourceCoreMappingWithDefault.lookup layout reason comparison.expression (.var 1) (.var 0)) result finalStore ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping futureWorld heap finalStore ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping finalStore ∧
      (∀ other, Terminal baseSource keySource other → other = outcome) := by
  obtain ⟨rawKey, rawValue, sources, rfl⟩ := source_mapping baseRep (by rw [sourceType]; rfl)
  obtain ⟨tag, nativeEntries, fallback, rfl, keyView, valueView, fields⟩ := header.mapping_fields sourceType baseRep
  have keyTyped : Dynamic.ValueRuntimeTypeMatches keySource rawKey := by
    cases keyRep.source_runtimeView functionTypes with
    | intro typed view =>
      exact .intro typed (view.trans (runtimeType_eq_of_metadata keyView))
  have nativeKey : Payload registry functions mapping world rawKey layout.keyType keySource keyValue :=
    .compatible keyView.symm (header.keyType ▸ keyRep)
  obtain ⟨result, finalStore, futureWorld, resultMeaning, evaluated, finalHeaps, worlds, frame⟩ :=
    lookup_preserves_heap comparison faithful functionLeaves header.comparisonType fields nativeKey environmentTyped heaps reason
  have outcome : ∃ outcome, Terminal (.mapping rawKey rawValue sources) keySource outcome ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        mapping futureWorld node.type layout.valueType faults outcome result := by
    cases resultMeaning with
    | found located represented => exact ⟨_, .found rfl located, .value (.compatible valueView represented)⟩
    | default absent defaulted represented => exact ⟨_, .default rfl absent defaulted, .value (.compatible valueView represented)⟩
    | missing absent unavailable => exact ⟨_, .unavailable rfl keyTyped absent unavailable, .fault (missing rawKey rawValue sources tag nativeEntries fallback
        ⟨lookupExpression?_sound header.metadata.found, lookupExpression?_sound header.baseMetadata.found,
          sourceType, rfl, rfl, keyView, valueView, fields, keyTyped, absent, unavailable⟩)⟩
  obtain ⟨outcome, terminal, represented⟩ := outcome
  exact ⟨outcome, result, finalStore, futureWorld, terminal, represented, evaluated, finalHeaps, worlds, frame,
    fun _ other => other.functional keyTyped terminal⟩

/-- The original uniform inclusion supplies the policy at its actual witness. -/
theorem finish {values : ValuesContext} {source : TypedSource} {id base : ExpressionId}
    {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
    (header : Header values source id base node baseNode layout comparison first second)
    (sourceType : baseNode.type = .mapping keyNode.type node.type)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {functions : FunctionModel values.checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop}
    (faithful : DataEquality.IdentityFaithful identities)
    (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
    (functionTypes : FunctionRuntimeViews functions)
    {baseSource keySource : Dynamic.Value} {baseValue keyValue : Value}
    (baseRep : ValueRep values.checked registry functions mapping world baseNode.type baseSource baseValue first.type)
    (keyRep : ValueRep values.checked registry functions mapping world keyNode.type keySource keyValue second.type)
    {environment : Environment} {context : Core.Context} {heap : Dynamic.Heap} {store : Store}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store)
    (reason : Word) {faults : FunctionCalls.FaultRep}
    (missing : ∀ key value tag, MetadataRep registry (.mapping key value) tag → faults (.missingMappingDefault value) (reason.add tag)) :
    ∃ outcome result finalStore futureWorld,
      Terminal baseSource keySource outcome ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        mapping futureWorld node.type layout.valueType faults outcome result ∧
      Evaluates (keyValue :: baseValue :: environment) store
        (SourceCoreMappingWithDefault.lookup layout reason comparison.expression (.var 1) (.var 0)) result finalStore ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping futureWorld heap finalStore ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping finalStore ∧
      (∀ other, Terminal baseSource keySource other → other = outcome) := by
  exact finish_with_diagnostics header sourceType faithful functionLeaves functionTypes baseRep keyRep
    environmentTyped heaps reason (fun _ _ _ _ _ _ witness => missing _ _ _ witness.fields.metadata)

end Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndex
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleNamedBodyCertificates
/-! Static receipts for the ordinary fixed-scope named-body fragment. A receipt
retains the actual production traversal equation and its extracted statement
tree at one source context. It contains no body execution or semantic induction
hypothesis. Context/evidence validity remains a separate static obligation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleNamedBody
open Core Frontend SourceInference

structure Certificate (readFuel : Nat) (values : SourceCoreCompatibleValues.Context)
    (source : TypedSource) (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty)
    (policy : SourceCoreLoops.Policy) (fuel : Nat) (fellThrough escaped : Word) (code : Expr) where private mk ::
  accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements
    type reasonAt fellThrough escaped = .ok code
  flow : Expr
  emitted : code = CompatibleStatements.finish type flow fellThrough escaped
  tree : CompatibleStatements.Tree readFuel values source context solved reasonAt scope
    statements expected type flow

/-- Extract the body tree from the actual contextual compiler. Every remaining
premise concerns source syntax, typing, context, or a production policy field. -/
theorem of_contextual
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {policy : SourceCoreLoops.Policy}
    (ordinary : CompatibleExpressionConstructors.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (readExpression : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (readStatement : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (lowerExpression : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression program representation
      signatures locals parents assignments diagnostics compilation native parent skipInitializer)
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {fellThrough escaped : Word}
    (syntaxTree : CompatibleStatements.Syntax source context statements expected)
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code) :
    Nonempty (Certificate readFuel values source context compilation.solvedRequirements reasonAt scope
      statements expected type policy fuel fellThrough escaped code) := by
  obtain ⟨flow, emitted, tree⟩ := CompatibleStatements.tree_of_contextual_body ordinary unique closed residual
    declarations readExpression lowerRead leafLowerer readStatement lowerExpression syntaxTree projection accepted
  exact ⟨⟨accepted, flow, emitted, tree⟩⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleNamedBody
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleNamedBodyMeaning
/-! The static body receipt discharges ordinary body correspondence at its
actual context. Independent closure-call traces and language-result values are
connected without assuming a universal body theorem for arbitrary contexts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleNamedBody
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

/-- Function call exits, including the independent escaped-control fault. -/
inductive Exit (resultType : TypeSystem.Ty) : Dynamic.ControlOutcome → Dynamic.ExpressionOutcome → Prop where
  | returned (value : Dynamic.Value) : Exit resultType (.returned value) (.value value)
  | unit (environment : Dynamic.Environment) (same : resultType = .unit) :
      Exit resultType (.fallthrough environment) (.value .unit)
  | fault (reason : Dynamic.SemanticFault) : Exit resultType (.fault reason) (.fault reason)
  | breaking (environment : Dynamic.Environment) :
      Exit resultType (.breaking environment) (.fault .controlEscapedFunction)
  | continuing (environment : Dynamic.Environment) :
      Exit resultType (.continuing environment) (.fault .controlEscapedFunction)

theorem trace_control {program : Program} {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ finalContext control,
      Dynamic.FunctionStatementsExecuteOutcome program context function.evidence function.source environment
        before function.body finalContext control after ∧ Exit function.resultType control outcome := by
  cases trace with
  | returned execution => exact ⟨_, _, .control execution, .returned _⟩
  | unit same execution => exact ⟨_, _, .control execution, .unit _ same⟩
  | fault execution => exact ⟨_, _, .fault execution, .fault _⟩
  | escaped execution escape =>
    rcases escape with ⟨environment, rfl⟩ | ⟨environment, rfl⟩
    · exact ⟨_, _, .control execution, .breaking environment⟩
    · exact ⟨_, _, .control execution, .continuing environment⟩

theorem body_result {values : SourceCoreCompatibleValues.Context} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {faults : FunctionCalls.FaultRep}
    {expected : TypeSystem.Ty} {type : Ty} {control : Dynamic.ControlOutcome}
    {outcome : Dynamic.ExpressionOutcome} {value : Value}
    (related : CompatibleStatements.BodyRep (registry := registry) functions mapping world faults expected type control value)
    (exit : Exit expected control outcome) :
    FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world expected type faults outcome value := by
  cases related with
  | fallthrough environment => cases exit; exact .value .unit
  | returned payload => cases exit; exact .value payload
  | fault matched => cases exit; exact .fault matched

/-- The fixed grammar cannot manufacture fault control through successful
source execution. Actual source faults retain their separate fault derivation. -/
theorem tree_control_not_fault {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {flow : Expr}
    (tree : CompatibleStatements.Tree readFuel values source context solved reasonAt scope statements expected type flow)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {actualContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (executed : Dynamic.FunctionStatementsExecute program actualContext evidence source environment before
      statements finalContext (.fault reason) after) : False := by
  induction tree generalizing actualContext finalContext environment before after with
  | nil => cases executed
  | @returnUnit id node rest found form =>
    have contains := lookupStatement?_sound found
    have notTail : true = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
      intro _ _ expression; simp [form]
    rcases ScalarStatementViews.cons_view true unique contains notTail executed with
      ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.returnUnit unique contains form head
      cases impossible
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.returnUnit unique contains form head
      cases impossible
  | @returnValue id node expression expressionNode expected lowered rest found form expressionFound valueType value =>
    have contains := lookupStatement?_sound found
    have notTail : true = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
      intro _ _ expression; simp [form]
    rcases ScalarStatementViews.cons_view true unique contains notTail executed with
      ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, _, impossible, _⟩ := ScalarStatementViews.returnValue unique contains form head
      cases impossible
    · obtain ⟨_, _, impossible, _⟩ := ScalarStatementViews.returnValue unique contains form head
      cases impossible
  | tail found form expressionFound valueType value =>
    cases executed with
    | singleton contains notTail head =>
      have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
      subst_vars
      exact notTail _ form
  | @discard id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining ih =>
    have contains := lookupStatement?_sound found
    have notTailExpression : true = true → rest = [] → ∀ other, node.form ≠ .expression other false := by
      intro _ empty other impossible
      rw [form] at impossible
      cases impossible
      simp [empty] at notTail
    rcases ScalarStatementViews.cons_view true unique contains notTailExpression executed with
      ⟨_, _, _, head, tail⟩ | ⟨head, terminal⟩
    · obtain ⟨rfl, same, _, _⟩ := ScalarStatementViews.expression unique contains form head
      cases same
      exact ih tail
    · obtain ⟨_, impossible, _, _⟩ := ScalarStatementViews.expression unique contains form head
      cases impossible

variable {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {type : Ty}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {code : Expr}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))

include extension contextValid unique uninitialized in
theorem Certificate.preserves [FunctionCalls.FaultTokens faults]
    (certificate : Certificate readFuel values function.source context solved reasonAt scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨_, control, sourceTrace, exit⟩ := trace_control trace
  obtain ⟨_, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    certificate.tree.body_preserves functions extension program function.evidence contextValid unique uninitialized
      fellThrough escaped environments heaps locals agrees sourceTrace
  rw [← certificate.emitted] at evaluated
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, body_result represented exit,
    finalHeaps, maps, worlds, frame, metadata⟩

include extension contextValid unique uninitialized in
theorem Certificate.reflects [FunctionCalls.FaultTokens faults]
    (certificate : Certificate readFuel values function.source context solved reasonAt scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  rw [certificate.emitted] at evaluated
  obtain ⟨control, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    certificate.tree.body_reflects functions extension program function.evidence contextValid uninitialized
      fellThrough escaped environments heaps locals agrees evaluated
  have result : ∃ outcome, FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value := by
    generalize raw : function.resultType = expected at represented
    cases represented with
    | fallthrough finalEnvironment =>
      cases trace with
      | control executed =>
        refine ⟨_, .unit raw executed, ?_⟩
        exact .value .unit
    | returned payload =>
      cases trace with
      | control executed =>
        refine ⟨_, .returned executed, ?_⟩
        exact .value payload
    | fault matched =>
      cases trace with
      | control executed => exact False.elim (tree_control_not_fault certificate.tree unique executed)
      | fault failed => exact ⟨_, .fault failed, .fault matched⟩
  obtain ⟨outcome, trace, result⟩ := result
  exact ⟨outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, frame, metadata⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleNamedBody
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleNamedBodyIndexed
/-! Indexed frame installation/restoration for a certified compatible body at
its actual source context. The named hook equation is retained explicitly. For
a parameterized whole function it must be composed with the separately derived
parameter prefix; this theorem does not identify that prefix with the body. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleNamedBody.Indexed
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableAncestryPairedLookup CallableIndexedHistory
open SourceCoreCallableIndexedFrames

private theorem agree_body {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (saved : Value) :
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
      canonical (.unit :: saved :: actual) :=
  GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees saved) .unit

private theorem rename_body (body : Expr) (ξ : Renaming) :
    body.rename (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)) =
      ((body.rename ξ).weakenAt 0).weakenAt 0 := by
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix]

private theorem next_evaluates (layout : Layout) (index : Int) (environment : Environment)
    (store : Store) (saved : Value) :
    Evaluates (saved :: environment) store
      ((SourceCoreCallableIndexedDispatch.literal layout (.state index)).weakenAt 0)
      (encode layout (.state index)) store := by
  rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
  exact CallableIndexedContextFrames.literal_evaluates _ _ _ _

variable {checked : Checked} {base : Base checked}
  {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {sourceFunction : Dynamic.Closure} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {type : Ty}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {body : Expr}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : CompatiblePayload.FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context sourceFunction.evidence)
  (unique : NodeOccurrencesUnique sourceFunction.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))

include extension contextValid unique uninitialized in
/-- At the certified body context, finite source execution determines the
accepted named hook's native result and restores its caller's frame. -/
theorem preserves [FunctionCalls.FaultTokens faults] (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
    {named : SourceCoreGeneralFunctions.Function} {code : Expr} {ξ : Renaming}
    (accepted : SourceCoreCallableIndexedAncestry.namedBody prepared named (body.rename ξ) = .ok code)
    (certificate : CompatibleNamedBody.Certificate readFuel values sourceFunction.source context solved reasonAt scope
      sourceFunction.body sourceFunction.resultType type policy fuel fellThrough escaped body)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {location : Location}
    {current : NativeFrame} {currentGhost : GhostFrame} {outcome : Dynamic.ExpressionOutcome}
    {records : List CallableIndexedSnapshots.Record}
    (registered : prepared.layout.frame.Registered ambient.definitions)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (unmapped : location ∉ mapping) (typed : world[location]? = some prepared.layout.frame.type)
    (reference : actual[base.globals.length + 1]? = some (.cellRef prepared.layout.frame.type location))
    (caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost store)
    (snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records)
    (trace : FunctionCallBody.Trace program sourceFunction context environment before outcome after) :
    ∃ origin index metadata value finalStore finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Evaluates actual store code value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld sourceFunction.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history prepared accepted
  obtain ⟨installedHeaps, _⟩ := CallableIndexedBodyFrames.install registered heaps unmapped typed caller (.stable history)
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, represented, finalHeaps, maps, worlds, frame, sourceMetadata⟩ :=
    certificate.preserves functions extension program contextValid unique uninitialized environments installedHeaps locals
      (agree_body agrees (encode prepared.layout.frame current)) trace
  rw [rename_body] at bodyEvaluation
  have evaluated := CallableContextFrames.withFrame_evaluates (.var reference) caller.read
    (next_evaluates prepared.layout.frame index actual store (encode prepared.layout.frame current)) bodyEvaluation
  obtain ⟨restoredHeaps, restoredFrame, restoredCaller⟩ :=
    CallableIndexedBodyFrames.restore registered unmapped typed caller finalHeaps worlds frame
  exact ⟨origin, index, metadata, value, _, finalMap, finalWorld, owned, history,
    emitted.symm ▸ evaluated, represented, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata,
    restoredCaller, snapshots.transport restoredFrame⟩

include extension contextValid unique uninitialized in
/-- Completed execution of the actual named hook constructs the independent
source trace. The body correspondence is derived from its static receipt. -/
theorem reflects [FunctionCalls.FaultTokens faults] (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
    {named : SourceCoreGeneralFunctions.Function} {code : Expr} {ξ : Renaming}
    (accepted : SourceCoreCallableIndexedAncestry.namedBody prepared named (body.rename ξ) = .ok code)
    (certificate : CompatibleNamedBody.Certificate readFuel values sourceFunction.source context solved reasonAt scope
      sourceFunction.body sourceFunction.resultType type policy fuel fellThrough escaped body)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {location : Location}
    {current : NativeFrame} {currentGhost : GhostFrame} {value : Value}
    {records : List CallableIndexedSnapshots.Record}
    (registered : prepared.layout.frame.Registered ambient.definitions)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (unmapped : location ∉ mapping) (typed : world[location]? = some prepared.layout.frame.type)
    (reference : actual[base.globals.length + 1]? = some (.cellRef prepared.layout.frame.type location))
    (caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost store)
    (snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records)
    (evaluation : Evaluates actual store code value finalStore) :
    ∃ origin index metadata outcome after finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      FunctionCallBody.Trace program sourceFunction context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld sourceFunction.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history prepared accepted
  obtain ⟨installedHeaps, _⟩ := CallableIndexedBodyFrames.install registered heaps unmapped typed caller (.stable history)
  rw [emitted] at evaluation
  obtain ⟨nextValue, nextStore, bodyStore, nextEvaluation, bodyEvaluation, finalEq⟩ :=
    CallableContextFrames.withFrame_reflects (.var reference) caller.read evaluation
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic nextEvaluation
    (next_evaluates prepared.layout.frame index actual store (encode prepared.layout.frame current))
  rw [← rename_body] at bodyEvaluation
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, sourceMetadata⟩ :=
    certificate.reflects functions extension program contextValid unique uninitialized environments installedHeaps locals
      (agree_body agrees (encode prepared.layout.frame current)) bodyEvaluation
  obtain ⟨restoredHeaps, restoredFrame, restoredCaller⟩ :=
    CallableIndexedBodyFrames.restore registered unmapped typed caller finalHeaps worlds frame
  subst finalStore
  exact ⟨origin, index, metadata, outcome, after, finalMap, finalWorld, owned, history,
    trace, represented, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata,
    restoredCaller, snapshots.transport restoredFrame⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleNamedBody.Indexed
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleNamedBodyCompilation
/-! Extraction from the actual zero-parameter named-function compiler. The
source/diagnostic/contextual-parent receipts are static preflight facts. The
compiled body tree and accepted indexed named hook are obtained from compiler
success, rather than assumed child trees or semantic body hypotheses. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleNamedBody
open Core Frontend SourceInference
open CompatibleEncoding (bind_ok)

def bodyContext (plan : SourceSpecializationWorklist.Plan) (globals : List SourceCoreCalls.Signature)
    (named : SourceCoreGeneralFunctions.Function) : SourceCoreFunctions.Context := {
  plan, globals, owner := named.signature.key, administrativePrefix := 1
  solvedRequirements := named.specialized.function.solvedRequirements
  internalReason := Word.zero
}

def bodyPolicy (representation : SourceCoreGeneralFunctions.Representation)
    (program : CheckedProgram) (signatures : ProgramSignatures)
    (locals : SourceCoreLocalPolymorphism.Catalog) (parents : List SourceCoreLocalEvidence.Prepared)
    (assignments : SourceCoreAssignmentFaultSites.Table) (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (context : SourceCoreFunctions.Context) (native : Option SourceCoreGeneralFunctions.CallableContext) : SourceCoreLoops.Policy := {
  representation.loopsWithSourceCells representation.expressions.sourceCells context.solvedRequirements assignments diagnostics context.owner
    (SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments diagnostics
      context native none none) with
  sourceCells := representation.expressions.sourceCells
  lowerBinder := SourceCoreGeneralFunctions.contextualBinder representation locals context.owner []
}

private theorem roots_map (statements : List StatementId) :
    (statements.map NodeId.statement).mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
      | .statement id => pure id
      | .expression id => throw (.expectedStatementRoot id)) = .ok statements := by
  induction statements with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, List.mapM_cons]
    rw [ih]
    rfl

/-- The source attribution is stated independently of emitted Core shape. -/
structure NamedAgreement (named : SourceCoreGeneralFunctions.Function) (function : Dynamic.Closure) : Prop where
  source : function.source = named.specialized.function.typedBody
  roots : function.source.roots = function.body.map NodeId.statement
  parameters : function.parameters = named.inputs.map Prod.fst
  result : function.resultType = named.specialized.function.inferredBodyType

/-- For zero parameters, compiler success yields the real body certificate and
the actual frame-installation hook equation. No parameter prefix is erased. -/
theorem zero_of_accepted
    {checked : SourceCoreCompatibleCatalog.Checked} {base : SourceCoreCompatibleFunctions.Prepared checked}
    (ancestry : SourceCoreCallableIndexedAncestry.Prepared base)
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {plan : SourceSpecializationWorklist.Plan}
    {globals : List SourceCoreCalls.Signature} {locals : SourceCoreLocalPolymorphism.Catalog}
    {native : Option SourceCoreGeneralFunctions.CallableContext}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {named : SourceCoreGeneralFunctions.Function}
    {parents : List SourceCoreLocalEvidence.Prepared} {own : SourceCoreProgramFaultSites.Function}
    {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {readFuel fuel : Nat} {values : SourceCoreCompatibleValues.Context} {code : Expr}
    (agreement : NamedAgreement named function) (parameters : named.inputs = [])
    (parentReceipt : SourceCoreStageCodebook.prepareContexts program plan (locals.bindings.flatMap (·.instances)) = .ok parents)
    (diagnosticReceipt : diagnostics.base.find? named.signature.key = some own)
    (ordinary : CompatibleExpressionConstructors.Ordinary function.source locals named.signature.key)
    (unique : NodeOccurrencesUnique function.source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source [] context)
    (readExpression : (representation.atContext named.signature.key []).expressions.readExpression =
      SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : (representation.atContext named.signature.key []).expressions.lowerRead =
      SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : (representation.atContext named.signature.key []).expressions.leafLowerer =
      SourceCoreCompatibleDataExpressions.leafLowerer values)
    (readStatement : (bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents
      own.assignments diagnostics (bodyContext plan globals named) native).readStatement =
      SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (lowerExpression : (bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents
      own.assignments diagnostics (bodyContext plan globals named) native).lowerExpression =
      SourceCoreGeneralFunctions.lowerContextualExpression program (representation.atContext named.signature.key [])
        signatures locals parents own.assignments diagnostics (bodyContext plan globals named) native none none)
    (hook : representation.rawNamedBody = SourceCoreCallableIndexedAncestry.namedBody ancestry)
    (syntaxTree : CompatibleStatements.Syntax function.source context function.body function.resultType)
    (projection : values.checked.catalog.project function.resultType = .ok named.signature.resultType)
    (accepted : SourceCoreGeneralFunctions.compileClosureWithRepresentation program representation signatures plan globals
      diagnostics locals native fuel named = .ok code) :
    ∃ body output,
      Nonempty (Certificate readFuel values function.source context named.specialized.function.solvedRequirements
        (diagnostics.reasonAt named.signature.key) [] function.body function.resultType named.signature.resultType
        (bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents own.assignments
          diagnostics (bodyContext plan globals named) native) fuel own.fellThroughReason own.table.escapedReason body) ∧
      SourceCoreCallableIndexedAncestry.namedBody ancestry named body = .ok output ∧
      code = .lambda named.signature.parameterType (LanguageResult.resultType named.signature.resultType) output := by
  unfold SourceCoreGeneralFunctions.compileClosureWithRepresentation at accepted
  simp only [parentReceipt, Except.mapError, diagnosticReceipt, bind, Except.bind, pure, Except.pure] at accepted
  rw [← agreement.source, agreement.roots] at accepted
  have roots := roots_map function.body
  simp only [pure, Except.pure, List.mapM_map, Function.comp_def] at roots
  simp only [List.mapM_map, Function.comp_def] at accepted
  rw [roots] at accepted
  simp only [parameters, List.reverse_nil, List.map_nil,
    SourceCoreGeneralFunctions.bodyLowererWithRepresentation] at accepted
  cases result : SourceCoreLoops.lowerStatementsWithPolicy
      (bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents own.assignments
        diagnostics (bodyContext plan globals named) native) fuel function.source [] function.body named.signature.resultType
        (diagnostics.reasonAt named.signature.key) own.fellThroughReason own.table.escapedReason with
  | error error =>
    simp only [bodyPolicy, bodyContext] at result
    rw [result] at accepted
    cases accepted
  | ok body =>
    have certificate := of_contextual ordinary unique closed residual declarations readExpression lowerRead leafLowerer
      readStatement lowerExpression syntaxTree projection result
    simp only [bodyPolicy, bodyContext] at result
    rw [result] at accepted
    cases sourceCells : representation.allocatorAt named.signature.key [] <;>
      simp [SourceCoreGeneralFunctions.Representation.atContext, sourceCells,
        SourceCoreFunctions.bindParameters, SourceCoreSourceCells.bindParameters,
        hook, pure, Except.pure] at accepted
    all_goals
      obtain ⟨output, generated, same⟩ := bind_ok accepted
      have hookAccepted : SourceCoreCallableIndexedAncestry.namedBody ancestry named body = .ok output := by
        cases result : SourceCoreCallableIndexedAncestry.namedBody ancestry named body with
        | error error => simp [result] at generated
        | ok actual => simp only [result, Except.ok.injEq] at generated; cases generated; rfl
      exact ⟨body, output, certificate, hookAccepted, Except.ok.inj same.symm⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleNamedBody
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleNamedParameterCertificates
/-! The named compiler installs parameter cells before passing its raw body to
its indexed hook. Successful production compilation supplies both the body
certificate at the extended scope and the actual parameter-allocation tree.
No semantic body or parameter execution is a static premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleNamedParameters
open Core Frontend SourceInference CompatibleNamedBody
open CompatibleEncoding (bind_ok)

private theorem roots_map (statements : List StatementId) :
    (statements.map NodeId.statement).mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
      | .statement id => pure id
      | .expression id => throw (.expectedStatementRoot id)) = .ok statements := by
  induction statements with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, List.mapM_cons]
    rw [ih]
    rfl

/-- Extract the real parameter prefix and the body at the actual input scope.
The allocator equality identifies its registered layout/profile explicitly. -/
theorem of_accepted
    {checked : SourceCoreCompatibleCatalog.Checked} {base : SourceCoreCompatibleFunctions.Prepared checked}
    (ancestry : SourceCoreCallableIndexedAncestry.Prepared base)
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {plan : SourceSpecializationWorklist.Plan}
    {globals : List SourceCoreCalls.Signature} {locals : SourceCoreLocalPolymorphism.Catalog}
    {native : Option SourceCoreGeneralFunctions.CallableContext}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {named : SourceCoreGeneralFunctions.Function}
    {parents : List SourceCoreLocalEvidence.Prepared} {own : SourceCoreProgramFaultSites.Function}
    {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {readFuel fuel : Nat} {values : SourceCoreCompatibleValues.Context} {code : Expr}
    {layouts : SourceCoreAllocationLayouts.Prepared} {allocationGlobals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (agreement : NamedAgreement named function)
    (parentReceipt : SourceCoreStageCodebook.prepareContexts program plan (locals.bindings.flatMap (·.instances)) = .ok parents)
    (diagnosticReceipt : diagnostics.base.find? named.signature.key = some own)
    (ordinary : CompatibleExpressionConstructors.Ordinary function.source locals named.signature.key)
    (unique : NodeOccurrencesUnique function.source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source
      (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) context)
    (readExpression : (representation.atContext named.signature.key []).expressions.readExpression =
      SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : (representation.atContext named.signature.key []).expressions.lowerRead =
      SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : (representation.atContext named.signature.key []).expressions.leafLowerer =
      SourceCoreCompatibleDataExpressions.leafLowerer values)
    (readStatement : (bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents
      own.assignments diagnostics (bodyContext plan globals named) native).readStatement =
      SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (lowerExpression : (bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents
      own.assignments diagnostics (bodyContext plan globals named) native).lowerExpression =
      SourceCoreGeneralFunctions.lowerContextualExpression program (representation.atContext named.signature.key [])
        signatures locals parents own.assignments diagnostics (bodyContext plan globals named) native none none)
    (allocator : (representation.atContext named.signature.key []).expressions.sourceCells = some
      (SourceCoreCallableIndexedAllocationFrames.allocator ancestry.layout.frame allocationGlobals
        (layouts.allocatorAt named.signature.key [] onError)))
    (hook : representation.rawNamedBody = SourceCoreCallableIndexedAncestry.namedBody ancestry)
    (syntaxTree : CompatibleStatements.Syntax function.source context function.body function.resultType)
    (projection : values.checked.catalog.project function.resultType = .ok named.signature.resultType)
    (accepted : SourceCoreGeneralFunctions.compileClosureWithRepresentation program representation signatures plan globals
      diagnostics locals native fuel named = .ok code) :
    ∃ body parameterCode output,
      Nonempty (Certificate readFuel values function.source context named.specialized.function.solvedRequirements
        (diagnostics.reasonAt named.signature.key) (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)))
        function.body function.resultType named.signature.resultType
        (bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents own.assignments
          diagnostics (bodyContext plan globals named) native) fuel own.fellThroughReason own.table.escapedReason body) ∧
      SourceCoreSourceCells.bindParameters
        (SourceCoreCallableIndexedAllocationFrames.allocator ancestry.layout.frame allocationGlobals
          (layouts.allocatorAt named.signature.key [] onError)) function.source [] named.inputs
        named.signature.resultType SourceCoreFunctions.argumentProjection body = .ok parameterCode ∧
      CallableIndexedParameterCertificates.Tree layouts named.signature.key [] ancestry.layout.frame allocationGlobals onError
        function.source named.inputs.length named.signature.resultType body [] 0 named.inputs parameterCode ∧
      SourceCoreCallableIndexedAncestry.namedBody ancestry named parameterCode = .ok output ∧
      code = .lambda named.signature.parameterType (LanguageResult.resultType named.signature.resultType) output := by
  unfold SourceCoreGeneralFunctions.compileClosureWithRepresentation at accepted
  simp only [parentReceipt, Except.mapError, diagnosticReceipt, bind, Except.bind, pure, Except.pure] at accepted
  rw [← agreement.source, agreement.roots] at accepted
  have roots := roots_map function.body
  simp only [pure, Except.pure, List.mapM_map, Function.comp_def] at roots
  simp only [List.mapM_map, Function.comp_def] at accepted
  rw [roots] at accepted
  simp only [SourceCoreGeneralFunctions.bodyLowererWithRepresentation] at accepted
  cases bodyResult : SourceCoreLoops.lowerStatementsWithPolicy
      (bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents own.assignments
        diagnostics (bodyContext plan globals named) native) fuel function.source
        (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) function.body named.signature.resultType
        (diagnostics.reasonAt named.signature.key) own.fellThroughReason own.table.escapedReason with
  | error error =>
    simp only [bodyPolicy, bodyContext] at bodyResult
    rw [bodyResult] at accepted
    cases accepted
  | ok body =>
    have certificate := CompatibleNamedBody.of_contextual ordinary unique closed residual declarations readExpression
      lowerRead leafLowerer readStatement lowerExpression syntaxTree projection bodyResult
    simp only [bodyPolicy, bodyContext] at bodyResult
    rw [bodyResult] at accepted
    rw [allocator] at accepted
    cases prefixResult : SourceCoreSourceCells.bindParameters
        (SourceCoreCallableIndexedAllocationFrames.allocator ancestry.layout.frame allocationGlobals
          (layouts.allocatorAt named.signature.key [] onError)) function.source [] named.inputs
        named.signature.resultType SourceCoreFunctions.argumentProjection body with
    | error error => simp [prefixResult] at accepted
    | ok parameterCode =>
      have tree := CallableIndexedParameterCertificates.of_accepted onError prefixResult
      simp only [prefixResult] at accepted
      obtain ⟨output, generated, same⟩ := bind_ok accepted
      simp only [SourceCoreGeneralFunctions.Representation.atContext, hook] at generated
      have hookAccepted : SourceCoreCallableIndexedAncestry.namedBody ancestry named parameterCode = .ok output := by
        cases result : SourceCoreCallableIndexedAncestry.namedBody ancestry named parameterCode with
        | error error => simp [result] at generated
        | ok actual => simp only [result, Except.ok.injEq] at generated; cases generated; rfl
      exact ⟨body, parameterCode, output, certificate, prefixResult, tree, hookAccepted, Except.ok.inj same.symm⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleNamedParameters
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleNamedParameterMeaning
/-! Parameter installation reaches the actual monomorphic call context. Its
finite continuation agreement comes from the production allocation receipts;
body correspondence comes from the extracted fixed-context certificate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleNamedParameters
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning

structure Entry (values : SourceCoreCompatibleValues.Context)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (function : Dynamic.Closure) (context : SourceSemantics.Context) (bindings : List Binding)
    (arguments : List Dynamic.Value) (before : Dynamic.Heap) (initialStore : Store)
    (initialMap : LocationMap) (initialWorld : StoreTyping) (administrative : Core.Context)
    (actual : Environment) (ξ : Renaming) (parameterCode body : Expr) where private mk ::
  environment : Dynamic.Environment
  heap : Dynamic.Heap
  canonical : Environment
  actualBody : Environment
  store : Store
  mapping : LocationMap
  world : StoreTyping
  embedding : Renaming
  allocation : Dynamic.BindersAllocate [] before function.parameters arguments environment heap
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative)
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment canonical ambient.definitions
  heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  maps : LocationMap.Extends initialMap mapping
  worlds : WorldExtends initialWorld world
  frame : AdministrativePreserved initialMap initialStore mapping store
  metadata : Dynamic.HeapMetadataExtend before heap
  lookups : EnvironmentsAgree embedding canonical actualBody
  agreement : ContinuationAgreement actual initialStore (parameterCode.rename ξ) actualBody store (body.rename embedding)

/-- Every source/native parameter fact is constructed before running the body.
The call context is fixed by the independent monomorphic binder extension. -/
theorem entry_of_accepted
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {bindings : List Binding} {output : Ty} {body parameterCode : Expr}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      function.source [] bindings output SourceCoreFunctions.argumentProjection body = .ok parameterCode)
    (parameters : function.parameters = bindings.map Prod.fst)
    (inputs : function.source.inputs = bindings.map Prod.fst)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world bindings arguments nativeArguments)
    {administrative : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
    {ξ : Renaming} {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals [])
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
    (reference : canonical[globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping) :
    Nonempty (Entry values functions registry function context bindings arguments before store mapping world
      administrative actual ξ parameterCode body) := by
  obtain ⟨environment, heap, finalCanonical, finalActual, finalStore, finalMap, finalWorld, embedding,
      allocated, finalEnvironments, finalHeaps, maps, worlds, frame, lookups, agreement⟩ :=
    CallableIndexedParameters.named_prefix onError accepted inputs definitions registered represented environments heaps
      actualLayout reference read unmapped
  rw [← parameters] at allocated
  have mono := FunctionCallBody.mono_binders extended
  exact ⟨⟨environment, heap, finalCanonical, finalActual, finalStore, finalMap, finalWorld, embedding,
    allocated, finalEnvironments, finalHeaps, GenericLexicalContext.binders_agree mono.1 mono.2 initialLocals allocated,
    maps, worlds, frame, GenericLexicalContext.binders_metadata allocated, lookups, agreement⟩⟩

variable {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry) (program : Program)
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {bindings : List Binding} {output : Ty}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {body parameterCode : Expr}
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {store : Store}
  {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context} {actual : Environment} {ξ : Renaming}

include extension contextValid unique uninitialized in
/-- Finite source body execution completes the actual parameter prefix. The
source allocation is the one retained by the constructed entry. -/
theorem Entry.preserves [FunctionCalls.FaultTokens faults]
    (entry : Entry values functions registry function context bindings arguments before store mapping world
      administrative actual ξ parameterCode body)
    (certificate : CompatibleNamedBody.Certificate readFuel values function.source context solved reasonAt
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) function.body function.resultType output
      policy fuel fellThrough escaped body)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : FunctionCallBody.Trace program function context entry.environment entry.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (parameterCode.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata⟩ :=
    certificate.preserves functions extension program contextValid unique uninitialized entry.environments entry.heaps
      entry.locals entry.lookups trace
  exact ⟨value, finalStore, finalMap, finalWorld, entry.agreement.wrap evaluated, represented, heaps,
    entry.maps.trans maps, entry.worlds.trans worlds, entry.frame.trans frame, entry.metadata.trans metadata⟩

include extension contextValid unique uninitialized in
/-- Completed native prefix execution constructs the independent source trace
at the installed call context, without a universal body reflection premise. -/
theorem Entry.reflects [FunctionCalls.FaultTokens faults]
    (entry : Entry values functions registry function context bindings arguments before store mapping world
      administrative actual ξ parameterCode body)
    (certificate : CompatibleNamedBody.Certificate readFuel values function.source context solved reasonAt
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) function.body function.resultType output
      policy fuel fellThrough escaped body)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates actual store (parameterCode.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata⟩ :=
    certificate.reflects functions extension program contextValid unique uninitialized entry.environments entry.heaps
      entry.locals entry.lookups (entry.agreement.unwrap evaluated)
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, heaps, entry.maps.trans maps,
    entry.worlds.trans worlds, entry.frame.trans frame, entry.metadata.trans metadata⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleNamedParameters
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleNamedParameterIndexed
/-! The actual named hook encloses the complete marked parameter prefix. Its
body certificate is applied only at the installed call context. Native and
source parameter allocations precede that continuation, and the caller frame
and protected snapshots are restored after either represented body outcome. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleNamedParameters.Indexed
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableAncestryPairedLookup CallableIndexedHistory
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

private theorem agree_prefix {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (saved : Value) :
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
      canonical (.unit :: saved :: actual) :=
  GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees saved) .unit

private theorem rename_prefix (body : Expr) (ξ : Renaming) :
    body.rename (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)) =
      ((body.rename ξ).weakenAt 0).weakenAt 0 := by
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix]

private theorem next_evaluates (layout : Layout) (index : Int) (environment : Environment)
    (store : Store) (saved : Value) :
    Evaluates (saved :: environment) store
      ((SourceCoreCallableIndexedDispatch.literal layout (.state index)).weakenAt 0)
      (encode layout (.state index)) store := by
  rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
  exact CallableIndexedContextFrames.literal_evaluates _ _ _ _

variable {checked : Checked} {base : Base checked}
  (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : CompatiblePayload.FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {readFuel : Nat} {bindings : List Binding} {output : Ty} {policy : SourceCoreLoops.Policy}
  {fuel : Nat} {fellThrough escaped : Word} {body parameterCode : Expr}
  (certificate : CompatibleNamedBody.Certificate readFuel values function.source context solved reasonAt
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) function.body function.resultType output
    policy fuel fellThrough escaped body)
  (parameters : function.parameters = bindings.map Prod.fst)
  (inputs : function.source.inputs = bindings.map Prod.fst)
  (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {allocationGlobals : Nat}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame allocationGlobals
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode)
  (definitions : layouts.definitions = ambient.definitions) (registered : prepared.layout.frame.Registered ambient.definitions)
  {named : SourceCoreGeneralFunctions.Function} {code : Expr} {ξ : Renaming}
  (acceptedHook : SourceCoreCallableIndexedAncestry.namedBody prepared named (parameterCode.rename ξ) = .ok code)
  {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world bindings arguments nativeArguments)
  {administrative : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
  {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}
  {records : List CallableIndexedSnapshots.Record}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative [] [] canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals [])
  (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
  (canonicalReference : canonical[allocationGlobals]? = some (.cellRef prepared.layout.frame.type location))
  (actualReference : actual[base.globals.length + 1]? = some (.cellRef prepared.layout.frame.type location))
  (unmapped : location ∉ mapping) (typed : world[location]? = some prepared.layout.frame.type)
  (caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost store)
  (snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records)

include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized in
/-- A source allocation and its finite body trace execute the real full named
hook. Parameters are compared with the independently constructed allocation. -/
theorem preserves [FunctionCalls.FaultTokens faults] {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate [] before function.parameters arguments environment bound)
    (trace : FunctionCallBody.Trace program function context environment bound outcome after) :
    ∃ origin index metadata value finalStore finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Evaluates actual store code value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history prepared acceptedHook
  obtain ⟨installedHeaps, installedCaller⟩ := CallableIndexedBodyFrames.install registered heaps unmapped typed caller (.stable history)
  obtain ⟨entry⟩ := entry_of_accepted functions onError acceptedPrefix parameters inputs extended definitions registered represented
    environments installedHeaps initialLocals (agree_prefix actualLayout (encode prepared.layout.frame current))
    canonicalReference installedCaller.read unmapped
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at trace
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, represented, finalHeaps, maps, worlds, frame, sourceMetadata⟩ :=
    entry.preserves functions extension program contextValid unique uninitialized certificate trace
  rw [rename_prefix] at bodyEvaluation
  have evaluated := CallableContextFrames.withFrame_evaluates (.var actualReference) caller.read
    (next_evaluates prepared.layout.frame index actual store (encode prepared.layout.frame current)) bodyEvaluation
  obtain ⟨restoredHeaps, restoredFrame, restoredCaller⟩ :=
    CallableIndexedBodyFrames.restore registered unmapped typed caller finalHeaps worlds frame
  exact ⟨origin, index, metadata, value, _, finalMap, finalWorld, owned, history,
    emitted.symm ▸ evaluated, represented, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata,
    restoredCaller, snapshots.transport restoredFrame⟩

include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized in
/-- Completed actual native execution constructs both source parameter
allocation and the independent body trace at the fixed call context. -/
theorem reflects [FunctionCalls.FaultTokens faults] {value : Value} {finalStore : Store}
    (evaluation : Evaluates actual store code value finalStore) :
    ∃ origin index metadata environment bound outcome after finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound ∧
      FunctionCallBody.Trace program function context environment bound outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history prepared acceptedHook
  obtain ⟨installedHeaps, installedCaller⟩ := CallableIndexedBodyFrames.install registered heaps unmapped typed caller (.stable history)
  obtain ⟨entry⟩ := entry_of_accepted functions onError acceptedPrefix parameters inputs extended definitions registered represented
    environments installedHeaps initialLocals (agree_prefix actualLayout (encode prepared.layout.frame current))
    canonicalReference installedCaller.read unmapped
  rw [emitted] at evaluation
  obtain ⟨nextValue, nextStore, bodyStore, nextEvaluation, bodyEvaluation, finalEq⟩ :=
    CallableContextFrames.withFrame_reflects (.var actualReference) caller.read evaluation
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic nextEvaluation
    (next_evaluates prepared.layout.frame index actual store (encode prepared.layout.frame current))
  rw [← rename_prefix] at bodyEvaluation
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, sourceMetadata⟩ :=
    entry.reflects functions extension program contextValid unique uninitialized certificate bodyEvaluation
  obtain ⟨restoredHeaps, restoredFrame, restoredCaller⟩ :=
    CallableIndexedBodyFrames.restore registered unmapped typed caller finalHeaps worlds frame
  subst finalStore
  exact ⟨origin, index, metadata, entry.environment, entry.heap, outcome, after, finalMap, finalWorld, owned, history,
    entry.allocation, trace, represented, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata,
    restoredCaller, snapshots.transport restoredFrame⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleNamedParameters.Indexed
end
