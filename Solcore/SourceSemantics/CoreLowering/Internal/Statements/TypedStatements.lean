import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionTyped
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Statements
import Solcore.SourceSemantics.CoreLowering.ScalarStatementViews
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.LoopRenaming
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.LoopLayouts

/-!
# Typed statements

Trees, certificates and meaning of typed statement sequences, and of mixed ones.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedStatementTree
/-! A fixed-scope function sequence with typed compatible expressions.
The static source spine retains raw result types and independent expression
 typing. Unreachable suffixes of explicit returns need no execution certificate.
Scalar-key mapping indexes use ordinary comparator code and typed captures.
Let bindings, assignments, scoped statements and calls are separate extensions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedStatements
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
      (value : CompatibleExpressionTyped.Syntax source expression) : Syntax source context (id :: rest) expected
  | tail {id node expression expressionNode expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
      (sourceType : node.type = expected) (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (value : CompatibleExpressionTyped.Syntax source expression) : Syntax source context [id] expected
  | discard {id node expression expressionNode semicolon rest expected}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && rest.isEmpty) = false)
      (sourceType : node.type = if semicolon then .unit else expressionNode.type)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (typed : ExpressionHasType source context expression expressionNode.type)
      (value : CompatibleExpressionTyped.Syntax source expression)
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
      (value : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope expression lowered) :
      Tree readFuel values source context solved reasonAt scope (id :: rest) expected lowered.type
        (LocalLoop.returnValue lowered.type lowered.expression)
  | tail {id node expression expressionNode expected lowered}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (value : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope expression lowered) :
      Tree readFuel values source context solved reasonAt scope [id] expected lowered.type
        (LocalLoop.returnValue lowered.type lowered.expression)
  | discard {id node expression expressionNode semicolon rest expected lowered type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && rest.isEmpty) = false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (value : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope expression lowered)
      (remaining : Tree readFuel values source context solved reasonAt scope rest expected type body) :
      Tree readFuel values source context solved reasonAt scope (id :: rest) expected type
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)

/-- The existing production body wrapper, with no extra Core instruction. -/
abbrev finish := CompatibleStatements.finish

end Solcore.SourceSemantics.CoreLowering.TypedStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedStatementCertificates
/-! Static extraction from the production statement traversal. The generic
extraction callback is discharged by the actual contextual expression compiler
below; neither theorem assumes a child runtime execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedStatements
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
    (expressions : ∀ {fuel id node lowered}, CompatibleExpressionTyped.Syntax source id →
      source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope id lowered)
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
    (expressions : ∀ {fuel id node lowered}, CompatibleExpressionTyped.Syntax source id →
      source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope id lowered)
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
    (ordinary : CompatibleExpressionTyped.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (sourceSignatures : context.signatures = values.checked.signatures)
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
  exact CompatibleExpressionTyped.tree_of_contextual ordinary unique closed residual declarations sourceSignatures
    syntaxValue found typed readExpression lowerRead leafLowerer generated

end Solcore.SourceSemantics.CoreLowering.TypedStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedStatementMeaning
/-! Finite semantics of typed fixed-scope compatible function sequences.
Discarded values receive a typed administrative slot before the remaining
statement tree runs, so later comparator closures capture a typed environment. The child
expression theorem is supplied by the concrete expression tree, rather than a
caller-provided runtime induction hypothesis. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedStatements
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

open CompatibleStatements (FlowRep BodyRep)

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
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension contextValid unique uninitialized missing in
/-- The entire finite source sequence determines a native execution. No child
execution or universal child meaning is a certificate premise. -/
theorem Tree.preserves {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree readFuel values source context solved reasonAt scope statements expected type code)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (trace : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before statements finalContext outcome after) :
    finalContext = context ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction tree generalizing mapping world actual before after store ξ outcome finalContext actualContext with
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
      CompatibleExpressionTyped.preserves functions extension program evidence contextValid unique uninitialized missing child expressionFound
        environments heaps locals agrees actualTyped childTrace
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
      CompatibleExpressionTyped.preserves functions extension program evidence contextValid unique uninitialized missing child expressionFound
        environments heaps locals agrees actualTyped childTrace
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
        CompatibleExpressionTyped.preserves functions extension program evidence contextValid unique uninitialized missing child expressionFound
          environments heaps locals agrees actualTyped (.fault failed)
      cases represented with
      | fault matched =>
        exact ⟨rfl, _, finalStore, finalMap, finalWorld, by rw [LoopRenaming.discard]; exact LocalSequence.discard_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        CompatibleExpressionTyped.preserves functions extension program evidence contextValid unique uninitialized missing child expressionFound
          environments heaps locals agrees actualTyped (.value childTrace)
      cases represented with
      | @value _ coreValue payload =>
        obtain ⟨same, value, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
          ih (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) tail
        refine ⟨same, value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata⟩
        rw [LoopRenaming.discard]
        rw [GenericExpressionMeaning.rename_prefix] at second
        exact LocalSequence.discard_success _ first second

include extension contextValid uninitialized missing in
/-- Every completed generated flow constructs its independent source trace.
The returned expression trace is derived from the actual native subtree. -/
theorem Tree.reflects {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree readFuel values source context solved reasonAt scope statements expected type code)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before statements context outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction tree generalizing mapping world actual before store finalStore ξ value actualContext with
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
        CompatibleExpressionTyped.reflects functions extension program evidence contextValid uninitialized missing child expressionFound
          environments heaps locals agrees actualTyped childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalLoop.returnValue_failure _ childEvaluation)
          exact ⟨_, after, finalMap, finalWorld, head_fault (.returnValue (lookupStatement?_sound found) form failed),
            .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        CompatibleExpressionTyped.reflects functions extension program evidence contextValid uninitialized missing child expressionFound
          environments heaps locals agrees actualTyped childEvaluation
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
        CompatibleExpressionTyped.reflects functions extension program evidence contextValid uninitialized missing child expressionFound
          environments heaps locals agrees actualTyped childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalLoop.returnValue_failure _ childEvaluation)
          exact ⟨_, after, finalMap, finalWorld, .fault (.tailExpression (lookupStatement?_sound found) form failed),
            .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        CompatibleExpressionTyped.reflects functions extension program evidence contextValid uninitialized missing child expressionFound
          environments heaps locals agrees actualTyped childEvaluation
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
        CompatibleExpressionTyped.reflects functions extension program evidence contextValid uninitialized missing child expressionFound
          environments heaps locals agrees actualTyped childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalSequence.discard_failure _ childEvaluation)
          exact ⟨_, after, finalMap, finalWorld, head_fault (.expression (lookupStatement?_sound found) form failed),
            .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        CompatibleExpressionTyped.reflects functions extension program evidence contextValid uninitialized missing child expressionFound
          environments heaps locals agrees actualTyped childEvaluation
      cases represented with
      | @value _ coreValue payload =>
        cases trace with
        | value childTrace =>
          obtain ⟨outcome, after, finalMap, finalWorld, tail, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
            ih (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees _)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds))
              (by simpa only [GenericExpressionMeaning.rename_prefix] using branch)
          exact ⟨outcome, after, finalMap, finalWorld,
            prepend (lookupStatement?_sound found) (not_tail form guard) (.expression (lookupStatement?_sound found) form childTrace) tail,
            represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata⟩

private theorem finish_rename (type : Ty) (flow : Expr) (fellThrough escaped : Word) (ξ : Renaming) :
    (finish type flow fellThrough escaped).rename ξ = finish type (flow.rename ξ) fellThrough escaped := by
  unfold finish CompatibleStatements.finish
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

include extension contextValid unique uninitialized missing in
/-- Finite preservation for the complete production function wrapper. -/
theorem Tree.body_preserves {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {flow : Expr}
    (tree : Tree readFuel values source context solved reasonAt scope statements expected type flow)
    (fellThrough escaped : Word)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (trace : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before statements finalContext outcome after) :
    finalContext = context ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((finish type flow fellThrough escaped).rename ξ) value finalStore ∧
      BodyRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨same, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    tree.preserves functions extension program evidence contextValid unique uninitialized missing environments heaps locals agrees actualTyped trace
  obtain ⟨result, completed, related⟩ := finish_from_flow functions fellThrough escaped represented evaluated
  exact ⟨same, result, finalStore, finalMap, finalWorld, by rw [finish_rename]; exact completed,
    related, finalHeaps, maps, worlds, frame, metadata⟩

include extension contextValid uninitialized missing in
/-- Completed full-body execution reflects into the independent source function
sequence, with the same final heap and all administrative-frame obligations. -/
theorem Tree.body_reflects {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {flow : Expr}
    (tree : Tree readFuel values source context solved reasonAt scope statements expected type flow)
    (fellThrough escaped : Word)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
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
    tree.reflects functions extension program evidence contextValid uninitialized missing environments heaps locals agrees actualTyped flowEvaluation
  obtain ⟨result, completed, related⟩ := finish_from_flow functions fellThrough escaped represented flowEvaluation
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated completed
  exact ⟨outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, frame, metadata⟩

end Solcore.SourceSemantics.CoreLowering.TypedStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedStatementMixedTree
/-! Typed expressions in arbitrarily mixed ordinary lexical bindings. Initializers belong to the
context before their binding; a failed initializer ends at that context. The
terminal fixed-scope statement tree closes every child semantic obligation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedStatementMixed
open Core Frontend SourceInference
abbrev Scope := SourceCoreLocalCell.Scope
abbrev ValuesContext := SourceCoreCompatibleValues.Context

abbrev absentRequest (source : TypedSource) (scope : Scope) (binder : TypedBinder) (payload : Ty) :
    SourceCoreSourceCells.Request := ⟨source, scope, Renaming.id, binder, payload, none⟩

abbrev initializedRequest := CompatibleStatementInitialized.request
abbrev sequence := CompatibleStatementInitialized.sequence

inductive Syntax (source : TypedSource) :
    SourceSemantics.Context → List StatementId → TypeSystem.Ty → Prop where
  | body {context statements expected} (syntaxTree : TypedStatements.Syntax source context statements expected) :
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
      (initializerSyntax : CompatibleExpressionTyped.Syntax source initializer)
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
      (body : TypedStatements.Tree readFuel values source context solved reasonAt scope statements expected type code) :
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
      (initial : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      (remaining : Tree layouts owner active frame globals onError readFuel values source
        solved reasonAt nextContext ((binder.id, lowered.type) :: scope) rest expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt
        context scope (id :: rest) expected type (sequence type lowered.expression annotation.expression body)

/-- Reuse the existing result-dependent lexical stopping relation. -/
abbrev Reached := CompatibleStatementMixed.Reached

end Solcore.SourceSemantics.CoreLowering.TypedStatementMixed
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedStatementMixedCertificates
/-! Successful production traversal extracts the marked binding spine. The
expression callback is static certificate extraction, never a runtime premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedStatementMixed
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
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → CompatibleExpressionTyped.Syntax source id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      CompatibleExpressionTyped.Tree readFuel values source sourceContext solved reasonAt scope id lowered)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context statements expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true selfReason = .ok code) :
    Tree layouts owner active frame globals onError readFuel values source solved reasonAt
      context scope statements expected type code := by
  induction syntaxTree generalizing scope fuel code with
  | body syntaxTree => exact .body (TypedStatements.tree_of_flow readPolicy (expressions _ closed residual sourceSignatures declarations) syntaxTree projection accepted)
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
        allocation annotation same (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
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
        (expressions context closed residual sourceSignatures declarations initializerSyntax initializerFound typed generated)
        allocation annotation same
        (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind lowered.type declarations declaration extended) projection generatedBody)

/-- The complete production body wrapper keeps the extracted binding spine. -/
theorem tree_of_body
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → CompatibleExpressionTyped.Syntax source id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      CompatibleExpressionTyped.Tree readFuel values source sourceContext solved reasonAt scope id lowered)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context statements expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
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
  exact ⟨flow, rfl, tree_of_flow readPolicy binderPolicy allocationPolicy expressions syntaxTree closed residual sourceSignatures declarations projection generated⟩
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
    (ordinary : CompatibleExpressionTyped.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
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
  apply tree_of_body readStatement ?_ sourceCells ?_ syntaxTree closed residual sourceSignatures declarations projection accepted
  · intro scope binder mono
    simp only [lowerBinder, SourceCoreGeneralFunctions.contextualBinder, mono, List.isEmpty_nil,
      ↓reduceIte, representationBinder]
  · intro sourceContext contextClosed contextResidual contextSignatures currentScope budget id node lowered currentDeclarations syntaxValue found typed generated
    rw [lowerExpression] at generated
    exact CompatibleExpressionTyped.tree_of_contextual ordinary unique contextClosed contextResidual currentDeclarations contextSignatures
      syntaxValue found typed readExpression lowerRead leafLowerer generated

end Solcore.SourceSemantics.CoreLowering.TypedStatementMixed
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedStatementMixedMeaning
/-! Mixed ordinary lexical prefixes preserve the actual stopping context.
Every child expression and terminal statement body is interpreted by its
concrete static tree, with no semantic child/body premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedStatementMixed
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

/-- The same reached-prefix relation as the ordinary mixed profile. -/
abbrev LexicalResult := CompatibleStatementMixed.LexicalResult

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
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include definitions registered extension uninitialized missing in
/-- Every independent finite source trace through the binding prefix and its
concrete body is preserved under the real full native definition table. -/
theorem Tree.preserves {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId}
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
      body.preserves functions extension program evidence contextValid unique uninitialized missing environments heaps locals agrees actualTyped trace
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
        CompatibleExpressionTyped.preserves functions extension program evidence contextValid unique uninitialized missing initial initialFound
          environments heaps locals agrees actualTyped (.fault failed)
      cases represented with
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LanguageResult.bind_failure _ initialEval,
          .fault matched, finalHeaps, maps, worlds, preservation, metadata, _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
        CompatibleExpressionTyped.preserves functions extension program evidence contextValid unique uninitialized missing initial initialFound
          environments heaps locals agrees actualTyped (.value initialTrace)
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
include definitions registered extension uninitialized missing in
/-- Reflection constructs the independent source allocations from a completed
native run; no prior source trace or child expression execution is supplied. -/
theorem Tree.reflects {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId}
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
      body.reflects functions extension program evidence contextValid uninitialized missing environments heaps locals agrees actualTyped evaluated
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
      CompatibleExpressionTyped.reflects functions extension program evidence contextValid uninitialized missing initial initialFound
        environments heaps locals agrees actualTyped initialEval
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

include definitions registered extension uninitialized missing in
/-- Initialization failure preserves its exact old-context effects. Success
allocates only afterward, then uses the concrete remaining binding tree. -/
theorem Tree.body_preserves {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId}
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
    tree.preserves functions definitions registered extension program evidence uninitialized missing contextValid unique
      environments heaps locals agrees actualTyped reference read unmapped trace
  obtain ⟨result, completed, related⟩ := finish_from_flow functions fellThrough escaped represented evaluated
  exact ⟨result, finalStore, finalMap, finalWorld, by rw [finish_rename]; exact completed,
    related, finalHeaps, maps, worlds, frame, metadata, lexical⟩

include definitions registered extension uninitialized missing in
/-- Every completed generated expression determines whether initialization
failed in the old scope or the allocated binding's tail ran in the new scope. -/
theorem Tree.body_reflects {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId}
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
    tree.reflects functions definitions registered extension program evidence uninitialized missing contextValid
      environments heaps locals agrees actualTyped reference read unmapped flowEvaluation
  obtain ⟨result, completed, related⟩ := finish_from_flow functions fellThrough escaped represented flowEvaluation
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated completed
  exact ⟨resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, frame, metadata, lexical⟩

end Solcore.SourceSemantics.CoreLowering.TypedStatementMixed
end
