import Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticTokenPlan
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping

/-! Full original body typing and genuine table reachability supply raw typing
at every retained assignment and unary occurrence. Contexts come from the
original Source judgments, including nested lambdas and ordered header items.
Synthetic direct callees are retained only as terminal reference leaves. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SourceDiagnosticTyping
open Core Frontend SourceInference

variable {source : TypedSource}

private inductive TypedNode (source : TypedSource) : NodeId → Prop where
  | expression {context id type} (typed : ExpressionHasType source context id type) :
      TypedNode source (.expression id)
  | statement {control context id final facts}
      (typed : StatementHasType source control context id final facts) :
      TypedNode source (.statement id)
  | leaf {id node} (contains : ContainsExpression source id node)
      (empty : node.form.references = []) : TypedNode source (.expression id)

private theorem expressions_member {context : SourceSemantics.Context}
    {ids : List ExpressionId} {types : List TypeSystem.Ty}
    (typed : ExpressionsHaveTypes source context ids types) {id : ExpressionId} (member : id ∈ ids) :
    ∃ type, ExpressionHasType source context id type := by
  induction ids generalizing types with
  | nil => simp at member
  | cons head rest ih =>
    cases typed with
    | cons first tail =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, first⟩
      · exact ih tail member

private theorem statements_member {control : ControlContext} {context final : SourceSemantics.Context}
    {ids : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context ids final facts) {id : StatementId} (member : id ∈ ids) :
    ∃ localContext localFinal localFacts, StatementHasType source control localContext id localFinal localFacts := by
  induction ids generalizing context final facts with
  | nil => simp at member
  | cons head rest ih =>
    cases typed with
    | singleton first =>
      have same := List.mem_singleton.mp member
      subst id
      exact ⟨_, _, _, first⟩
    | cons first tail =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, _, _, first⟩
      · exact ih tail member

private theorem items_member {control : ControlContext} {context final : SourceSemantics.Context}
    {items : List ForItemForm} (typed : ForItemsHaveType source control context items final)
    {item : ForItemForm} (member : item ∈ items) :
    ∃ localContext localFinal, ForItemHasType source control localContext item localFinal := by
  induction items generalizing context final with
  | nil => simp at member
  | cons head rest ih =>
    cases typed with
    | cons first tail =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, _, first⟩
      · exact ih tail member

private theorem cases_member {control : ControlContext} {context : SourceSemantics.Context}
    {type : TypeSystem.Ty} {arms : List TypedMatchCase} {facts : List BodyFacts}
    (typed : MatchCasesHaveType source control context type arms facts)
    {arm : TypedMatchCase} (member : arm ∈ arms) :
    ∃ facts, MatchCaseHasType source control context type arm facts := by
  induction arms generalizing facts with
  | nil => simp at member
  | cons head rest ih =>
    cases typed with
    | cons first tail =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, first⟩
      · exact ih tail member

private theorem expressions_references {context : SourceSemantics.Context}
    {ids : List ExpressionId} {types : List TypeSystem.Ty}
    (typed : ExpressionsHaveTypes source context ids types) {child : NodeId}
    (member : child ∈ ids.map NodeId.expression) : TypedNode source child := by
  obtain ⟨id, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨type, typed⟩ := expressions_member typed present
  exact .expression typed

private theorem statements_references {control : ControlContext} {context final : SourceSemantics.Context}
    {ids : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context ids final facts) {child : NodeId}
    (member : child ∈ ids.map NodeId.statement) : TypedNode source child := by
  obtain ⟨id, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨localContext, localFinal, localFacts, typed⟩ := statements_member typed present
  exact .statement typed

private theorem expression_single {context : SourceSemantics.Context} {id : ExpressionId} {type : TypeSystem.Ty}
    (typed : ExpressionHasType source context id type) {child : NodeId}
    (member : child ∈ [NodeId.expression id]) : TypedNode source child := by
  have same := List.mem_singleton.mp member
  subst child
  exact .expression typed

private theorem projections_references {context : SourceSemantics.Context}
    {initial final : TypeSystem.Ty} {projections : List PlaceProjection}
    (typed : SourceProjectionsHaveType source context initial projections final) {child : NodeId}
    (member : child ∈ projections.flatMap PlaceProjection.references) : TypedNode source child := by
  induction projections generalizing initial with
  | nil => simp at member
  | cons projection rest ih =>
    cases typed with
    | index key tail =>
      rcases List.mem_append.mp member with member | member
      · exact expression_single key member
      · exact ih tail member
    | member selected tail =>
      exact ih tail (by simpa [PlaceProjection.references] using member)

private theorem place_references {context : SourceSemantics.Context} {place : PlaceResolution} {type : TypeSystem.Ty}
    (typed : SourcePlaceHasType source context place type) {child : NodeId}
    (member : child ∈ place.references) : TypedNode source child := by
  cases typed with
  | intro root projections same => exact projections_references projections member

private theorem assignment_references {context : SourceSemantics.Context} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (typed : SourceAssignmentHasType source context assignment operator rhs) {child : NodeId}
    (member : child ∈ assignment.references ++ [NodeId.expression rhs]) : TypedNode source child := by
  cases typed with
  | equal place right _ =>
    rcases List.mem_append.mp member with member | member
    · exact place_references place member
    · exact expression_single right member
  | wordCompound _ place right _ =>
    rcases List.mem_append.mp member with member | member
    · exact place_references place member
    · exact expression_single right member

private theorem unary_references {context : SourceSemantics.Context} {assignment : AssignmentResolution}
    (typed : SourceBitNotAssignmentValid source context assignment) {child : NodeId}
    (member : child ∈ assignment.references) : TypedNode source child := by
  cases typed with
  | intro place _ => exact place_references place member

private theorem item_references {control : ControlContext} {context final : SourceSemantics.Context}
    {item : ForItemForm} (typed : ForItemHasType source control context item final) {child : NodeId}
    (member : child ∈ item.references) : TypedNode source child := by
  cases typed with
  | letUninitialized => simp [ForItemForm.references] at member
  | letInitialized initial => exact expression_single initial (by simpa [ForItemForm.references] using member)
  | letInitializedGeneralized _ _ _ initial => exact expression_single initial (by simpa [ForItemForm.references] using member)
  | expression expression => exact expression_single expression member
  | assignValue assignment => exact assignment_references assignment member
  | assignBitNot assignment => exact unary_references assignment member

private theorem items_references {control : ControlContext} {context final : SourceSemantics.Context}
    {items : List ForItemForm} (typed : ForItemsHaveType source control context items final) {child : NodeId}
    (member : child ∈ items.flatMap ForItemForm.references) : TypedNode source child := by
  obtain ⟨item, present, reference⟩ := List.mem_flatMap.mp member
  obtain ⟨localContext, localFinal, typed⟩ := items_member typed present
  exact item_references typed reference

private theorem cases_references {control : ControlContext} {context : SourceSemantics.Context}
    {type : TypeSystem.Ty} {arms : List TypedMatchCase} {facts : List BodyFacts}
    (typed : MatchCasesHaveType source control context type arms facts) {child : NodeId}
    (member : child ∈ arms.flatMap TypedMatchCase.references) : TypedNode source child := by
  obtain ⟨arm, present, reference⟩ := List.mem_flatMap.mp member
  obtain ⟨facts, typed⟩ := cases_member typed present
  cases typed with
  | intro _ _ body => exact statements_references body reference

private theorem expression_form_references {context : SourceSemantics.Context}
    {form : ExpressionForm} {type : TypeSystem.Ty} {plan : ExpressionRequirementPlan}
    (typed : ExpressionFormHasRawType source context form type plan) {child : NodeId}
    (member : child ∈ form.references) : TypedNode source child := by
  cases typed with
  | literal => simp [ExpressionForm.references] at member
  | integerLiteral => simp [ExpressionForm.references] at member
  | reference => simp [ExpressionForm.references] at member
  | group inner => exact expression_single inner member
  | tuple elements => exact expressions_references elements member
  | unary operand => exact expression_single operand member
  | binary left right =>
    rcases List.mem_cons.mp member with rfl | member
    · exact .expression left
    · exact expression_single right member
  | conditional condition left right =>
    rcases List.mem_cons.mp member with rfl | member
    · exact .expression condition
    · rcases List.mem_cons.mp member with rfl | member
      · exact .expression left
      · exact expression_single right member
  | lambda _ _ body => exact statements_references body member
  | directCall callee _ arguments =>
    rcases List.mem_cons.mp member with rfl | member
    · cases callee with
      | intro contains form _ _ _ _ => exact .leaf contains (by simp [form, ExpressionForm.references])
    · exact expressions_references arguments member
  | builtinCall callee arguments =>
    rcases List.mem_cons.mp member with rfl | member
    · cases callee with
      | intro contains form _ _ _ => exact .leaf contains (by simp [form, ExpressionForm.references])
    · exact expressions_references arguments member
  | indirectCall callee arguments =>
    rcases List.mem_cons.mp member with rfl | member
    · exact .expression callee
    · exact expressions_references arguments member
  | constructor _ arguments => exact expressions_references arguments member
  | member base => exact expression_single base member
  | proxy => simp [ExpressionForm.references] at member
  | index base key =>
    rcases List.mem_cons.mp member with rfl | member
    · exact .expression base
    · exact expression_single key member

private theorem statement_form_references {control : ControlContext} {context final : SourceSemantics.Context}
    {form : StatementForm} (typed : Dynamic.StatementHasType.FormTyping source control context form final)
    {child : NodeId} (member : child ∈ form.references) : TypedNode source child := by
  cases typed with
  | letUninitialized => simp [StatementForm.references] at member
  | letInitialized initial => exact expression_single initial (by simpa [StatementForm.references] using member)
  | letInitializedGeneralized _ _ _ initial => exact expression_single initial (by simpa [StatementForm.references] using member)
  | returnUnit => simp [StatementForm.references] at member
  | returnValue value => exact expression_single value (by simpa [StatementForm.references] using member)
  | expressionValue expression => exact expression_single expression member
  | expressionDiscard expression => exact expression_single expression member
  | assignValue assignment => exact assignment_references assignment member
  | assignBitNot assignment => exact unary_references assignment member
  | ifWithoutElse condition body =>
    simp only [StatementForm.references, Option.getD_none, List.map_nil, List.append_nil, List.mem_append, List.mem_singleton] at member
    rcases member with rfl | member
    · exact .expression condition
    · exact statements_references body member
  | ifWithElse condition left right =>
    simp only [StatementForm.references, Option.getD_some, List.mem_append, List.mem_singleton] at member
    rcases member with (rfl | member) | member
    · exact .expression condition
    · exact statements_references left member
    · exact statements_references right member
  | block body => exact statements_references body member
  | matchWithoutDefault absent scrutinee arms =>
    simp only [StatementForm.references, MatchResolution.references, absent, Option.getD_none, List.map_nil, List.append_nil, List.mem_append] at member
    rcases member with member | member
    · exact expression_single scrutinee member
    · exact cases_references arms member
  | matchWithDefault present scrutinee arms fallback =>
    simp only [StatementForm.references, MatchResolution.references, present, Option.getD_some, List.mem_append] at member
    rcases member with (member | member) | member
    · exact expression_single scrutinee member
    · exact cases_references arms member
    · exact statements_references fallback member
  | forLoop initial condition body post =>
    simp only [StatementForm.references, List.mem_append] at member
    rcases member with ((member | member) | member) | member
    · exact items_references initial member
    · exact expression_single condition member
    · exact items_references post member
    · exact statements_references body member
  | whileLoop condition body =>
    rcases List.mem_cons.mp member with rfl | member
    · exact .expression condition
    · exact statements_references body member
  | breakStmt => simp [StatementForm.references] at member
  | continueStmt => simp [StatementForm.references] at member

private theorem same_node (unique : NodeOccurrencesUnique source) {id : NodeId} {left right : Node}
    (first : ContainsNode source id left) (second : ContainsNode source id right) : left = right := by
  have leftId : left.occurrenceId = id.occurrenceId := by
    simpa [Node.occurrenceId] using congrArg NodeId.occurrenceId first.2
  have rightId : right.occurrenceId = id.occurrenceId := by
    simpa [Node.occurrenceId] using congrArg NodeId.occurrenceId second.2
  exact Option.some.inj ((lookupNode?_complete unique first.1 leftId).symm.trans
    (lookupNode?_complete unique second.1 rightId))

private theorem TypedNode.child (unique : NodeOccurrencesUnique source) {parent child : NodeId}
    (typed : TypedNode source parent) (edge : DirectChild source parent child) : TypedNode source child := by
  obtain ⟨actual, actualContains, member⟩ := edge
  cases typed with
  | expression typed =>
    cases typed with
    | intro contains raw _ _ _ _ =>
      have same := same_node unique ⟨contains.1, congrArg NodeId.expression contains.2⟩ actualContains
      subst actual
      exact expression_form_references raw member
  | statement typed =>
    obtain ⟨node, contains, raw⟩ := Dynamic.StatementHasType.formTyping typed
    have same := same_node unique ⟨contains.1, congrArg NodeId.statement contains.2⟩ actualContains
    subst actual
    exact statement_form_references raw member
  | leaf contains empty =>
    have same := same_node unique ⟨contains.1, congrArg NodeId.expression contains.2⟩ actualContains
    subst actual
    simp [nodeChildIds, Node.references, empty] at member

/-- Every actual retained statement has its original Source typing in some
real lexical context. Full root typing and graph reachability include lambda
bodies, all match arms and all statically typed suffixes. -/
theorem statement_at (unique : NodeOccurrencesUnique source) (reachable : AllNodesReachable source)
    {context : SourceSemantics.Context} {expected : TypeSystem.Ty} {facts : BodyFacts}
    (bodyTyped : BodyHasType source context expected facts) {id : StatementId} {node : StatementNode}
    (found : source.lookupStatement? id = some node) :
    ∃ control localContext localFinal localFacts,
      StatementHasType source control localContext id localFinal localFacts := by
  obtain ⟨final, rootsTyped, noExpressions, _completes⟩ := bodyTyped
  have typedReachable : ∀ {root}, Reachable source root → TypedNode source root := by
    intro root reached
    induction reached with
    | @root root member =>
      cases root with
      | expression expression => exact False.elim (noExpressions expression member)
      | statement statement =>
        have present : statement ∈ source.roots.filterMap (fun root => match root with
            | .statement statement => some statement | .expression _ => none) :=
          List.mem_filterMap.mpr ⟨.statement statement, member, rfl⟩
        obtain ⟨localContext, localFinal, localFacts, typed⟩ := statements_member rootsTyped present
        exact .statement typed
    | child _ edge ih => exact ih.child unique edge
  have contained := lookupStatement?_sound found
  have typed := typedReachable (reachable (.statement node) contained.1)
  change TypedNode source (.statement node.id) at typed
  rw [contained.2] at typed
  cases typed with
  | statement typed => exact ⟨_, _, _, _, typed⟩

private theorem item_unary {control : ControlContext} {context final : SourceSemantics.Context}
    {items : List ForItemForm} {assignment : AssignmentResolution}
    (typed : ForItemsHaveType source control context items final) (member : .assignBitNot assignment ∈ items) :
    ∃ localContext, SourceBitNotAssignmentValid source localContext assignment := by
  obtain ⟨localContext, localFinal, typed⟩ := items_member typed member
  cases typed with
  | assignBitNot typed => exact ⟨_, typed⟩

private theorem item_operand {control : ControlContext} {context final : SourceSemantics.Context}
    {items : List ForItemForm} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (typed : ForItemsHaveType source control context items final) (member : .assignValue assignment operator rhs ∈ items) :
    ∃ localContext, SourceAssignmentHasType source localContext assignment operator rhs := by
  obtain ⟨localContext, localFinal, typed⟩ := items_member typed member
  cases typed with
  | assignValue typed => exact ⟨_, typed⟩

/-- Genuine raw assignment and unary typing covers every actual lookup
occurrence and each ordered initializer/post member of a retained for node. -/
theorem diagnostic_typed_of_body (unique : NodeOccurrencesUnique source) (reachable : AllNodesReachable source)
    {context : SourceSemantics.Context} {expected : TypeSystem.Ty} {facts : BodyFacts}
    (bodyTyped : BodyHasType source context expected facts) :
    EmittedDiagnosticTokenPlan.UnaryTyped source ∧ AssignmentDiagnosticOrigins.OperandsTyped source := by
  have formTyped : ∀ {id node}, source.lookupStatement? id = some node →
      ∃ control localContext localFinal, Dynamic.StatementHasType.FormTyping source control localContext node.form localFinal := by
    intro id node found
    obtain ⟨control, localContext, localFinal, localFacts, typed⟩ := statement_at unique reachable bodyTyped found
    obtain ⟨actual, contains, raw⟩ := Dynamic.StatementHasType.formTyping typed
    have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
    subst actual
    exact ⟨_, _, _, raw⟩
  constructor
  · intro site assignment origin
    cases origin with
    | statement found form =>
      obtain ⟨control, localContext, localFinal, raw⟩ := formTyped found
      rw [form] at raw
      cases raw with
      | assignBitNot typed => exact ⟨_, typed⟩
    | header found form member =>
      obtain ⟨control, localContext, localFinal, raw⟩ := formTyped found
      rw [form] at raw
      cases raw with
      | forLoop initial _ _ post =>
        rcases List.mem_append.mp member with member | member
        · exact item_unary initial member
        · exact item_unary post member
  · intro site assignment operator rhs origin
    cases origin with
    | statement found form =>
      obtain ⟨control, localContext, localFinal, raw⟩ := formTyped found
      rw [form] at raw
      cases raw with
      | assignValue typed => exact ⟨_, typed⟩
    | header found form member =>
      obtain ⟨control, localContext, localFinal, raw⟩ := formTyped found
      rw [form] at raw
      cases raw with
      | forLoop initial _ _ post =>
        rcases List.mem_append.mp member with member | member
        · exact item_operand initial member
        · exact item_operand post member

/-- The exact original whole-program invocation certificate contains both
full root typing and the stronger structural reachability layer. -/
theorem diagnostic_typed_of_certificate {program : Program} {body : Dynamic.BodyInstance}
    {types : List TypeSystem.Ty} {context : SourceSemantics.Context} {facts : BodyFacts}
    (certificate : Dynamic.BodyInstanceTypingCertificate program body types context facts) :
    EmittedDiagnosticTokenPlan.UnaryTyped body.source ∧ AssignmentDiagnosticOrigins.OperandsTyped body.source :=
  diagnostic_typed_of_body certificate.graph_closed.wellFormed.nodeOccurrencesUnique
    certificate.graph_closed.allNodesReachable certificate.typing.body_typed

/-- The genuine selected Header derives its own complete certificate from
original program typing. The original frame authenticates the full Source. -/
theorem header_diagnostic_typed {checked : CallableAncestryPairedLookup.Checked} {base : CallableAncestryPairedLookup.Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
    {definitions : DataEnvironment} {program : Program}
    (header : RecursiveNamedCatalog.Header prepared values definitions program)
    (wellFormed : ProgramWellFormed program) :
    EmittedDiagnosticTokenPlan.UnaryTyped header.function.source ∧ AssignmentDiagnosticOrigins.OperandsTyped header.function.source := by
  obtain ⟨facts, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  simpa only [header.frame.source] using diagnostic_typed_of_certificate certificate.toBodyInstanceTypingCertificate

end Solcore.SourceSemantics.CoreLowering.SourceDiagnosticTyping
