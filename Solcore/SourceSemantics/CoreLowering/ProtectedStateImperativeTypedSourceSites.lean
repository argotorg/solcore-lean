import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeSourceSites
import Solcore.SourceSemantics.Dynamic.WholeLanguagePreservation

/-! Original Source statement typing accompanies compiler syntax at actual
sites. Assignment and loop judgments come from that Source receipt. Tail typing
is transported through the actual fallthrough context by the existing Source
context proof; no execution or compiler Tree fold is added. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeTypedSourceSites
open Frontend SourceInference
open RecursiveNamedLexicalContracts.Stateful.WithReady

variable {source : TypedSource} {expressionSyntax : ExpressionId → Prop}

def Statements (source : TypedSource) (context : SourceSemantics.Context)
    (statements : List StatementId) : Prop :=
  ∃ control final facts, StatementsHaveType source control context statements final facts

def Head (source : TypedSource) (context : SourceSemantics.Context) (id : StatementId) : Prop :=
  ∃ control final facts, StatementHasType source control context id final facts

def Facts (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (context : SourceSemantics.Context) (mode : Bool) (statements : List StatementId)
    (expected : TypeSystem.Ty) : Prop :=
  ProtectedStateImperativeSourceSites.Facts source expressionSyntax context mode statements expected ∧
    Statements source context statements

def HeadFacts (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (context : SourceSemantics.Context) (id : StatementId) (expected : TypeSystem.Ty) : Prop :=
  ∃ mode rest, Facts source expressionSyntax context mode (id :: rest) expected

theorem head {context : SourceSemantics.Context} {id : StatementId} {rest : List StatementId}
    (typed : Statements source context (id :: rest)) : Head source context id := by
  obtain ⟨control, final, facts, typed⟩ := typed
  cases typed with
  | singleton typed => exact ⟨control, final, _, typed⟩
  | cons typed _ => exact ⟨control, _, _, typed⟩

private theorem actual_form {control : ControlContext} {context final : SourceSemantics.Context}
    {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source)
    (typed : StatementHasType source control context id final facts)
    (found : source.lookupStatement? id = some node) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨original, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping typed
  have same : original = node := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  exact same ▸ formTyped

theorem assignment {context : SourceSemantics.Context} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (unique : NodeOccurrencesUnique source) (typed : Head source context id)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs) :
    SourceAssignmentHasType source context assignment operator rhs := by
  obtain ⟨control, final, facts, typed⟩ := typed
  have original := actual_form unique typed found
  rw [form] at original
  cases original with
  | assignValue typing => exact typing

theorem bit_not {context : SourceSemantics.Context} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution}
    (unique : NodeOccurrencesUnique source) (typed : Head source context id)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .assignBitNot assignment) :
    SourceBitNotAssignmentValid source context assignment := by
  obtain ⟨control, final, facts, typed⟩ := typed
  have original := actual_form unique typed found
  rw [form] at original
  cases original with
  | assignBitNot typing => exact typing

theorem while_loop {context : SourceSemantics.Context} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {body : List StatementId}
    (unique : NodeOccurrencesUnique source) (typed : Head source context id)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .whileLoop condition body) :
    ExpressionHasType source context condition .bool ∧ Statements source context body := by
  obtain ⟨control, final, facts, typed⟩ := typed
  have original := actual_form unique typed found
  rw [form] at original
  cases original with
  | whileLoop conditionTyped bodyTyped => exact ⟨conditionTyped, _, _, _, bodyTyped⟩

theorem for_loop {context : SourceSemantics.Context} {id : StatementId} {node : StatementNode}
    {items post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (unique : NodeOccurrencesUnique source) (typed : Head source context id)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .forLoop items condition post body) :
    ∃ control loopContext postContext bodyFinal bodyFacts,
      ForItemsHaveType source control context items loopContext ∧
      ExpressionHasType source loopContext condition .bool ∧
      StatementsHaveType source control.enterLoop loopContext body bodyFinal bodyFacts ∧
      ForItemsHaveType source control.enterLoop loopContext post postContext := by
  obtain ⟨control, final, facts, typed⟩ := typed
  have original := actual_form unique typed found
  rw [form] at original
  cases original with
  | forLoop initializerTyped conditionTyped bodyTyped postTyped =>
    exact ⟨control, _, _, _, _, initializerTyped, conditionTyped, bodyTyped, postTyped⟩

theorem block_typed {context : SourceSemantics.Context} {id : StatementId} {node : StatementNode}
    {body : List StatementId}
    (unique : NodeOccurrencesUnique source) (typed : Head source context id)
    (found : source.lookupStatement? id = some node) (form : node.form = .block body) :
    Statements source context body := by
  obtain ⟨control, final, facts, typed⟩ := typed
  have original := actual_form unique typed found
  rw [form] at original
  cases original with
  | block bodyTyped => exact ⟨control, _, _, bodyTyped⟩

theorem branch_typed {context : SourceSemantics.Context} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {thenBody : List StatementId} {elseBody : Option (List StatementId)}
    (boolean : Bool) (unique : NodeOccurrencesUnique source) (typed : Head source context id)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody) :
    Statements source context (if boolean then thenBody else elseBody.getD []) := by
  obtain ⟨control, final, facts, typed⟩ := typed
  have original := actual_form unique typed found
  rw [form] at original
  cases original with
  | ifWithoutElse _ thenTyped =>
    cases boolean
    · exact ⟨control, context, _, .nil _ _⟩
    · exact ⟨control, _, _, thenTyped⟩
  | ifWithElse _ thenTyped elseTyped =>
    cases boolean
    · exact ⟨control, _, _, elseTyped⟩
    · exact ⟨control, _, _, thenTyped⟩

theorem tail_typed {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {context nextContext : SourceSemantics.Context} {id : StatementId} {rest : List StatementId}
    {environment next : Dynamic.Environment} {before after : Dynamic.Heap}
    (graph : OccurrenceGraphWellFormed source)
    (typed : Statements source context (id :: rest))
    (executed : Dynamic.StatementExecutes program context evidence source environment before id
      nextContext (.fallthrough next) after) :
    Statements source nextContext rest := by
  obtain ⟨control, final, facts, typed⟩ := typed
  cases typed with
  | singleton _ => exact ⟨control, nextContext, _, .nil _ _⟩
  | cons headTyped tailTyped =>
    have same := executed.final_context_of_typing graph headTyped
    exact same.symm ▸ ⟨control, final, _, tailTyped⟩

theorem block {context : SourceSemantics.Context} {id : StatementId}
    {expected : TypeSystem.Ty} {node : StatementNode} {body : List StatementId}
    (unique : NodeOccurrencesUnique source)
    (facts : HeadFacts source expressionSyntax context id expected)
    (found : source.lookupStatement? id = some node) (form : node.form = .block body) :
    Facts source expressionSyntax context false body expected := by
  obtain ⟨mode, rest, compiledSyntax, typed⟩ := facts
  exact ⟨ProtectedStateImperativeSourceSites.block ⟨mode, rest, compiledSyntax⟩ found form,
    block_typed unique (head typed) found form⟩

theorem branch {context : SourceSemantics.Context} {id : StatementId}
    {expected : TypeSystem.Ty} {node : StatementNode} {condition : ExpressionId}
    {thenBody : List StatementId} {elseBody : Option (List StatementId)}
    (boolean : Bool) (unique : NodeOccurrencesUnique source)
    (facts : HeadFacts source expressionSyntax context id expected)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody) :
    Facts source expressionSyntax context false (if boolean then thenBody else elseBody.getD []) expected := by
  obtain ⟨mode, rest, compiledSyntax, typed⟩ := facts
  exact ⟨ProtectedStateImperativeSourceSites.branch boolean ⟨mode, rest, compiledSyntax⟩ found form,
    branch_typed boolean unique (head typed) found form⟩

theorem tail {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {context nextContext : SourceSemantics.Context} {mode : Bool} {id : StatementId}
    {rest : List StatementId} {expected : TypeSystem.Ty} {node : StatementNode}
    {environment next : Dynamic.Environment} {before after : Dynamic.Heap}
    (graph : OccurrenceGraphWellFormed source)
    (facts : Facts source expressionSyntax context mode (id :: rest) expected)
    (found : source.lookupStatement? id = some node)
    (notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false)
    (executed : Dynamic.StatementExecutes program context evidence source environment before id
      nextContext (.fallthrough next) after) :
    Facts source expressionSyntax nextContext mode rest expected :=
  ⟨ProtectedStateImperativeSourceSites.tail graph.nodeOccurrencesUnique facts.1 found notTail executed,
    tail_typed graph facts.2 executed⟩

theorem sites (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (graph : OccurrenceGraphWellFormed source) :
    StaticSites (Facts source expressionSyntax) (HeadFacts source expressionSyntax)
      (ProtectedStateImperativeSourceSites.ExpressionFacts source) program evidence source where
  head := fun typed => ⟨_, _, typed⟩
  expression := fun ⟨mode, rest, compiledSyntax, _typed⟩ slot found =>
    ProtectedStateImperativeSourceSites.expression ⟨mode, rest, compiledSyntax⟩ slot found
  block := block graph.nodeOccurrencesUnique
  branch := fun boolean => branch boolean graph.nodeOccurrencesUnique
  tail := tail graph

end Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeTypedSourceSites
