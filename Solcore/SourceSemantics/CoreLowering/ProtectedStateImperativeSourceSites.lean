import Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalSourceSites
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchTree
import Solcore.SourceSemantics.CoreLowering.ForSourceViews
import Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatementComposition
import Solcore.SourceSemantics.CoreLowering.ReachableMatchContinuationMeaning

/-! Genuine imperative Source syntax supplies facts at actual statement and
expression sites. Tail facts follow the executed Source fallthrough prefix;
stopped branches need no facts for an unexecuted suffix. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeSourceSites
open Frontend SourceInference GenericImperativeMatch
open RecursiveNamedLexicalContracts.Stateful.WithReady

variable {source : TypedSource} {expressionSyntax : ExpressionId → Prop}

def Facts (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (context : SourceSemantics.Context) (mode : Bool) (statements : List StatementId)
    (expected : TypeSystem.Ty) : Prop :=
  Syntax source expressionSyntax context (.statements mode statements) expected

def HeadFacts (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (context : SourceSemantics.Context) (id : StatementId) (expected : TypeSystem.Ty) : Prop :=
  ∃ mode rest, Facts source expressionSyntax context mode (id :: rest) expected

abbrev ExpressionFacts := ProtectedStateLexicalSourceSites.ExpressionFacts

theorem expression {context : SourceSemantics.Context} {id : StatementId}
    {expected : TypeSystem.Ty} {child : ExpressionId} {node : ExpressionNode}
    (facts : HeadFacts source expressionSyntax context id expected)
    (slot : ExpressionSlot source id child)
    (found : source.lookupExpression? child = some node) :
    ExpressionFacts source context child node := by
  obtain ⟨mode, rest, typedSyntax⟩ := facts
  cases typedSyntax
  case body typed =>
    exact ProtectedStateLexicalSourceSites.expression ⟨mode, rest, typed⟩ slot found
  all_goals cases slot <;> simp_all [ExpressionFacts, ProtectedStateLexicalSourceSites.ExpressionFacts]

theorem block {context : SourceSemantics.Context} {id : StatementId}
    {expected : TypeSystem.Ty} {node : StatementNode} {statements : List StatementId}
    (facts : HeadFacts source expressionSyntax context id expected)
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements) :
    Facts source expressionSyntax context false statements expected := by
  obtain ⟨mode, rest, typedSyntax⟩ := facts
  cases typedSyntax
  case body typed =>
    exact .body (ProtectedStateLexicalSourceSites.block ⟨mode, rest, typed⟩ found form)
  all_goals simp_all [Facts]

theorem branch {context : SourceSemantics.Context} {id : StatementId}
    {expected : TypeSystem.Ty} {node : StatementNode} {condition : ExpressionId}
    {thenBody : List StatementId} {elseBody : Option (List StatementId)}
    (boolean : Bool) (facts : HeadFacts source expressionSyntax context id expected)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody) :
    Facts source expressionSyntax context false (if boolean then thenBody else elseBody.getD []) expected := by
  obtain ⟨mode, rest, typedSyntax⟩ := facts
  cases typedSyntax
  case body typed =>
    exact .body (ProtectedStateLexicalSourceSites.branch boolean ⟨mode, rest, typed⟩ found form)
  all_goals cases boolean <;> simp_all [Facts]

theorem tail {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {context nextContext : SourceSemantics.Context} {mode : Bool} {id : StatementId}
    {rest : List StatementId} {expected : TypeSystem.Ty} {node : StatementNode}
    {environment next : Dynamic.Environment} {before after : Dynamic.Heap}
    (unique : NodeOccurrencesUnique source)
    (typedSyntax : Facts source expressionSyntax context mode (id :: rest) expected)
    (found : source.lookupStatement? id = some node)
    (notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false)
    (executed : Dynamic.StatementExecutes program context evidence source environment before id
      nextContext (.fallthrough next) after) :
    Facts source expressionSyntax nextContext mode rest expected := by
  cases typedSyntax with
  | body typed =>
    exact .body (ProtectedStateLexicalSourceSites.tail unique typed found notTail executed)
  | uninitialized found form declaration monomorphic extended ordinary remaining =>
    obtain ⟨actualExtension, _⟩ := ScalarStatementViews.letUninitialized unique (lookupStatement?_sound found) form executed
    exact Dynamic.BinderExtends.functional extended actualExtension ▸ remaining
  | initialized found form declaration monomorphic extended ordinary initializerFound sourceType initializerTyped initializerSyntax remaining =>
    obtain ⟨actualExtension, _⟩ := ScalarStatementViews.letInitialized unique (lookupStatement?_sound found) form monomorphic executed
    exact Dynamic.BinderExtends.functional extended actualExtension ▸ remaining
  | discard found form guard sourceType expressionFound typed value remaining =>
    obtain ⟨same, _⟩ := ScalarStatementViews.expression unique (lookupStatement?_sound found) form executed
    exact same.symm ▸ remaining
  | block found form sourceType inner remaining =>
    obtain ⟨same, _⟩ := ScalarStatementViews.block unique (lookupStatement?_sound found) form executed
    exact same.symm ▸ remaining
  | ifThen found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax remaining =>
    obtain ⟨same, _⟩ := ScalarStatementViews.ifThen unique (lookupStatement?_sound found) form executed
    exact same.symm ▸ remaining
  | breaking found form =>
    obtain ⟨_, impossible, _⟩ := ScalarStatementViews.breaking unique (lookupStatement?_sound found) form executed
    cases impossible
  | continuing found form =>
    obtain ⟨_, impossible, _⟩ := ScalarStatementViews.continuing unique (lookupStatement?_sound found) form executed
    cases impossible
  | whileLoop found form conditionFound conditionType typed conditionSyntax loopBody remaining =>
    obtain ⟨same, _⟩ := ScalarStatementViews.whileLoop unique (lookupStatement?_sound found) form executed
    exact same.symm ▸ remaining
  | assign found form sourceTyped writable rightTyped profile children remaining =>
    obtain ⟨same, _⟩ := ScalarStatementViews.assignValue unique (lookupStatement?_sound found) form executed
    exact same.symm ▸ remaining
  | forLoop found form sourceType initial remaining =>
    obtain ⟨same, _⟩ := ForSourceViews.success unique (lookupStatement?_sound found) form executed
    exact same.symm ▸ remaining
  | bitNot found form writable bare profile remaining =>
    obtain ⟨same, _⟩ := CompatibleBitNotStatements.bitNot_view unique (lookupStatement?_sound found) form executed
    exact same.symm ▸ remaining
  | matchWith found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped hiddenOrdinary armsOrdinary children remaining =>
    obtain ⟨same, _⟩ := DataMatchSourceTrace.of_outcome unique (lookupStatement?_sound found) form (.control executed)
    exact same.symm ▸ remaining
  | terminalBlock unique found form sourceType inner stops =>
    cases GenericLexicalStatements.block_terminates unique found form stops executed
  | terminalIf unique found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax thenStops elseStops =>
    cases GenericLexicalStatements.conditional_terminates unique found form thenStops elseStops executed
  | terminalMatch unique found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped hiddenOrdinary armsOrdinary children stops =>
    cases ReachableMatchContinuations.DefaultStopped.terminates unique stops executed
  | scopedBlock found form inner remaining =>
    obtain ⟨same, _⟩ := ScalarStatementViews.block unique (lookupStatement?_sound found) form executed
    exact same.symm ▸ remaining

theorem sites (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (unique : NodeOccurrencesUnique source) :
    StaticSites (Facts source expressionSyntax) (HeadFacts source expressionSyntax)
      (ExpressionFacts source) program evidence source where
  head := fun typedSyntax => ⟨_, _, typedSyntax⟩
  expression := expression
  block := block
  branch := branch
  tail := tail unique

end Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeSourceSites
