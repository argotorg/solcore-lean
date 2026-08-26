import Solcore.Surface.Multi.Location
import Solcore.Surface.Multi.ParserCore

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar

/-- The complete location fragment exposed by one parser rule value. -/
abbrev RuleLocationView := LocationFragment

namespace RuleLocationView

/-- Retain the optional comma that separates repeated forall binders. -/
def ofOptionalCommaValue : OptionalCommaValue → RuleLocationView
  | .absent => LocationFragment.empty
  | .present comma => LocationFragment.raw comma

@[simp] theorem ofOptionalCommaValue_absent_roots :
    (ofOptionalCommaValue .absent).roots = [] := by
  rfl

@[simp] theorem ofOptionalCommaValue_present_roots (comma : SourceSpan) :
    (ofOptionalCommaValue (.present comma)).roots = [comma] := by
  rfl

/-- Merge the complete fragments of a nonempty predicate list. -/
def ofPredicateList (predicates : NonemptyList Predicate) :
    RuleLocationView :=
  LocationFragment.merge
    (LocationFragment.ofPredicate predicates.head ::
      predicates.tail.map LocationFragment.ofPredicate)

/-- The rule-level predicate-list view agrees with the public nonempty
location combinator. -/
@[simp] theorem ofPredicateList_eq_ofNonempty
    (predicates : NonemptyList Predicate) :
    ofPredicateList predicates =
      LocationFragment.ofNonempty LocationFragment.ofPredicate predicates := by
  rcases predicates with ⟨head, tail⟩
  apply LocationFragment.eq_of_fields <;>
    simp [ofPredicateList, LocationFragment.ofNonempty,
      LocationFragment.ofList]

@[simp] private theorem predicateList_roots (predicates : List Predicate) :
    (predicates.map LocationFragment.ofPredicate).flatMap
        (fun fragment => fragment.roots) =
      predicates.map (fun predicate => predicate.span) := by
  induction predicates with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [inductionHypothesis]

@[simp] theorem ofPredicateList_roots
    (predicates : NonemptyList Predicate) :
    (ofPredicateList predicates).roots =
      predicates.head.span ::
        predicates.tail.map (fun predicate => predicate.span) := by
  simp [ofPredicateList]

@[simp] private theorem expression_roots (expression : Expression) :
    (LocationFragment.ofExpression expression).roots = [expression.span] := by
  cases expression
  rfl

@[simp] private theorem expressionList_roots (expressions : List Expression) :
    (expressions.map LocationFragment.ofExpression).flatMap
        (fun fragment => fragment.roots) =
      expressions.map (fun expression => expression.span) := by
  induction expressions with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [inductionHypothesis]

/-- Retain punctuation and operands before a postfix part is folded. -/
def ofPostfixPartValue : PostfixPartValue → RuleLocationView
  | .call openParen arguments closeParen =>
      LocationFragment.merge
        ([LocationFragment.raw openParen] ++
          arguments.map LocationFragment.ofExpression ++
          [LocationFragment.raw closeParen])
  | .select dot field =>
      LocationFragment.merge [
        LocationFragment.raw dot,
        LocationFragment.ofIdentifier field
      ]
  | .index openBracket index closeBracket =>
      LocationFragment.merge [
        LocationFragment.raw openBracket,
        LocationFragment.ofExpression index,
        LocationFragment.raw closeBracket
      ]

@[simp] theorem ofPostfixPartValue_call_roots
    (openParen closeParen : SourceSpan) (arguments : List Expression) :
    (ofPostfixPartValue (.call openParen arguments closeParen)).roots =
      openParen :: arguments.map (fun argument => argument.span) ++
        [closeParen] := by
  simp [ofPostfixPartValue]

@[simp] theorem ofPostfixPartValue_select_roots
    (dot : SourceSpan) (field : IdentifierOccurrence) :
    (ofPostfixPartValue (.select dot field)).roots =
      [dot, field.span] := by
  simp [ofPostfixPartValue]

@[simp] theorem ofPostfixPartValue_index_roots
    (openBracket closeBracket : SourceSpan) (index : Expression) :
    (ofPostfixPartValue (.index openBracket index closeBracket)).roots =
      [openBracket, index.span, closeBracket] := by
  simp [ofPostfixPartValue]

/--
Expose every location retained by a semantic value of any source grammar rule.
The dependent domain prevents a value from being paired with the wrong rule.
-/
def ofRuleValue : (rule : GrammarRuleId) →
    RuleValue rule → RuleLocationView
  | .module, value => LocationFragment.ofParsedModule value
  | .topItem, value => LocationFragment.ofTopItem value
  | .moduleRef, value => LocationFragment.ofModuleReference value
  | .importDecl, value => LocationFragment.ofImportDecl value
  | .importEntry, value => LocationFragment.ofImportSelectorEntry value
  | .hidingClause, value => LocationFragment.ofHidingClause value
  | .exportDecl, value => LocationFragment.ofExportDecl value
  | .localExportEntry, value => LocationFragment.ofExportEntry value
  | .remoteExportEntry, value => LocationFragment.ofRemoteExportEntry value
  | .exportItem, value => LocationFragment.ofExportItem value
  | .constructorSelection, value =>
      LocationFragment.ofConstructorSelection value
  | .pragmaDecl, value => LocationFragment.ofPragmaDecl value
  | .genericPrefix, value => LocationFragment.ofGenericPrefix value
  | .forallClause, value => LocationFragment.ofForallClause value
  | .forallBinder, value => LocationFragment.ofForallBinder value
  | .optionalComma, value => ofOptionalCommaValue value
  | .predicateList, value => ofPredicateList value
  | .predicate, value => LocationFragment.ofPredicate value
  | .functionSignature, value => LocationFragment.ofFunctionSignature value
  | .functionDecl, value => LocationFragment.ofFunctionDecl value
  | .classMethod, value => LocationFragment.ofClassMethodDecl value
  | .dataDecl, value => LocationFragment.ofDataDecl value
  | .dataConstructor, value => LocationFragment.ofDataConstructor value
  | .typeAliasDecl, value => LocationFragment.ofTypeAliasDecl value
  | .classDecl, value => LocationFragment.ofClassDecl value
  | .instanceDecl, value => LocationFragment.ofInstanceDecl value
  | .instanceMethod, value => LocationFragment.ofFunctionDecl value
  | .contractDecl, value => LocationFragment.ofContractDecl value
  | .contractMember, value => LocationFragment.ofContractMember value
  | .fieldDecl, value => LocationFragment.ofFieldDecl value
  | .fallbackDecl, value => LocationFragment.ofFallbackDecl value
  | .contractConstructorDecl, value =>
      LocationFragment.ofContractConstructorDecl value
  | .parameter, value => LocationFragment.ofParameter value
  | .body, value => LocationFragment.ofBody value
  | .type, value => LocationFragment.ofTypeExpr value
  | .typeAtom, value => LocationFragment.ofTypeExpr value
  | .qualifiedName, value => LocationFragment.ofQualifiedName value
  | .statement, value => LocationFragment.ofStatement value
  | .letStatement, value => LocationFragment.ofStatement value
  | .letBinding, value => LocationFragment.ofLetBinding value
  | .returnStatement, value => LocationFragment.ofStatement value
  | .blockStatement, value => LocationFragment.ofStatement value
  | .breakStatement, value => LocationFragment.ofStatement value
  | .continueStatement, value => LocationFragment.ofStatement value
  | .assemblyStatement, value => LocationFragment.ofStatement value
  | .ifStatement, value => LocationFragment.ofStatement value
  | .forStatement, value => LocationFragment.ofStatement value
  | .forInitItem, value => LocationFragment.ofForInitItem value
  | .forPostItem, value => LocationFragment.ofForPostItem value
  | .matchStatement, value => LocationFragment.ofStatement value
  | .matchArm, value => LocationFragment.ofMatchArm value
  | .armStatement, value => LocationFragment.ofStatement value
  | .assignmentStatement, value => LocationFragment.ofStatement value
  | .assignmentOperator, value =>
      LocationFragment.ofAssignmentOperator value
  | .expressionStatement, value => LocationFragment.ofStatement value
  | .terminalExpression, value => LocationFragment.ofExpression value
  | .pattern, value => LocationFragment.ofPattern value
  | .expression, value => LocationFragment.ofExpression value
  | .annotation, value => LocationFragment.ofExpression value
  | .conditional, value => LocationFragment.ofExpression value
  | .logicalOr, value => LocationFragment.ofExpression value
  | .logicalAnd, value => LocationFragment.ofExpression value
  | .equality, value => LocationFragment.ofExpression value
  | .relational, value => LocationFragment.ofExpression value
  | .bitOr, value => LocationFragment.ofExpression value
  | .bitXor, value => LocationFragment.ofExpression value
  | .bitAnd, value => LocationFragment.ofExpression value
  | .additive, value => LocationFragment.ofExpression value
  | .multiplicative, value => LocationFragment.ofExpression value
  | .prefix, value => LocationFragment.ofExpression value
  | .postfix, value => LocationFragment.ofExpression value
  | .postfixPart, value => ofPostfixPartValue value
  | .atom, value => LocationFragment.ofExpression value
  | .lambda, value => LocationFragment.ofExpression value
  | .literal, value => LocationFragment.ofLiteral value

/-- The root spans that the enclosing parser reduction must contain. -/
def exposedSpans (rule : GrammarRuleId) (value : RuleValue rule) :
    List SourceSpan :=
  (ofRuleValue rule value).roots

@[simp] theorem exposedSpans_eq_roots
    (rule : GrammarRuleId) (value : RuleValue rule) :
    exposedSpans rule value = (ofRuleValue rule value).roots := by
  rfl

end RuleLocationView

end Solcore.Surface.Multi
