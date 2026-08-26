import Solcore.Surface.Multi.ExactTokenDeclaration

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar

/-- Select the body visitor from the source origin retained by the AST. -/
def bodyTokenPlanAny? (body : Body) : Option TokenPlan :=
  match body.payload.origin with
  | .braced .. => bodyTokenPlan? .braced body
  | .matchArm .. => bodyTokenPlan? .matchArm body

/-- Reconstruct the tokens contributed by one postfix operation before it is
folded over its receiver. -/
def postfixPartTokenPlan? : PostfixPartValue → Option TokenPlan
  | .call openParen arguments closeParen => do
      let argumentPlans ← expressionTokenPlans? arguments
      pure (.concat [
        .exact (.symbol .leftParen) openParen,
        .commaSeparated argumentPlans,
        .exact (.symbol .rightParen) closeParen])
  | .select dot field =>
      some (.append
        (.exact (.symbol .dot) dot)
        (identifierPlan field))
  | .index openBracket index closeBracket => do
      let indexPlan ← expressionTokenPlan? index
      pure (.concat [
        .exact (.symbol .leftBracket) openBracket,
        indexPlan,
        .exact (.symbol .rightBracket) closeBracket])

/-- The source-sensitive token-plan visitor selected by each of the seventy-five
public grammar rules. Rules sharing one AST carrier deliberately use the entry
point matching that rule's grammar context. -/
def ruleTokenPlan? :
    (rule : GrammarRuleId) → RuleValue rule → Option TokenPlan
  | .module, value => declarationModulePlan? value
  | .topItem, value => topItemPlan? value
  | .moduleRef, value => moduleReferencePlan? value
  | .importDecl, value => importDeclPlan? value
  | .importEntry, value => importSelectorEntryPlan? value
  | .hidingClause, value => hidingClausePlan? value
  | .exportDecl, value => exportDeclPlan? value
  | .localExportEntry, value => localExportEntryPlan? value
  | .remoteExportEntry, value => remoteExportEntryPlan? value
  | .exportItem, value => exportItemPlan? value
  | .constructorSelection, value => constructorSelectionPlan? value
  | .pragmaDecl, value => pragmaDeclPlan? value
  | .genericPrefix, value => genericPrefixPlan? value
  | .forallClause, value => forallClausePlan? value
  | .forallBinder, value => forallBinderPlan? value
  | .optionalComma, _ => some (.optional (.symbol .comma))
  | .predicateList, value => predicateListPlan? value
  | .predicate, value => predicatePlan? value
  | .functionSignature, value => functionSignaturePlan? value
  | .functionDecl, value => functionDeclPlan? value
  | .classMethod, value => classMethodDeclPlan? value
  | .dataDecl, value => dataDeclPlan? value
  | .dataConstructor, value => dataConstructorPlan? value
  | .typeAliasDecl, value => typeAliasDeclPlan? value
  | .classDecl, value => classDeclPlan? value
  | .instanceDecl, value => instanceDeclPlan? value
  | .instanceMethod, value => functionDeclPlan? value
  | .contractDecl, value => contractDeclPlan? value
  | .contractMember, value => contractMemberPlan? value
  | .fieldDecl, value => fieldDeclPlan? value
  | .fallbackDecl, value => fallbackDeclPlan? value
  | .contractConstructorDecl, value => contractConstructorDeclPlan? value
  | .parameter, value => parameterTokenPlan? value
  | .body, value => bodyTokenPlan? .braced value
  | .type, value => typeExprPlan? value
  | .typeAtom, value => typeAtomPlan? value
  | .qualifiedName, value => some (qualifiedNamePlan value)
  | .statement, value => statementTokenPlan? true value
  | .letStatement, value => statementTokenPlan? false value
  | .letBinding, value => letBindingTokenPlan? value
  | .returnStatement, value => statementTokenPlan? false value
  | .blockStatement, value => statementTokenPlan? false value
  | .breakStatement, value => statementTokenPlan? false value
  | .continueStatement, value => statementTokenPlan? false value
  | .assemblyStatement, value => statementTokenPlan? false value
  | .ifStatement, value => statementTokenPlan? false value
  | .forStatement, value => statementTokenPlan? false value
  | .forInitItem, value => forInitTokenPlan? value
  | .forPostItem, value => forPostTokenPlan? value
  | .matchStatement, value => statementTokenPlan? false value
  | .matchArm, value => matchArmTokenPlan? value
  | .armStatement, value => statementTokenPlan? true value
  | .assignmentStatement, value => statementTokenPlan? false value
  | .assignmentOperator, value => some (assignmentOperatorTokenPlan value)
  | .expressionStatement, value => statementTokenPlan? true value
  | .terminalExpression, value => expressionTokenPlan? value
  | .pattern, value => patternTokenPlan? value
  | .expression, value => expressionTokenPlan? value
  | .annotation, value => annotationExpressionTokenPlan? value
  | .conditional, value => conditionalExpressionTokenPlan? value
  | .logicalOr, value => logicalOrExpressionTokenPlan? value
  | .logicalAnd, value => logicalAndExpressionTokenPlan? value
  | .equality, value => equalityExpressionTokenPlan? value
  | .relational, value => relationalExpressionTokenPlan? value
  | .bitOr, value => bitOrExpressionTokenPlan? value
  | .bitXor, value => bitXorExpressionTokenPlan? value
  | .bitAnd, value => bitAndExpressionTokenPlan? value
  | .additive, value => additiveExpressionTokenPlan? value
  | .multiplicative, value => multiplicativeExpressionTokenPlan? value
  | .prefix, value => prefixExpressionTokenPlan? value
  | .postfix, value => postfixExpressionTokenPlan? value
  | .postfixPart, value => postfixPartTokenPlan? value
  | .atom, value => atomExpressionTokenPlan? value
  | .lambda, value => atomExpressionTokenPlan? value
  | .literal, value => some (literalTokenPlan value)

/-- Closed coverage check for the dependent rule-plan dispatcher. -/
theorem ruleTokenPlan_rule_count : allGrammarRuleIds.length = 75 := by
  rfl

end Solcore.Surface.Multi
