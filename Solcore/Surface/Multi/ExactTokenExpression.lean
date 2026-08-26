import Solcore.Surface.Multi.ExactToken

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

def literalTokenPlan (literal : Literal) : TokenPlan :=
  match literal.payload with
  | .decimal spelling digits =>
      .exact (.decimalLiteral spelling digits) literal.span
  | .hexadecimal spelling digits =>
      .exact (.hexadecimalLiteral spelling digits) literal.span
  | .string spelling decoded =>
      .exact (.stringLiteral spelling decoded) literal.span

def prefixOperatorTokenPlan
    (operator : Located PrefixOperator) : TokenPlan :=
  match operator.payload with
  | .logicalNot => .exact (.symbol .bang) operator.span

def infixOperatorTokenPlan
    (operator : Located InfixOperator) : TokenPlan :=
  let symbol :=
    match operator.payload with
    | .multiply => Symbol.star
    | .divide => .slash
    | .modulo => .percent
    | .add => .plus
    | .subtract => .minus
    | .bitAnd => .amp
    | .bitXor => .caret
    | .bitOr => .pipe
    | .less => .less
    | .greater => .greater
    | .lessEqual => .lessEqual
    | .greaterEqual => .greaterEqual
    | .equal => .equalEqual
    | .notEqual => .notEqual
    | .logicalAnd => .logicalAnd
    | .logicalOr => .logicalOr
  .exact (.symbol symbol) operator.span

def assignmentOperatorTokenPlan
    (operator : Located AssignmentOperator) : TokenPlan :=
  let symbol :=
    match operator.payload with
    | .equal => Symbol.equal
    | .addEqual => .plusEqual
    | .subtractEqual => .minusEqual
    | .bitXorEqual => .caretEqual
    | .bitAndEqual => .ampEqual
    | .bitOrEqual => .pipeEqual
    | .moduloEqual => .percentEqual
  .exact (.symbol symbol) operator.span

/-- Parameters carry a semantic marker payload; a marker of another retained
kind at the same span is not accepted. -/
def parameterTokenPlan? (parameter : Parameter) : Option TokenPlan := do
  let comptimePlan ←
    match parameter.payload.comptime with
    | none => some .empty
    | some marker =>
        if marker.payload = .comptimeModifier then
          some (.exact
            (.identifier ContextualKeyword.comptimeKw.spelling) marker.span)
        else
          none
  let typePlan ←
    match parameter.payload.type with
    | none => some .empty
    | some typeExpression => do
        let plan ← typeExprPlan? typeExpression
        pure (.append (.plain (.symbol .colon)) plan)
  pure (.enclose parameter.span (.concat [
    comptimePlan,
    identifierPlan parameter.payload.name,
    typePlan]))

private def parameterTokenPlans? :
    List Parameter → Option (List TokenPlan)
  | [] => some []
  | head :: tail => do
      let headPlan ← parameterTokenPlan? head
      let tailPlans ← parameterTokenPlans? tail
      pure (headPlan :: tailPlans)

/-- The source expression grammar level at which a subtree occurs. -/
inductive ExpressionTokenLevel where
  | annotation
  | conditional
  | logicalOr
  | logicalAnd
  | equality
  | relational
  | bitOr
  | bitXor
  | bitAnd
  | additive
  | multiplicative
  | prefix
  | postfix
  | atom
  deriving Repr, BEq, DecidableEq

namespace ExpressionTokenLevel

private def rank : ExpressionTokenLevel → Nat
  | .annotation => 13
  | .conditional => 12
  | .logicalOr => 11
  | .logicalAnd => 10
  | .equality => 9
  | .relational => 8
  | .bitOr => 7
  | .bitXor => 6
  | .bitAnd => 5
  | .additive => 4
  | .multiplicative => 3
  | .prefix => 2
  | .postfix => 1
  | .atom => 0

end ExpressionTokenLevel

/-- The context in which a body nonterminal is expected. -/
inductive BodyTokenContext where
  | braced
  | matchArm
  deriving Repr, BEq, DecidableEq

mutual

private def expressionTokenMeasure : Expression → Nat
  | ⟨_, payload⟩ => 1 + expressionPayloadTokenMeasure payload

private def expressionPayloadTokenMeasure : ExpressionPayload → Nat
  | .name _ => 1
  | .call callee arguments =>
      1 + expressionTokenMeasure callee + expressionListTokenMeasure arguments
  | .select receiver _ => 1 + expressionTokenMeasure receiver
  | .dotConstructor _ _ arguments =>
      1 + expressionListOptionTokenMeasure arguments
  | .proxy .. => 1
  | .literal .. => 1
  | .lambda _ _ body => 1 + bodyTokenMeasure body
  | .annotation expression _ => 1 + expressionTokenMeasure expression
  | .keywordConditional condition thenBranch elseBranch
  | .ternaryConditional condition thenBranch elseBranch =>
      1 + expressionTokenMeasure condition +
        expressionTokenMeasure thenBranch + expressionTokenMeasure elseBranch
  | .index receiver index =>
      1 + expressionTokenMeasure receiver + expressionTokenMeasure index
  | .prefix _ operand => 1 + expressionTokenMeasure operand
  | .infix _ left right =>
      1 + expressionTokenMeasure left + expressionTokenMeasure right
  | .tuple elements => 1 + expressionListTokenMeasure elements
  | .group inner => 1 + expressionTokenMeasure inner

private def expressionListTokenMeasure : List Expression → Nat
  | [] => 0
  | head :: tail =>
      1 + expressionTokenMeasure head + expressionListTokenMeasure tail

private def expressionListOptionTokenMeasure :
    Option (List Expression) → Nat
  | none => 0
  | some values => 1 + expressionListTokenMeasure values

private def expressionOptionTokenMeasure : Option Expression → Nat
  | none => 0
  | some value => 1 + expressionTokenMeasure value

private def expressionNonemptyTokenMeasure :
    NonemptyList Expression → Nat
  | ⟨head, tail⟩ =>
      1 + expressionTokenMeasure head + expressionListTokenMeasure tail

private def patternTokenMeasure : Pattern → Nat
  | ⟨_, payload⟩ => 1 + patternPayloadTokenMeasure payload

private def patternPayloadTokenMeasure : PatternPayload → Nat
  | .named _ arguments
  | .dotConstructor _ _ arguments =>
      1 + patternArgumentsTokenMeasure arguments
  | .wildcard .. => 1
  | .literal .. => 1
  | .comptime _ expression => 1 + expressionTokenMeasure expression
  | .tuple elements => 1 + patternListTokenMeasure elements
  | .group inner => 1 + patternTokenMeasure inner

private def patternArgumentsTokenMeasure :
    Option (NonemptyList Pattern) → Nat
  | none => 0
  | some arguments => 1 + patternNonemptyTokenMeasure arguments

private def patternNonemptyTokenMeasure :
    NonemptyList Pattern → Nat
  | ⟨head, tail⟩ =>
      1 + patternTokenMeasure head + patternListTokenMeasure tail

private def patternListTokenMeasure : List Pattern → Nat
  | [] => 0
  | head :: tail =>
      1 + patternTokenMeasure head + patternListTokenMeasure tail

private def bodyTokenMeasure : Body → Nat
  | ⟨_, payload⟩ => 1 + bodyPayloadTokenMeasure payload

private def bodyPayloadTokenMeasure : BodyPayload → Nat
  | ⟨_, statements⟩ => 1 + statementListTokenMeasure statements

private def bodyOptionTokenMeasure : Option Body → Nat
  | none => 0
  | some body => 1 + bodyTokenMeasure body

private def letBindingTokenMeasure : LetBinding → Nat
  | ⟨_, payload⟩ => 1 + letBindingPayloadTokenMeasure payload

private def letBindingPayloadTokenMeasure : LetBindingPayload → Nat
  | ⟨_, _, _, initializer⟩ =>
      1 + expressionOptionTokenMeasure initializer

private def forInitTokenMeasure : ForInitItem → Nat
  | ⟨_, payload⟩ => 1 + forInitPayloadTokenMeasure payload

private def forInitPayloadTokenMeasure : ForInitItemPayload → Nat
  | .letBinding binding => 1 + letBindingTokenMeasure binding
  | .assignment _ left right =>
      1 + expressionTokenMeasure left + expressionTokenMeasure right
  | .expression expression => 1 + expressionTokenMeasure expression

private def forInitListTokenMeasure : List ForInitItem → Nat
  | [] => 0
  | head :: tail =>
      1 + forInitTokenMeasure head + forInitListTokenMeasure tail

private def forPostTokenMeasure : ForPostItem → Nat
  | ⟨_, payload⟩ => 1 + forPostPayloadTokenMeasure payload

private def forPostPayloadTokenMeasure : ForPostItemPayload → Nat
  | .assignment _ left right =>
      1 + expressionTokenMeasure left + expressionTokenMeasure right
  | .expression expression => 1 + expressionTokenMeasure expression

private def forPostListTokenMeasure : List ForPostItem → Nat
  | [] => 0
  | head :: tail =>
      1 + forPostTokenMeasure head + forPostListTokenMeasure tail

private def matchArmTokenMeasure : MatchArm → Nat
  | ⟨_, payload⟩ => 1 + matchArmPayloadTokenMeasure payload

private def matchArmPayloadTokenMeasure : MatchArmPayload → Nat
  | ⟨patterns, body⟩ =>
      1 + patternNonemptyTokenMeasure patterns + bodyTokenMeasure body

private def matchArmListTokenMeasure : List MatchArm → Nat
  | [] => 0
  | head :: tail =>
      1 + matchArmTokenMeasure head + matchArmListTokenMeasure tail

private def matchArmNonemptyTokenMeasure :
    NonemptyList MatchArm → Nat
  | ⟨head, tail⟩ =>
      1 + matchArmTokenMeasure head + matchArmListTokenMeasure tail

private def statementTokenMeasure : Statement → Nat
  | ⟨_, payload⟩ => 1 + statementPayloadTokenMeasure payload

private def statementPayloadTokenMeasure : StatementPayload → Nat
  | .assignment _ left right =>
      1 + expressionTokenMeasure left + expressionTokenMeasure right
  | .letBinding binding => 1 + letBindingTokenMeasure binding
  | .block body => 1 + bodyTokenMeasure body
  | .expression expression _ => 1 + expressionTokenMeasure expression
  | .return value _ => 1 + expressionOptionTokenMeasure value
  | .match scrutinees arms _ =>
      1 + expressionNonemptyTokenMeasure scrutinees +
        matchArmNonemptyTokenMeasure arms
  | .assembly .. => 1
  | .ifThenElse condition thenBody elseBody =>
      1 + expressionTokenMeasure condition + bodyTokenMeasure thenBody +
        bodyOptionTokenMeasure elseBody
  | .forLoop initializers condition post body =>
      1 + forInitListTokenMeasure initializers +
        expressionTokenMeasure condition + forPostListTokenMeasure post +
        bodyTokenMeasure body
  | .break .. => 1
  | .continue .. => 1

private def statementListTokenMeasure : List Statement → Nat
  | [] => 0
  | head :: tail =>
      1 + statementTokenMeasure head + statementListTokenMeasure tail

end

private def expressionAtPlanMeasure
    (level : ExpressionTokenLevel) (expression : Expression) : Nat :=
  32 * expressionTokenMeasure expression + level.rank

private def expressionListPlanMeasure (values : List Expression) : Nat :=
  32 * expressionListTokenMeasure values + 31

private def expressionNonemptyPlanMeasure
    (values : NonemptyList Expression) : Nat :=
  32 * expressionNonemptyTokenMeasure values + 31

private def patternPlanMeasure (value : Pattern) : Nat :=
  32 * patternTokenMeasure value + 31

private def patternListPlanMeasure (values : List Pattern) : Nat :=
  32 * patternListTokenMeasure values + 31

private def patternNonemptyPlanMeasure
    (values : NonemptyList Pattern) : Nat :=
  32 * patternNonemptyTokenMeasure values + 31

private def bodyPlanMeasure (value : Body) : Nat :=
  32 * bodyTokenMeasure value + 31

private def letBindingPlanMeasure (value : LetBinding) : Nat :=
  32 * letBindingTokenMeasure value + 31

private def forInitPlanMeasure (value : ForInitItem) : Nat :=
  32 * forInitTokenMeasure value + 31

private def forInitListPlanMeasure (values : List ForInitItem) : Nat :=
  32 * forInitListTokenMeasure values + 31

private def forPostPlanMeasure (value : ForPostItem) : Nat :=
  32 * forPostTokenMeasure value + 31

private def forPostListPlanMeasure (values : List ForPostItem) : Nat :=
  32 * forPostListTokenMeasure values + 31

private def matchArmPlanMeasure (value : MatchArm) : Nat :=
  32 * matchArmTokenMeasure value + 31

private def matchArmListPlanMeasure (values : List MatchArm) : Nat :=
  32 * matchArmListTokenMeasure values + 31

private def matchArmNonemptyPlanMeasure
    (values : NonemptyList MatchArm) : Nat :=
  32 * matchArmNonemptyTokenMeasure values + 31

private def statementPlanMeasure (value : Statement) : Nat :=
  32 * statementTokenMeasure value + 31

private def statementListPlanMeasure (values : List Statement) : Nat :=
  32 * statementListTokenMeasure values + 31

local macro "solve_token_plan_termination" : tactic =>
  `(tactic|
    all_goals
      simp_all only [expressionAtPlanMeasure, ExpressionTokenLevel.rank,
        expressionListPlanMeasure, expressionNonemptyPlanMeasure,
        patternPlanMeasure, patternListPlanMeasure,
        patternNonemptyPlanMeasure, bodyPlanMeasure,
        letBindingPlanMeasure, forInitPlanMeasure,
        forInitListPlanMeasure, forPostPlanMeasure,
        forPostListPlanMeasure, matchArmPlanMeasure,
        matchArmListPlanMeasure, matchArmNonemptyPlanMeasure,
        statementPlanMeasure, statementListPlanMeasure,
        expressionTokenMeasure, expressionPayloadTokenMeasure,
        expressionListTokenMeasure, expressionListOptionTokenMeasure,
        expressionOptionTokenMeasure, expressionNonemptyTokenMeasure,
        patternTokenMeasure, patternPayloadTokenMeasure,
        patternArgumentsTokenMeasure, patternNonemptyTokenMeasure,
        patternListTokenMeasure, bodyTokenMeasure,
        bodyPayloadTokenMeasure, bodyOptionTokenMeasure,
        letBindingTokenMeasure, letBindingPayloadTokenMeasure,
        forInitTokenMeasure, forInitPayloadTokenMeasure,
        forInitListTokenMeasure, forPostTokenMeasure,
        forPostPayloadTokenMeasure, forPostListTokenMeasure,
        matchArmTokenMeasure, matchArmPayloadTokenMeasure,
        matchArmListTokenMeasure, matchArmNonemptyTokenMeasure,
        statementTokenMeasure, statementPayloadTokenMeasure,
        statementListTokenMeasure] <;> omega)

mutual

/-- Build the exact retained-token plan for an expression at one grammar
precedence level. Failure reports a structurally impossible parse tree. -/
def expressionTokenPlanAt?
    (level : ExpressionTokenLevel)
    (expression : Expression) : Option TokenPlan :=
  match level with
  | .annotation =>
      match _expressionEq : expression with
      | ⟨span, .annotation inner typeExpression⟩ => do
          let innerPlan ← expressionTokenPlanAt? .conditional inner
          let typePlan ← typeExprPlan? typeExpression
          pure (.enclose span (.concat [
            innerPlan,
            .plain (.symbol .colon),
            typePlan]))
      | _ => expressionTokenPlanAt? .conditional expression
  | .conditional =>
      match _expressionEq : expression with
      | ⟨span, .keywordConditional condition thenBranch elseBranch⟩ => do
          let conditionPlan ← expressionTokenPlanAt? .conditional condition
          let thenPlan ← expressionTokenPlanAt? .conditional thenBranch
          let elsePlan ← expressionTokenPlanAt? .conditional elseBranch
          pure (.enclose span (.concat [
            .plain (.hardKeyword .ifKw),
            conditionPlan,
            .plain (.identifier ContextualKeyword.thenKw.spelling),
            thenPlan,
            .plain (.hardKeyword .elseKw),
            elsePlan]))
      | ⟨span, .ternaryConditional condition thenBranch elseBranch⟩ => do
          let conditionPlan ← expressionTokenPlanAt? .logicalOr condition
          let thenPlan ← expressionTokenPlanAt? .conditional thenBranch
          let elsePlan ← expressionTokenPlanAt? .conditional elseBranch
          pure (.enclose span (.concat [
            conditionPlan,
            .plain (.symbol .question),
            thenPlan,
            .plain (.symbol .colon),
            elsePlan]))
      | _ => expressionTokenPlanAt? .logicalOr expression
  | .logicalOr =>
      match _expressionEq : expression with
      | ⟨span, .infix operator left right⟩ =>
          match operator.payload with
          | .logicalOr => do
              let leftPlan ← expressionTokenPlanAt? .logicalOr left
              let rightPlan ← expressionTokenPlanAt? .logicalAnd right
              pure (.enclose span (.concat [
                leftPlan, infixOperatorTokenPlan operator, rightPlan]))
          | _ => expressionTokenPlanAt? .logicalAnd expression
      | _ => expressionTokenPlanAt? .logicalAnd expression
  | .logicalAnd =>
      match _expressionEq : expression with
      | ⟨span, .infix operator left right⟩ =>
          match operator.payload with
          | .logicalAnd => do
              let leftPlan ← expressionTokenPlanAt? .logicalAnd left
              let rightPlan ← expressionTokenPlanAt? .equality right
              pure (.enclose span (.concat [
                leftPlan, infixOperatorTokenPlan operator, rightPlan]))
          | _ => expressionTokenPlanAt? .equality expression
      | _ => expressionTokenPlanAt? .equality expression
  | .equality =>
      match _expressionEq : expression with
      | ⟨span, .infix operator left right⟩ =>
          match operator.payload with
          | .equal | .notEqual => do
              let leftPlan ← expressionTokenPlanAt? .relational left
              let rightPlan ← expressionTokenPlanAt? .relational right
              pure (.enclose span (.concat [
                leftPlan, infixOperatorTokenPlan operator, rightPlan]))
          | _ => expressionTokenPlanAt? .relational expression
      | _ => expressionTokenPlanAt? .relational expression
  | .relational =>
      match _expressionEq : expression with
      | ⟨span, .infix operator left right⟩ =>
          match operator.payload with
          | .less | .greater | .lessEqual | .greaterEqual => do
              let leftPlan ← expressionTokenPlanAt? .bitOr left
              let rightPlan ← expressionTokenPlanAt? .bitOr right
              pure (.enclose span (.concat [
                leftPlan, infixOperatorTokenPlan operator, rightPlan]))
          | _ => expressionTokenPlanAt? .bitOr expression
      | _ => expressionTokenPlanAt? .bitOr expression
  | .bitOr =>
      match _expressionEq : expression with
      | ⟨span, .infix operator left right⟩ =>
          match operator.payload with
          | .bitOr => do
              let leftPlan ← expressionTokenPlanAt? .bitOr left
              let rightPlan ← expressionTokenPlanAt? .bitXor right
              pure (.enclose span (.concat [
                leftPlan, infixOperatorTokenPlan operator, rightPlan]))
          | _ => expressionTokenPlanAt? .bitXor expression
      | _ => expressionTokenPlanAt? .bitXor expression
  | .bitXor =>
      match _expressionEq : expression with
      | ⟨span, .infix operator left right⟩ =>
          match operator.payload with
          | .bitXor => do
              let leftPlan ← expressionTokenPlanAt? .bitXor left
              let rightPlan ← expressionTokenPlanAt? .bitAnd right
              pure (.enclose span (.concat [
                leftPlan, infixOperatorTokenPlan operator, rightPlan]))
          | _ => expressionTokenPlanAt? .bitAnd expression
      | _ => expressionTokenPlanAt? .bitAnd expression
  | .bitAnd =>
      match _expressionEq : expression with
      | ⟨span, .infix operator left right⟩ =>
          match operator.payload with
          | .bitAnd => do
              let leftPlan ← expressionTokenPlanAt? .bitAnd left
              let rightPlan ← expressionTokenPlanAt? .additive right
              pure (.enclose span (.concat [
                leftPlan, infixOperatorTokenPlan operator, rightPlan]))
          | _ => expressionTokenPlanAt? .additive expression
      | _ => expressionTokenPlanAt? .additive expression
  | .additive =>
      match _expressionEq : expression with
      | ⟨span, .infix operator left right⟩ =>
          match operator.payload with
          | .add | .subtract => do
              let leftPlan ← expressionTokenPlanAt? .additive left
              let rightPlan ← expressionTokenPlanAt? .multiplicative right
              pure (.enclose span (.concat [
                leftPlan, infixOperatorTokenPlan operator, rightPlan]))
          | _ => expressionTokenPlanAt? .multiplicative expression
      | _ => expressionTokenPlanAt? .multiplicative expression
  | .multiplicative =>
      match _expressionEq : expression with
      | ⟨span, .infix operator left right⟩ =>
          match operator.payload with
          | .multiply | .divide | .modulo => do
              let leftPlan ← expressionTokenPlanAt? .multiplicative left
              let rightPlan ← expressionTokenPlanAt? .prefix right
              pure (.enclose span (.concat [
                leftPlan, infixOperatorTokenPlan operator, rightPlan]))
          | _ => expressionTokenPlanAt? .prefix expression
      | _ => expressionTokenPlanAt? .prefix expression
  | .prefix =>
      match _expressionEq : expression with
      | ⟨span, .prefix operator operand⟩ => do
          let operandPlan ← expressionTokenPlanAt? .prefix operand
          pure (.enclose span (.append
            (prefixOperatorTokenPlan operator) operandPlan))
      | _ => expressionTokenPlanAt? .postfix expression
  | .postfix =>
      match _expressionEq : expression with
      | ⟨span, .call callee arguments⟩ =>
          match callee.payload with
          | .dotConstructor _ _ none => none
          | _ => do
              let calleePlan ← expressionTokenPlanAt? .postfix callee
              let argumentPlans ← expressionTokenPlans? arguments
              pure (.enclose span (.append calleePlan
                (.parens (.commaSeparated argumentPlans))))
      | ⟨span, .select receiver field⟩ => do
          let receiverPlan ← expressionTokenPlanAt? .postfix receiver
          pure (.enclose span (.concat [
            receiverPlan,
            .plain (.symbol .dot),
            identifierPlan field]))
      | ⟨span, .index receiver index⟩ => do
          let receiverPlan ← expressionTokenPlanAt? .postfix receiver
          let indexPlan ← expressionTokenPlanAt? .annotation index
          pure (.enclose span (.concat [
            receiverPlan,
            .plain (.symbol .leftBracket),
            indexPlan,
            .plain (.symbol .rightBracket)]))
      | _ => expressionTokenPlanAt? .atom expression
  | .atom =>
      match _expressionEq : expression with
      | ⟨span, .name name⟩ =>
          some (.enclose span (identifierPlan name))
      | ⟨span, .dotConstructor marker name none⟩ =>
          some (.enclose span (.concat [
            .exact (.symbol .dot) marker.span,
            identifierPlan name]))
      | ⟨span, .dotConstructor marker name (some arguments)⟩ => do
          let argumentPlans ← expressionTokenPlans? arguments
          pure (.enclose span (.concat [
            .exact (.symbol .dot) marker.span,
            identifierPlan name,
            .parens (.commaSeparated argumentPlans)]))
      | ⟨span, .proxy marker typeExpression⟩ => do
          let typePlan ← typeAtomPlan? typeExpression
          pure (.enclose span (.append
            (.exact (.symbol .at) marker.span) typePlan))
      | ⟨span, .literal literal⟩ =>
          some (.enclose span (literalTokenPlan literal))
      | ⟨span, .lambda parameters returnType body⟩ => do
          let parameterPlans ← parameterTokenPlans? parameters
          let returnPlan ←
            match returnType with
            | none => some .empty
            | some typeExpression => do
                let typePlan ← typeExprPlan? typeExpression
                pure (.append (.plain (.symbol .arrow)) typePlan)
          let bodyPlan ← bodyTokenPlan? .braced body
          pure (.enclose span (.concat [
            .plain (.hardKeyword .lamKw),
            .parens (.commaSeparated parameterPlans),
            returnPlan,
            bodyPlan]))
      | ⟨span, .tuple []⟩ =>
          some (.enclose span (.parens .empty))
      | ⟨_, .tuple [_]⟩ => none
      | ⟨span, .tuple (first :: second :: rest)⟩ => do
          let elementPlans ←
            expressionTokenPlans? (first :: second :: rest)
          pure (.enclose span (.parens (.commaSeparated elementPlans)))
      | ⟨span, .group inner⟩ => do
          let innerPlan ← expressionTokenPlanAt? .annotation inner
          pure (.enclose span (.parens innerPlan))
      | _ => none
termination_by expressionAtPlanMeasure level expression
decreasing_by solve_token_plan_termination

def expressionTokenPlans? :
    List Expression → Option (List TokenPlan)
  | [] => some []
  | head :: tail => do
      let headPlan ← expressionTokenPlanAt? .annotation head
      let tailPlans ← expressionTokenPlans? tail
      pure (headPlan :: tailPlans)
termination_by values => expressionListPlanMeasure values
decreasing_by solve_token_plan_termination

def nonemptyExpressionTokenPlans? :
    NonemptyList Expression → Option (List TokenPlan)
  | ⟨head, tail⟩ => do
      let headPlan ← expressionTokenPlanAt? .annotation head
      let tailPlans ← expressionTokenPlans? tail
      pure (headPlan :: tailPlans)
termination_by values => expressionNonemptyPlanMeasure values
decreasing_by solve_token_plan_termination

def patternTokenPlan? (pattern : Pattern) : Option TokenPlan :=
  match pattern with
  | ⟨span, .named name none⟩ =>
      some (.enclose span (qualifiedNamePlan name))
  | ⟨span, .named name (some arguments)⟩ => do
      let argumentPlans ← nonemptyPatternTokenPlans? arguments
      pure (.enclose span (.append (qualifiedNamePlan name)
        (.parens (.commaSeparated argumentPlans))))
  | ⟨span, .dotConstructor marker name none⟩ =>
      some (.enclose span (.concat [
        .exact (.symbol .dot) marker.span,
        identifierPlan name]))
  | ⟨span, .dotConstructor marker name (some arguments)⟩ => do
      let argumentPlans ← nonemptyPatternTokenPlans? arguments
      pure (.enclose span (.concat [
        .exact (.symbol .dot) marker.span,
        identifierPlan name,
        .parens (.commaSeparated argumentPlans)]))
  | ⟨span, .wildcard marker⟩ =>
      if marker.payload = .wildcard then
        some (.enclose span
          (.exact (.symbol .underscore) marker.span))
      else
        none
  | ⟨span, .literal literal⟩ =>
      some (.enclose span (literalTokenPlan literal))
  | ⟨span, .comptime marker expression⟩ =>
      if marker.payload = .comptimeModifier then do
        let expressionPlan ←
          expressionTokenPlanAt? .annotation expression
        some (.enclose span (.append
          (.exact (.identifier ContextualKeyword.comptimeKw.spelling)
            marker.span) expressionPlan))
      else
        none
  | ⟨span, .tuple []⟩ =>
      some (.enclose span (.parens .empty))
  | ⟨_, .tuple [_]⟩ => none
  | ⟨span, .tuple (first :: second :: rest)⟩ => do
      let elementPlans ← patternTokenPlans? (first :: second :: rest)
      pure (.enclose span (.parens (.commaSeparated elementPlans)))
  | ⟨span, .group inner⟩ => do
      let innerPlan ← patternTokenPlan? inner
      pure (.enclose span (.parens innerPlan))
termination_by patternPlanMeasure pattern
decreasing_by solve_token_plan_termination

def patternTokenPlans? : List Pattern → Option (List TokenPlan)
  | [] => some []
  | head :: tail => do
      let headPlan ← patternTokenPlan? head
      let tailPlans ← patternTokenPlans? tail
      pure (headPlan :: tailPlans)
termination_by values => patternListPlanMeasure values
decreasing_by solve_token_plan_termination

def nonemptyPatternTokenPlans? :
    NonemptyList Pattern → Option (List TokenPlan)
  | ⟨head, tail⟩ => do
      let headPlan ← patternTokenPlan? head
      let tailPlans ← patternTokenPlans? tail
      pure (headPlan :: tailPlans)
termination_by values => patternNonemptyPlanMeasure values
decreasing_by solve_token_plan_termination

def bodyTokenPlan?
    (context : BodyTokenContext) (body : Body) : Option TokenPlan :=
  match context, body with
  | .braced, ⟨_, ⟨.matchArm _, _⟩⟩ => none
  | .matchArm, ⟨_, ⟨.braced .., _⟩⟩ => none
  | .braced, body@⟨_, ⟨.braced _ _, statements⟩⟩ => do
      let statementPlans ← statementTokenPlans? statements
      bracedBodyPlanWith? statementPlans body
  | .matchArm, body@⟨_, ⟨.matchArm _, statements⟩⟩ => do
      let statementPlans ← statementTokenPlans? statements
      armBodyPlanWith? statementPlans body
termination_by bodyPlanMeasure body
decreasing_by solve_token_plan_termination

/-- `allowTerminal` is true exactly for the final element of one body. -/
def statementTokenPlan?
    (allowTerminal : Bool) (statement : Statement) : Option TokenPlan :=
  match statement with
  | ⟨span, .assignment operator left right⟩ => do
      let leftPlan ← expressionTokenPlanAt? .annotation left
      let rightPlan ← expressionTokenPlanAt? .annotation right
      pure (.enclose span (.concat [
        leftPlan,
        assignmentOperatorTokenPlan operator,
        rightPlan,
        .plain (.symbol .semicolon)]))
  | ⟨span, .letBinding binding⟩ => do
      let bindingPlan ← letBindingTokenPlan? binding
      pure (.enclose span (.append bindingPlan
        (.plain (.symbol .semicolon))))
  | ⟨span, .block body⟩ => do
      let bodyPlan ← bodyTokenPlan? .braced body
      pure (.enclose span bodyPlan)
  | ⟨span, .expression expression (some terminator)⟩ => do
      let expressionPlan ← expressionTokenPlanAt? .annotation expression
      pure (.enclose span (.append expressionPlan
        (.exact (.symbol .semicolon) terminator)))
  | ⟨span, .expression expression none⟩ =>
      if allowTerminal then do
        let expressionPlan ← expressionTokenPlanAt? .annotation expression
        pure (.enclose span expressionPlan)
      else
        none
  | ⟨span, .return value terminator⟩ => do
      let valuePlan ←
        match value with
        | none => some .empty
        | some expression => expressionTokenPlanAt? .annotation expression
      pure (.enclose span (.concat [
        .plain (.hardKeyword .returnKw),
        valuePlan,
        .exact (.symbol .semicolon) terminator]))
  | ⟨span, .match scrutinees arms terminator⟩ => do
      let scrutineePlans ← nonemptyExpressionTokenPlans? scrutinees
      let armPlans ← nonemptyMatchArmTokenPlans? arms
      let terminatorPlan :=
        match terminator with
        | none => TokenPlan.empty
        | some semicolon => .exact (.symbol .semicolon) semicolon
      pure (.enclose span (.concat [
        .plain (.hardKeyword .matchKw),
        .commaSeparated scrutineePlans,
        .plain (.symbol .leftBrace),
        .concat armPlans,
        .plain (.symbol .rightBrace),
        terminatorPlan]))
  | ⟨span, .assembly slice⟩ =>
      some (.enclose span (.concat [
        .plain (.hardKeyword .assemblyKw),
        .exact (.assemblyBlock slice) slice.span]))
  | ⟨span, .ifThenElse condition thenBody elseBody⟩ => do
      let conditionPlan ← expressionTokenPlanAt? .annotation condition
      let thenPlan ← bodyTokenPlan? .braced thenBody
      let elsePlan ←
        match elseBody with
        | none => some .empty
        | some body => do
            let bodyPlan ← bodyTokenPlan? .braced body
            pure (.append (.plain (.hardKeyword .elseKw)) bodyPlan)
      pure (.enclose span (.concat [
        .plain (.hardKeyword .ifKw),
        .parens conditionPlan,
        thenPlan,
        elsePlan]))
  | ⟨span, .forLoop initializers condition post body⟩ => do
      let initializerPlans ← forInitTokenPlans? initializers
      let conditionPlan ← expressionTokenPlanAt? .annotation condition
      let postPlans ← forPostTokenPlans? post
      let bodyPlan ← bodyTokenPlan? .braced body
      pure (.enclose span (.concat [
        .plain (.hardKeyword .forKw),
        .plain (.symbol .leftParen),
        .commaSeparated initializerPlans,
        .plain (.symbol .semicolon),
        conditionPlan,
        .plain (.symbol .semicolon),
        .commaSeparated postPlans,
        .plain (.symbol .rightParen),
        bodyPlan]))
  | ⟨span, .break terminator⟩ =>
      some (.enclose span (.concat [
        .plain (.hardKeyword .breakKw),
        .exact (.symbol .semicolon) terminator]))
  | ⟨span, .continue terminator⟩ =>
      some (.enclose span (.concat [
        .plain (.hardKeyword .continueKw),
        .exact (.symbol .semicolon) terminator]))
termination_by statementPlanMeasure statement
decreasing_by solve_token_plan_termination

def statementTokenPlans? :
    List Statement → Option (List TokenPlan)
  | [] => some []
  | [last] => do
      let lastPlan ← statementTokenPlan? true last
      pure [lastPlan]
  | head :: second :: rest => do
      let headPlan ← statementTokenPlan? false head
      let tailPlans ← statementTokenPlans? (second :: rest)
      pure (headPlan :: tailPlans)
termination_by values => statementListPlanMeasure values
decreasing_by solve_token_plan_termination

/-- The optional `comptime` before a let-binding type has parser priority over
a `comptime` type expression. The latter shape is therefore rejected when the
dedicated marker field is absent. -/
def letBindingTokenPlan? (binding : LetBinding) : Option TokenPlan :=
  match binding with
  | ⟨span, ⟨comptime, name, typeExpression, initializer⟩⟩ => do
      let typePlan ←
        match comptime, typeExpression with
        | none, none => some .empty
        | some _, none => none
        | none, some typeExpression =>
            match typeExpression.payload with
            | .comptime .. => none
            | _ => do
                let plan ← typeExprPlan? typeExpression
                pure (.append (.plain (.symbol .colon)) plan)
        | some marker, some typeExpression =>
            if marker.payload = .comptimeModifier then do
              let plan ← typeExprPlan? typeExpression
              pure (.concat [
                .plain (.symbol .colon),
                .exact (.identifier ContextualKeyword.comptimeKw.spelling)
                  marker.span,
                plan])
            else
              none
      let initializerPlan ←
        match initializer with
        | none => some .empty
        | some expression => do
            let plan ← expressionTokenPlanAt? .annotation expression
            pure (.append (.plain (.symbol .equal)) plan)
      pure (.enclose span (.concat [
        .plain (.hardKeyword .letKw),
        identifierPlan name,
        typePlan,
        initializerPlan]))
termination_by letBindingPlanMeasure binding
decreasing_by solve_token_plan_termination

def forInitTokenPlan? (item : ForInitItem) : Option TokenPlan :=
  match item with
  | ⟨span, .letBinding binding⟩ => do
      let bindingPlan ← letBindingTokenPlan? binding
      pure (.enclose span bindingPlan)
  | ⟨span, .assignment operator left right⟩ => do
      let leftPlan ← expressionTokenPlanAt? .annotation left
      let rightPlan ← expressionTokenPlanAt? .annotation right
      pure (.enclose span (.concat [
        leftPlan,
        assignmentOperatorTokenPlan operator,
        rightPlan]))
  | ⟨span, .expression expression⟩ => do
      let expressionPlan ← expressionTokenPlanAt? .annotation expression
      pure (.enclose span expressionPlan)
termination_by forInitPlanMeasure item
decreasing_by solve_token_plan_termination

def forInitTokenPlans? :
    List ForInitItem → Option (List TokenPlan)
  | [] => some []
  | head :: tail => do
      let headPlan ← forInitTokenPlan? head
      let tailPlans ← forInitTokenPlans? tail
      pure (headPlan :: tailPlans)
termination_by values => forInitListPlanMeasure values
decreasing_by solve_token_plan_termination

def forPostTokenPlan? (item : ForPostItem) : Option TokenPlan :=
  match item with
  | ⟨span, .assignment operator left right⟩ => do
      let leftPlan ← expressionTokenPlanAt? .annotation left
      let rightPlan ← expressionTokenPlanAt? .annotation right
      pure (.enclose span (.concat [
        leftPlan,
        assignmentOperatorTokenPlan operator,
        rightPlan]))
  | ⟨span, .expression expression⟩ => do
      let expressionPlan ← expressionTokenPlanAt? .annotation expression
      pure (.enclose span expressionPlan)
termination_by forPostPlanMeasure item
decreasing_by solve_token_plan_termination

def forPostTokenPlans? :
    List ForPostItem → Option (List TokenPlan)
  | [] => some []
  | head :: tail => do
      let headPlan ← forPostTokenPlan? head
      let tailPlans ← forPostTokenPlans? tail
      pure (headPlan :: tailPlans)
termination_by values => forPostListPlanMeasure values
decreasing_by solve_token_plan_termination

def matchArmTokenPlan? (arm : MatchArm) : Option TokenPlan :=
  match arm with
  | ⟨_, ⟨_, ⟨_, ⟨.braced .., _⟩⟩⟩⟩ => none
  | ⟨span, ⟨patterns, body@⟨_, ⟨.matchArm _, _⟩⟩⟩⟩ => do
      let patternPlans ← nonemptyPatternTokenPlans? patterns
      let arrowPlan ← matchArmArrowPlan body
      let bodyPlan ← bodyTokenPlan? .matchArm body
      pure (.enclose span (.concat [
        .plain (.symbol .pipe),
        .commaSeparated patternPlans,
        arrowPlan,
        bodyPlan]))
termination_by matchArmPlanMeasure arm
decreasing_by solve_token_plan_termination

def matchArmTokenPlans? :
    List MatchArm → Option (List TokenPlan)
  | [] => some []
  | head :: tail => do
      let headPlan ← matchArmTokenPlan? head
      let tailPlans ← matchArmTokenPlans? tail
      pure (headPlan :: tailPlans)
termination_by values => matchArmListPlanMeasure values
decreasing_by solve_token_plan_termination

def nonemptyMatchArmTokenPlans? :
    NonemptyList MatchArm → Option (List TokenPlan)
  | ⟨head, tail⟩ => do
      let headPlan ← matchArmTokenPlan? head
      let tailPlans ← matchArmTokenPlans? tail
      pure (headPlan :: tailPlans)
termination_by values => matchArmNonemptyPlanMeasure values
decreasing_by solve_token_plan_termination

end


/-- Public full-expression entry. -/
def expressionTokenPlan? : Expression → Option TokenPlan :=
  expressionTokenPlanAt? .annotation

def annotationExpressionTokenPlan? :=
  expressionTokenPlanAt? .annotation
def conditionalExpressionTokenPlan? :=
  expressionTokenPlanAt? .conditional
def logicalOrExpressionTokenPlan? :=
  expressionTokenPlanAt? .logicalOr
def logicalAndExpressionTokenPlan? :=
  expressionTokenPlanAt? .logicalAnd
def equalityExpressionTokenPlan? :=
  expressionTokenPlanAt? .equality
def relationalExpressionTokenPlan? :=
  expressionTokenPlanAt? .relational
def bitOrExpressionTokenPlan? :=
  expressionTokenPlanAt? .bitOr
def bitXorExpressionTokenPlan? :=
  expressionTokenPlanAt? .bitXor
def bitAndExpressionTokenPlan? :=
  expressionTokenPlanAt? .bitAnd
def additiveExpressionTokenPlan? :=
  expressionTokenPlanAt? .additive
def multiplicativeExpressionTokenPlan? :=
  expressionTokenPlanAt? .multiplicative
def prefixExpressionTokenPlan? :=
  expressionTokenPlanAt? .prefix
def postfixExpressionTokenPlan? :=
  expressionTokenPlanAt? .postfix
def atomExpressionTokenPlan? :=
  expressionTokenPlanAt? .atom

@[simp] theorem atomExpressionTokenPlan_name
    (span : SourceSpan) (name : IdentifierOccurrence) :
    atomExpressionTokenPlan?
        (show Expression from ⟨span, .name name⟩) =
      some (.enclose span (identifierPlan name)) := by
  simp [atomExpressionTokenPlan?, expressionTokenPlanAt?]

@[simp] theorem atomExpressionTokenPlan_tuple_singleton
    (span : SourceSpan) (element : Expression) :
    atomExpressionTokenPlan?
        (show Expression from ⟨span, .tuple [element]⟩) = none := by
  simp [atomExpressionTokenPlan?, expressionTokenPlanAt?]

@[simp] theorem expressionTokenPlan_tuple_singleton
    (span : SourceSpan) (element : Expression) :
    expressionTokenPlan?
        (show Expression from ⟨span, .tuple [element]⟩) = none := by
  simp [expressionTokenPlan?, expressionTokenPlanAt?]

@[simp] theorem patternTokenPlan_tuple_singleton
    (span : SourceSpan) (element : Pattern) :
    patternTokenPlan?
        (show Pattern from ⟨span, .tuple [element]⟩) = none := by
  simp [patternTokenPlan?]

@[simp] theorem postfixExpressionTokenPlan_call_dotConstructor_none
    (span calleeSpan markerSpan : SourceSpan)
    (name : IdentifierOccurrence) (arguments : List Expression) :
    postfixExpressionTokenPlan?
        (show Expression from ⟨span, .call
          ⟨calleeSpan, .dotConstructor ⟨markerSpan, ()⟩ name none⟩
          arguments⟩) = none := by
  simp [postfixExpressionTokenPlan?, expressionTokenPlanAt?]

end Solcore.Surface.Multi
