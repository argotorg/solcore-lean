import Solcore.Surface.Multi.RuleLocationProperties

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace
open Grammar

mutual

/-- A source-rule value occurring anywhere inside one checked EBNF value. -/
inductive EbnfValue.ContainsRuleValue
    (file : WorkspaceFile) (tokens : List Token) :
    {expression : EbnfExpr} -> EbnfValue file tokens expression ->
      (rule : GrammarRuleId) -> RuleValue rule -> Prop where
  | rule (rule : GrammarRuleId) (value : RuleValue rule) :
      EbnfValue.ContainsRuleValue file tokens
        (EbnfValue.ruleAtom rule value) rule value
  | transport
      {left right : EbnfExpr} (shape : left = right)
      {input : EbnfValue file tokens left}
      {rule : GrammarRuleId} {value : RuleValue rule}
      (inside : EbnfValue.ContainsRuleValue file tokens input rule value) :
      EbnfValue.ContainsRuleValue file tokens
        (EbnfValue.transport shape input) rule value
  | sequence
      {children : List EbnfExpr}
      {values : EbnfValues file tokens children}
      {rule : GrammarRuleId} {value : RuleValue rule}
      (inside : EbnfValues.ContainsRuleValue file tokens values rule value) :
      EbnfValue.ContainsRuleValue file tokens
        (EbnfValue.sequence children values) rule value
  | group
      {child : EbnfExpr} {childValue : EbnfValue file tokens child}
      {rule : GrammarRuleId} {value : RuleValue rule}
      (inside : EbnfValue.ContainsRuleValue file tokens childValue rule value) :
      EbnfValue.ContainsRuleValue file tokens
        (EbnfValue.group child childValue) rule value
  | choice
      {branches : List EbnfExpr} (branch : Fin branches.length)
      {branchValue : EbnfValue file tokens (branches.get branch)}
      {rule : GrammarRuleId} {value : RuleValue rule}
      (inside : EbnfValue.ContainsRuleValue file tokens branchValue rule value) :
      EbnfValue.ContainsRuleValue file tokens
        (EbnfValue.choice branches ⟨branch, branchValue⟩) rule value
  | optional
      {child : EbnfExpr} {childValue : EbnfValue file tokens child}
      {rule : GrammarRuleId} {value : RuleValue rule}
      (inside : EbnfValue.ContainsRuleValue file tokens childValue rule value) :
      EbnfValue.ContainsRuleValue file tokens
        (EbnfValue.optional child (some childValue)) rule value
  | star
      {child : EbnfExpr} {values : List (EbnfValue file tokens child)}
      {childValue : EbnfValue file tokens child}
      {rule : GrammarRuleId} {value : RuleValue rule}
      (member : childValue ∈ values)
      (inside : EbnfValue.ContainsRuleValue file tokens childValue rule value) :
      EbnfValue.ContainsRuleValue file tokens
        (EbnfValue.star child values) rule value
  | plusHead
      {child : EbnfExpr} {head : EbnfValue file tokens child}
      {tail : List (EbnfValue file tokens child)}
      {rule : GrammarRuleId} {value : RuleValue rule}
      (inside : EbnfValue.ContainsRuleValue file tokens head rule value) :
      EbnfValue.ContainsRuleValue file tokens
        (EbnfValue.plus child ⟨head, tail⟩) rule value
  | plusTail
      {child : EbnfExpr} {head childValue : EbnfValue file tokens child}
      {tail : List (EbnfValue file tokens child)}
      {rule : GrammarRuleId} {value : RuleValue rule}
      (member : childValue ∈ tail)
      (inside : EbnfValue.ContainsRuleValue file tokens childValue rule value) :
      EbnfValue.ContainsRuleValue file tokens
        (EbnfValue.plus child ⟨head, tail⟩) rule value
  | list0
      {child : EbnfExpr} {values : List (EbnfValue file tokens child)}
      {childValue : EbnfValue file tokens child}
      {rule : GrammarRuleId} {value : RuleValue rule}
      (member : childValue ∈ values)
      (inside : EbnfValue.ContainsRuleValue file tokens childValue rule value) :
      EbnfValue.ContainsRuleValue file tokens
        (EbnfValue.list0 child values) rule value
  | list1Head
      {child : EbnfExpr} {head : EbnfValue file tokens child}
      {tail : List (EbnfValue file tokens child)}
      {rule : GrammarRuleId} {value : RuleValue rule}
      (inside : EbnfValue.ContainsRuleValue file tokens head rule value) :
      EbnfValue.ContainsRuleValue file tokens
        (EbnfValue.list1 child ⟨head, tail⟩) rule value
  | list1Tail
      {child : EbnfExpr} {head childValue : EbnfValue file tokens child}
      {tail : List (EbnfValue file tokens child)}
      {rule : GrammarRuleId} {value : RuleValue rule}
      (member : childValue ∈ tail)
      (inside : EbnfValue.ContainsRuleValue file tokens childValue rule value) :
      EbnfValue.ContainsRuleValue file tokens
        (EbnfValue.list1 child ⟨head, tail⟩) rule value

/-- A source-rule value occurring in one checked heterogeneous EBNF tuple. -/
inductive EbnfValues.ContainsRuleValue
    (file : WorkspaceFile) (tokens : List Token) :
    {expressions : List EbnfExpr} -> EbnfValues file tokens expressions ->
      (rule : GrammarRuleId) -> RuleValue rule -> Prop where
  | head
      {child : EbnfExpr} {rest : List EbnfExpr}
      {childValue : EbnfValue file tokens child}
      {restValues : EbnfValues file tokens rest}
      {rule : GrammarRuleId} {value : RuleValue rule}
      (inside : EbnfValue.ContainsRuleValue file tokens childValue rule value) :
      EbnfValues.ContainsRuleValue file tokens
        (EbnfValues.cons child rest childValue restValues) rule value
  | tail
      {child : EbnfExpr} {rest : List EbnfExpr}
      {childValue : EbnfValue file tokens child}
      {restValues : EbnfValues file tokens rest}
      {rule : GrammarRuleId} {value : RuleValue rule}
      (inside : EbnfValues.ContainsRuleValue file tokens restValues rule value) :
      EbnfValues.ContainsRuleValue file tokens
        (EbnfValues.cons child rest childValue restValues) rule value

end

/-- The output location fragment is exactly that of a source-rule child
retained by the reduction input. -/
def RuleReduction.PassesThroughLocation
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    (_reduces : RuleReduction file tokens rule origin finish input output) : Prop :=
  ∃ childRule childValue,
    EbnfValue.ContainsRuleValue file tokens input childRule childValue ∧
      RuleLocationView.ofRuleValue rule output =
        RuleLocationView.ofRuleValue childRule childValue

/-- The reductions whose semantic action returns one source-rule child's
location-bearing value without adding a new location layer. -/
inductive RuleReduction.SemanticPassThrough
    {file : WorkspaceFile} {tokens : List Token} :
    {rule : GrammarRuleId} -> {origin finish : Boundary tokens} ->
      {input : EbnfValue file tokens (m2cV1.rhs rule)} ->
      {output : RuleValue rule} ->
      RuleReduction file tokens rule origin finish input output -> Prop where
  | instanceMethod (origin finish : Boundary tokens)
      (value : FunctionDecl) :
      RuleReduction.SemanticPassThrough
        (RuleReduction.instanceMethod origin finish value)
  | typeAtomOnly (origin finish : Boundary tokens) (value : TypeExpr) :
      RuleReduction.SemanticPassThrough
        (RuleReduction.typeAtomOnly origin finish value)
  | statementLet (origin finish : Boundary tokens) (value : Statement) :
      RuleReduction.SemanticPassThrough
        (RuleReduction.statementLet origin finish value)
  | statementReturn (origin finish : Boundary tokens) (value : Statement) :
      RuleReduction.SemanticPassThrough
        (RuleReduction.statementReturn origin finish value)
  | statementMatch (origin finish : Boundary tokens) (value : Statement) :
      RuleReduction.SemanticPassThrough
        (RuleReduction.statementMatch origin finish value)
  | statementIf (origin finish : Boundary tokens) (value : Statement) :
      RuleReduction.SemanticPassThrough
        (RuleReduction.statementIf origin finish value)
  | statementFor (origin finish : Boundary tokens) (value : Statement) :
      RuleReduction.SemanticPassThrough
        (RuleReduction.statementFor origin finish value)
  | statementAssembly (origin finish : Boundary tokens) (value : Statement) :
      RuleReduction.SemanticPassThrough
        (RuleReduction.statementAssembly origin finish value)
  | statementBlock (origin finish : Boundary tokens) (value : Statement) :
      RuleReduction.SemanticPassThrough
        (RuleReduction.statementBlock origin finish value)
  | statementBreak (origin finish : Boundary tokens) (value : Statement) :
      RuleReduction.SemanticPassThrough
        (RuleReduction.statementBreak origin finish value)
  | statementContinue (origin finish : Boundary tokens) (value : Statement) :
      RuleReduction.SemanticPassThrough
        (RuleReduction.statementContinue origin finish value)
  | statementAssignment (origin finish : Boundary tokens) (value : Statement) :
      RuleReduction.SemanticPassThrough
        (RuleReduction.statementAssignment origin finish value)
  | statementExpression (origin finish : Boundary tokens) (value : Statement) :
      RuleReduction.SemanticPassThrough
        (RuleReduction.statementExpression origin finish value)
  | armStatement (origin finish : Boundary tokens) (value : Statement) :
      RuleReduction.SemanticPassThrough
        (RuleReduction.armStatement origin finish value)
  | terminalExpression (origin finish : Boundary tokens)
      (value : Expression) :
      RuleReduction.SemanticPassThrough
        (RuleReduction.terminalExpression origin finish value)
  | expression (origin finish : Boundary tokens) (value : Expression) :
      RuleReduction.SemanticPassThrough
        (RuleReduction.expression origin finish value)
  | annotationNone (origin finish : Boundary tokens) (value : Expression) :
      RuleReduction.SemanticPassThrough
        (RuleReduction.annotationNone origin finish value)
  | conditionalLogical (origin finish : Boundary tokens)
      (value : Expression) :
      RuleReduction.SemanticPassThrough
        (RuleReduction.conditionalLogical origin finish value)
  | equalityNone (origin finish : Boundary tokens) (value : Expression) :
      RuleReduction.SemanticPassThrough
        (RuleReduction.equalityNone origin finish value)
  | relationalNone (origin finish : Boundary tokens) (value : Expression) :
      RuleReduction.SemanticPassThrough
        (RuleReduction.relationalNone origin finish value)
  | prefixPostfix (origin finish : Boundary tokens) (value : Expression) :
      RuleReduction.SemanticPassThrough
        (RuleReduction.prefixPostfix origin finish value)
  | atomLambda (origin finish : Boundary tokens) (value : Expression) :
      RuleReduction.SemanticPassThrough
        (RuleReduction.atomLambda origin finish value)

namespace RuleReduction.SemanticPassThrough

/-- Every semantic pass-through action exposes the same complete location
fragment as the exact child value encoded by its checked EBNF input. -/
theorem location
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    {reduces : RuleReduction file tokens rule origin finish input output}
    (passThrough : RuleReduction.SemanticPassThrough reduces) :
    RuleReduction.PassesThroughLocation reduces := by
  cases passThrough with
  | instanceMethod origin finish value =>
      refine ⟨.functionDecl, value, ?_, rfl⟩
      exact EbnfValue.ContainsRuleValue.transport (by rfl)
        (EbnfValue.ContainsRuleValue.rule .functionDecl value)
  | typeAtomOnly origin finish value =>
      refine ⟨.typeAtom, value, ?_, rfl⟩
      exact EbnfValue.ContainsRuleValue.transport (by rfl)
        (EbnfValue.ContainsRuleValue.choice ⟨1, by decide⟩
          (EbnfValue.ContainsRuleValue.sequence
            (EbnfValues.ContainsRuleValue.head
              (EbnfValue.ContainsRuleValue.rule .typeAtom value))))
  | statementLet origin finish value =>
      refine ⟨.letStatement, value, ?_, rfl⟩
      exact EbnfValue.ContainsRuleValue.choice ⟨0, by decide⟩
        (EbnfValue.ContainsRuleValue.rule .letStatement value)
  | statementReturn origin finish value =>
      refine ⟨.returnStatement, value, ?_, rfl⟩
      exact EbnfValue.ContainsRuleValue.choice ⟨1, by decide⟩
        (EbnfValue.ContainsRuleValue.rule .returnStatement value)
  | statementMatch origin finish value =>
      refine ⟨.matchStatement, value, ?_, rfl⟩
      exact EbnfValue.ContainsRuleValue.choice ⟨2, by decide⟩
        (EbnfValue.ContainsRuleValue.rule .matchStatement value)
  | statementIf origin finish value =>
      refine ⟨.ifStatement, value, ?_, rfl⟩
      exact EbnfValue.ContainsRuleValue.choice ⟨3, by decide⟩
        (EbnfValue.ContainsRuleValue.rule .ifStatement value)
  | statementFor origin finish value =>
      refine ⟨.forStatement, value, ?_, rfl⟩
      exact EbnfValue.ContainsRuleValue.choice ⟨4, by decide⟩
        (EbnfValue.ContainsRuleValue.rule .forStatement value)
  | statementAssembly origin finish value =>
      refine ⟨.assemblyStatement, value, ?_, rfl⟩
      exact EbnfValue.ContainsRuleValue.choice ⟨5, by decide⟩
        (EbnfValue.ContainsRuleValue.rule .assemblyStatement value)
  | statementBlock origin finish value =>
      refine ⟨.blockStatement, value, ?_, rfl⟩
      exact EbnfValue.ContainsRuleValue.choice ⟨6, by decide⟩
        (EbnfValue.ContainsRuleValue.rule .blockStatement value)
  | statementBreak origin finish value =>
      refine ⟨.breakStatement, value, ?_, rfl⟩
      exact EbnfValue.ContainsRuleValue.choice ⟨7, by decide⟩
        (EbnfValue.ContainsRuleValue.rule .breakStatement value)
  | statementContinue origin finish value =>
      refine ⟨.continueStatement, value, ?_, rfl⟩
      exact EbnfValue.ContainsRuleValue.choice ⟨8, by decide⟩
        (EbnfValue.ContainsRuleValue.rule .continueStatement value)
  | statementAssignment origin finish value =>
      refine ⟨.assignmentStatement, value, ?_, rfl⟩
      exact EbnfValue.ContainsRuleValue.choice ⟨9, by decide⟩
        (EbnfValue.ContainsRuleValue.rule .assignmentStatement value)
  | statementExpression origin finish value =>
      refine ⟨.expressionStatement, value, ?_, rfl⟩
      exact EbnfValue.ContainsRuleValue.choice ⟨10, by decide⟩
        (EbnfValue.ContainsRuleValue.rule .expressionStatement value)
  | armStatement origin finish value =>
      refine ⟨.statement, value, ?_, rfl⟩
      exact EbnfValue.ContainsRuleValue.rule .statement value
  | terminalExpression origin finish value =>
      refine ⟨.expression, value, ?_, rfl⟩
      exact EbnfValue.ContainsRuleValue.rule .expression value
  | expression origin finish value =>
      refine ⟨.annotation, value, ?_, rfl⟩
      exact EbnfValue.ContainsRuleValue.rule .annotation value
  | annotationNone origin finish value =>
      refine ⟨.conditional, value, ?_, rfl⟩
      exact EbnfValue.ContainsRuleValue.sequence
        (EbnfValues.ContainsRuleValue.head
          (EbnfValue.ContainsRuleValue.rule .conditional value))
  | conditionalLogical origin finish value =>
      refine ⟨.logicalOr, value, ?_, rfl⟩
      exact EbnfValue.ContainsRuleValue.choice ⟨1, by decide⟩
        (EbnfValue.ContainsRuleValue.sequence
          (EbnfValues.ContainsRuleValue.head
            (EbnfValue.ContainsRuleValue.rule .logicalOr value)))
  | equalityNone origin finish value =>
      refine ⟨.relational, value, ?_, rfl⟩
      exact EbnfValue.ContainsRuleValue.sequence
        (EbnfValues.ContainsRuleValue.head
          (EbnfValue.ContainsRuleValue.rule .relational value))
  | relationalNone origin finish value =>
      refine ⟨.bitOr, value, ?_, rfl⟩
      exact EbnfValue.ContainsRuleValue.sequence
        (EbnfValues.ContainsRuleValue.head
          (EbnfValue.ContainsRuleValue.rule .bitOr value))
  | prefixPostfix origin finish value =>
      refine ⟨.postfix, value, ?_, rfl⟩
      exact EbnfValue.ContainsRuleValue.choice ⟨1, by decide⟩
        (EbnfValue.ContainsRuleValue.rule .postfix value)
  | atomLambda origin finish value =>
      refine ⟨.lambda, value, ?_, rfl⟩
      exact EbnfValue.ContainsRuleValue.choice ⟨4, by decide⟩
        (EbnfValue.ContainsRuleValue.rule .lambda value)

end RuleReduction.SemanticPassThrough

end Solcore.Surface.Multi
