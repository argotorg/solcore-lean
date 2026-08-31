import Solcore.Syntax.StatementValidity

/-! Canonical recursive source-validity for Core terms. -/

set_option autoImplicit false

namespace Solcore.Syntax

namespace Expr.ValidFor

/-- Expression validity is monotone in its statement contract. -/
theorem mono {old new : SourceFile → Statement → Prop}
    (lift : ∀ {file statement}, old file statement → new file statement)
    {file : SourceFile} {expression : Expr}
    (valid : Expr.ValidFor old file expression) :
    Expr.ValidFor new file expression := by
  induction valid with
  | literal spanValid literalValid => exact .literal spanValid literalValid
  | identifier spanValid nameValid => exact .identifier spanValid nameValid
  | dotConstructor spanValid dotValid nameValid argumentsSpanValid
      argumentsValid argumentsInduction =>
      exact .dotConstructor spanValid dotValid nameValid argumentsSpanValid
        argumentsInduction
  | proxy spanValid markerValid typeValid =>
      exact .proxy spanValid markerValid typeValid
  | lambda spanValid keywordValid parametersSpanValid parametersValid
      returnTypeValid bodyValid =>
      exact .lambda spanValid keywordValid parametersSpanValid parametersValid
        returnTypeValid ⟨bodyValid.1, fun statement member =>
          lift (bodyValid.2 statement member)⟩
  | unary spanValid operatorValid _ operandInduction =>
      exact .unary spanValid operatorValid operandInduction
  | binary spanValid _ operatorValid _ leftInduction rightInduction =>
      exact .binary spanValid leftInduction operatorValid rightInduction
  | index spanValid _ bracketsValid _ baseInduction indexInduction =>
      exact .index spanValid baseInduction bracketsValid indexInduction
  | call spanValid _ argumentsSpanValid _ calleeInduction
      argumentsInduction =>
      exact .call spanValid calleeInduction argumentsSpanValid
        argumentsInduction
  | field spanValid _ dotValid nameValid baseInduction =>
      exact .field spanValid baseInduction dotValid nameValid
  | conditional spanValid _ questionValid _ colonValid _ conditionInduction
      thenInduction elseInduction =>
      exact .conditional spanValid conditionInduction questionValid
        thenInduction colonValid elseInduction
  | group spanValid _ innerInduction =>
      exact .group spanValid innerInduction
  | tuple spanValid elementsSpanValid _ elementsInduction =>
      exact .tuple spanValid elementsSpanValid elementsInduction
  | array spanValid elementsSpanValid _ elementsInduction =>
      exact .array spanValid elementsSpanValid elementsInduction
  | error spanValid => exact .error spanValid

end Expr.ValidFor

namespace Pattern.ValidFor

/-- Pattern validity is monotone in its embedded-expression contract. -/
theorem mono {old new : SourceFile → Expr → Prop}
    (lift : ∀ {file expression}, old file expression → new file expression)
    {file : SourceFile} {pattern : Pattern}
    (valid : Pattern.ValidFor old file pattern) :
    Pattern.ValidFor new file pattern := by
  induction valid with
  | wildcard spanValid markerValid => exact .wildcard spanValid markerValid
  | literal spanValid literalValid => exact .literal spanValid literalValid
  | binder spanValid nameValid => exact .binder spanValid nameValid
  | constructor spanValid leadingDotValid qualifiersValid nameValid
      argumentsSpanValid _ argumentsInduction =>
      exact .constructor spanValid leadingDotValid qualifiersValid nameValid
        argumentsSpanValid argumentsInduction
  | comptime spanValid keywordValid expressionValid =>
      exact .comptime spanValid keywordValid (lift expressionValid)
  | group spanValid _ innerInduction => exact .group spanValid innerInduction
  | tuple spanValid elementsSpanValid _ elementsInduction =>
      exact .tuple spanValid elementsSpanValid elementsInduction
  | error spanValid => exact .error spanValid

end Pattern.ValidFor

namespace ForItem.ValidFor

/-- `for`-item validity is monotone in its expression contract. -/
theorem mono {old new : SourceFile → Expr → Prop}
    (lift : ∀ {file expression}, old file expression → new file expression)
    {file : SourceFile} {item : ForItem}
    (valid : ForItem.ValidFor old file item) : ForItem.ValidFor new file item := by
  cases valid with
  | letDecl spanValid nameValid typeValid initializerValid =>
      exact .letDecl spanValid nameValid typeValid fun expression member =>
        lift (initializerValid expression member)
  | expression spanValid expressionValid =>
      exact .expression spanValid (lift expressionValid)
  | assignValue spanValid targetValid operatorValid valueValid =>
      exact .assignValue spanValid (lift targetValid) operatorValid
        (lift valueValid)
  | assignBitNot spanValid targetValid operatorValid =>
      exact .assignBitNot spanValid (lift targetValid) operatorValid

end ForItem.ValidFor

/-- Statement validity is monotone in all three embedded syntax contracts. -/
theorem Statement.ValidFor.mono {oldExpr newExpr : SourceFile → Expr → Prop}
    {oldPattern newPattern : SourceFile → Pattern → Prop}
    {oldYul newYul : SourceFile → YulStmt → Prop}
    (liftExpr : ∀ {file expression}, oldExpr file expression →
      newExpr file expression)
    (liftPattern : ∀ {file pattern}, oldPattern file pattern →
      newPattern file pattern)
    (liftYul : ∀ {file statement}, oldYul file statement →
      newYul file statement)
    {file : SourceFile} {statement : Statement}
    (valid : Statement.ValidFor oldExpr oldPattern oldYul file statement) :
    Statement.ValidFor newExpr newPattern newYul file statement := by
  exact Statement.ValidFor.rec
    (motive_1 := fun statement _ =>
      Statement.ValidFor newExpr newPattern newYul file statement)
    (motive_2 := fun matchCase _ =>
      MatchCase.ValidFor newExpr newPattern newYul file matchCase)
    (motive_3 := fun arms _ =>
      MatchArms.ValidFor newExpr newPattern newYul file arms)
    (fun spanValid nameValid typeValid initializerValid =>
      .letDecl spanValid nameValid typeValid fun expression member =>
        liftExpr (initializerValid expression member))
    (fun spanValid valueValid =>
      .returnStmt spanValid fun expression member =>
        liftExpr (valueValid expression member))
    (fun spanValid expressionValid =>
      .expression spanValid (liftExpr expressionValid))
    (fun spanValid targetValid operatorValid valueValid =>
      .assignValue spanValid (liftExpr targetValid) operatorValid
        (liftExpr valueValid))
    (fun spanValid targetValid operatorValid =>
      .assignBitNot spanValid (liftExpr targetValid) operatorValid)
    (fun spanValid scrutineesSpanValid scrutineesValid _ armsInduction =>
      .matchWith spanValid scrutineesSpanValid
        (fun expression member => liftExpr
          (scrutineesValid expression member)) armsInduction)
    (fun spanValid headerValid initializerValid conditionValid postValid
        bodySpanValid _ bodyInduction =>
      .forLoop spanValid headerValid
        (fun item member => (initializerValid item member).mono liftExpr)
        (liftExpr conditionValid)
        (fun item member => (postValid item member).mono liftExpr)
        bodySpanValid bodyInduction)
    (fun spanValid conditionValid bodySpanValid _ bodyInduction =>
      .whileLoop spanValid (liftExpr conditionValid) bodySpanValid
        bodyInduction)
    (fun spanValid conditionValid thenSpanValid _ elseSpanValid _
        thenInduction elseInduction =>
      .ifThen spanValid (liftExpr conditionValid) thenSpanValid
        thenInduction elseSpanValid elseInduction)
    (fun spanValid _ bodyInduction => .block spanValid bodyInduction)
    (fun spanValid bodyValid =>
      .assembly spanValid fun statement member =>
        liftYul (bodyValid statement member))
    (fun spanValid => .breakStmt spanValid)
    (fun spanValid => .continueStmt spanValid)
    (fun spanValid => .error spanValid)
    (fun spanValid patternValid bodySpanValid _ bodyInduction =>
      .arm spanValid (liftPattern patternValid) bodySpanValid bodyInduction)
    (fun spanValid _ defaultSpanValid _ casesInduction defaultInduction =>
      .arms spanValid casesInduction defaultSpanValid defaultInduction)
    valid

namespace CoreStatement

/--
The depth-indexed approximation to recursive Core source-validity.  Depth only
decreases when an expression crosses into a lambda statement body; ordinary
statement nesting remains covered by `Statement.ValidFor` itself.
-/
def ValidForAt : Nat → SourceFile → Statement → Prop
  | 0, _, _ => True
  | depth + 1, file, statement =>
      Statement.ValidFor
        (Expr.ValidFor (ValidForAt depth))
        (Pattern.ValidFor (Expr.ValidFor (ValidForAt depth)))
        YulStmt.ValidFor file statement

/-- A Core statement is valid at every finite lambda/statement depth. -/
def ValidFor (file : SourceFile) (statement : Statement) : Prop :=
  ∀ depth, ValidForAt depth file statement

end CoreStatement

/-- Canonical recursive source-validity for Core expressions. -/
abbrev CoreExpr.ValidFor : SourceFile → Expr → Prop :=
  Expr.ValidFor CoreStatement.ValidFor

/-- Canonical recursive source-validity for Core patterns. -/
abbrev CorePattern.ValidFor : SourceFile → Pattern → Prop :=
  Pattern.ValidFor CoreExpr.ValidFor

namespace CoreStatement.ValidFor

/-- One well-formed statement layer closes the canonical recursive contract. -/
theorem ofStatement {file : SourceFile} {statement : Statement}
    (valid : Statement.ValidFor CoreExpr.ValidFor CorePattern.ValidFor
      YulStmt.ValidFor file statement) :
    CoreStatement.ValidFor file statement := by
  intro depth
  cases depth with
  | zero => trivial
  | succ depth =>
      exact valid.mono
        (fun expressionValid => expressionValid.mono
          (fun statementValid => statementValid depth))
        (fun patternValid => patternValid.mono fun expressionValid =>
          expressionValid.mono fun statementValid => statementValid depth)
        (fun yulValid => yulValid)

/-- A canonically valid Core statement has a source-valid outer range. -/
theorem span_valid {file : SourceFile} {statement : Statement}
    (valid : CoreStatement.ValidFor file statement) :
    statement.span.ValidFor file :=
  (valid 1).span_valid

end CoreStatement.ValidFor

end Solcore.Syntax
