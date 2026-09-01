import Solcore.Syntax.DeclarativeCoreArrayLiteralOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreExpressionAtomFinalRejectionGrammar
import Solcore.Syntax.DeclarativeCoreExpressionDotConstructorOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreExpressionLambdaOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreIdentifierExpressionOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreLiteralOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreParenthesizedOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreProxyExpressionOutcomeGrammar

/-!
Parser-independent ordinary outcomes for the ordered `expressionAtomCore`
dispatcher.

Literal and name branches cannot reject under their positive executable
guards.  The remaining five selected branches retain the exact earlier guard
failures, and the final branch is the established non-consuming rejection.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact ordinary success of the seven ordered Core atom branches. -/
inductive ExpressionAtomCoreOrdinaryParses
    (nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (parameterOrdinary :
      Remainder → Syntax.LambdaParameter → Remainder → Prop)
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop)
    (blockOrdinary : Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Syntax.Expr → Remainder → Prop where
  | literal {input output : Remainder} {expression : Syntax.Expr}
      (parsed : LiteralExpressionOrdinaryParses input expression output) :
      ExpressionAtomCoreOrdinaryParses nestedOrdinary parameterOrdinary
        typeOrdinary blockOrdinary input expression output
  | identifier {input output : Remainder} {expression : Syntax.Expr}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (parsed : IdentifierExpressionOrdinaryParses input expression output) :
      ExpressionAtomCoreOrdinaryParses nestedOrdinary parameterOrdinary
        typeOrdinary blockOrdinary input expression output
  | dotConstructor {input output : Remainder} {expression : Syntax.Expr}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (parsed : DotConstructorOrdinaryParses nestedOrdinary input expression
        output) :
      ExpressionAtomCoreOrdinaryParses nestedOrdinary parameterOrdinary
        typeOrdinary blockOrdinary input expression output
  | proxy {input output : Remainder} {expression : Syntax.Expr}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (parsed : ProxyExpressionOrdinaryParses typeOrdinary input expression
        output) :
      ExpressionAtomCoreOrdinaryParses nestedOrdinary parameterOrdinary
        typeOrdinary blockOrdinary input expression output
  | parenthesized {input output : Remainder} {expression : Syntax.Expr}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (parsed : ParenthesizedExpressionOrdinaryParses nestedOrdinary input
        expression output) :
      ExpressionAtomCoreOrdinaryParses nestedOrdinary parameterOrdinary
        typeOrdinary blockOrdinary input expression output
  | array {input output : Remainder} {expression : Syntax.Expr}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (parsed : ArrayLiteralExpressionOrdinaryParses nestedOrdinary input
        expression output) :
      ExpressionAtomCoreOrdinaryParses nestedOrdinary parameterOrdinary
        typeOrdinary blockOrdinary input expression output
  | lambda {input output : Remainder} {expression : Syntax.Expr}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (leftBracketAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftBracket))
      (parsed : LambdaExpressionOrdinaryParses parameterOrdinary typeOrdinary
        blockOrdinary input expression output) :
      ExpressionAtomCoreOrdinaryParses nestedOrdinary parameterOrdinary
        typeOrdinary blockOrdinary input expression output

/-- Exact ordinary rejection of the five fallible selected branches or the
final non-consuming branch. -/
inductive ExpressionAtomCoreRejects
    (nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop)
    (parameterOrdinary :
      Remainder → Syntax.LambdaParameter → Remainder → Prop)
    (parameterRejects : Remainder → Remainder → Prop)
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop)
    (typeRejects : Remainder → Remainder → Prop)
    (blockRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | dotConstructor {input rejected : Remainder}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (branchRejected : DotConstructorRejects nestedOrdinary nestedRejects
        input rejected) :
      ExpressionAtomCoreRejects nestedOrdinary nestedRejects
        parameterOrdinary parameterRejects typeOrdinary typeRejects
          blockRejects input rejected
  | proxy {input rejected : Remainder}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (branchRejected : ProxyExpressionRejects typeRejects input rejected) :
      ExpressionAtomCoreRejects nestedOrdinary nestedRejects
        parameterOrdinary parameterRejects typeOrdinary typeRejects
          blockRejects input rejected
  | parenthesized {input rejected : Remainder}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (branchRejected : ParenthesizedExpressionRejects nestedOrdinary
        nestedRejects input rejected) :
      ExpressionAtomCoreRejects nestedOrdinary nestedRejects
        parameterOrdinary parameterRejects typeOrdinary typeRejects
          blockRejects input rejected
  | array {input rejected : Remainder}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (branchRejected : ArrayLiteralExpressionRejects nestedOrdinary
        nestedRejects input rejected) :
      ExpressionAtomCoreRejects nestedOrdinary nestedRejects
        parameterOrdinary parameterRejects typeOrdinary typeRejects
          blockRejects input rejected
  | lambda {input rejected : Remainder}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (leftBracketAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftBracket))
      (branchRejected : LambdaExpressionRejects parameterOrdinary
        parameterRejects typeOrdinary typeRejects blockRejects input rejected) :
      ExpressionAtomCoreRejects nestedOrdinary nestedRejects
        parameterOrdinary parameterRejects typeOrdinary typeRejects
          blockRejects input rejected
  | final {input : Remainder}
      (branchRejected : ExpressionAtomCoreFinalRejects input) :
      ExpressionAtomCoreRejects nestedOrdinary nestedRejects
        parameterOrdinary parameterRejects typeOrdinary typeRejects
          blockRejects input input

end Solcore.Syntax.DeclarativeGrammar
