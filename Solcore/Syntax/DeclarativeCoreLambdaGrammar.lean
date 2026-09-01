import Solcore.Syntax.DeclarativeGrammar

/-!
Parser-independent diagnostic-free grammar for Core lambda parameters and
lambda-expression type suffixes.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Type shapes that do not trigger the parameter-specific comptime warning. -/
def ParameterTypeAllowed (type : Syntax.TypeExpr) : Prop :=
  match type.value with
  | .comptime .. => False
  | _ => True

/-- The contextual `comptime` marker followed by an identifier starts here. -/
def ComptimeLambdaParameterStartsAt (input : Remainder) : Prop :=
  ∃ markerSpan nameSpan spelling,
    TokenAt input.tokens input.endIndex input.cursor {
      span := markerSpan
      value := .identifier ContextualKeyword.comptime.spelling
    } ∧
    TokenAt input.tokens input.endIndex (input.cursor + 1) {
      span := nameSpan
      value := .identifier spelling
    }

/-- Exact inferred-or-typed suffix of an ordinary lambda parameter. -/
inductive OrdinaryLambdaParameterTailParses (name : Syntax.Identifier) :
    Remainder → Syntax.LambdaParameter → Remainder → Prop where
  | inferred {input : Remainder}
      (colonAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .colon)) :
      OrdinaryLambdaParameterTailParses name input {
        span := name.span
        value := .inferred name
      } input
  | typed {input afterColon output : Remainder} {type : Syntax.TypeExpr}
      (colonSpan : SourceSpan)
      (colonToken : ExactTokenParses (.symbol .colon) input colonSpan
        afterColon)
      (typeParsed : TypeExprParses afterColon type output)
      (typeAllowed : ParameterTypeAllowed type) :
      OrdinaryLambdaParameterTailParses name input {
        span := SourceSpan.cover name.span type.span
        value := .typed none name type
      } output

/-- Exact diagnostic-free ordinary lambda parameter grammar. -/
inductive OrdinaryLambdaParameterParses :
    Remainder → Syntax.LambdaParameter → Remainder → Prop where
  | parsed {input afterName output : Remainder}
      {name : Syntax.Identifier} {parameter : Syntax.LambdaParameter}
      (nameParsed : IdentifierParses input name afterName)
      (notComptimeName :
        name.value ≠ ContextualKeyword.comptime.spelling)
      (tail : OrdinaryLambdaParameterTailParses name afterName parameter
        output) :
      OrdinaryLambdaParameterParses input parameter output

/-- Exact diagnostic-free contextual-comptime lambda parameter grammar. -/
inductive ComptimeLambdaParameterParses :
    Remainder → Syntax.LambdaParameter → Remainder → Prop where
  | parsed {input afterMarker afterName afterColon output : Remainder}
      {name : Syntax.Identifier} {type : Syntax.TypeExpr}
      (markerSpan colonSpan : SourceSpan)
      (markerToken : ExactTokenParses
        (.identifier ContextualKeyword.comptime.spelling) input markerSpan
          afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (colonToken : ExactTokenParses (.symbol .colon) afterName colonSpan
        afterColon)
      (typeParsed : TypeExprParses afterColon type output)
      (typeAllowed : ParameterTypeAllowed type) :
      ComptimeLambdaParameterParses input {
        span := SourceSpan.cover markerSpan type.span
        value := .typed (some markerSpan) name type
      } output

/-- Exact ordered diagnostic-free grammar of one lambda parameter. -/
inductive LambdaParameterParses :
    Remainder → Syntax.LambdaParameter → Remainder → Prop where
  | comptime {input output : Remainder}
      {parameter : Syntax.LambdaParameter}
      (parsed : ComptimeLambdaParameterParses input parameter output) :
      LambdaParameterParses input parameter output
  | ordinary {input output : Remainder}
      {parameter : Syntax.LambdaParameter}
      (comptimeAbsent : ¬ ComptimeLambdaParameterStartsAt input)
      (parsed : OrdinaryLambdaParameterParses input parameter output) :
      LambdaParameterParses input parameter output

/-- Exact optional `-> Type` suffix of a lambda expression. -/
inductive OptionalLambdaReturnTypeParses :
    Remainder → Option Syntax.TypeExpr → Remainder → Prop where
  | absent {input : Remainder}
      (arrowAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .arrow)) :
      OptionalLambdaReturnTypeParses input none input
  | present {input afterArrow output : Remainder} {type : Syntax.TypeExpr}
      (arrowSpan : SourceSpan)
      (arrowToken : ExactTokenParses (.symbol .arrow) input arrowSpan
        afterArrow)
      (typeParsed : TypeExprParses afterArrow type output) :
      OptionalLambdaReturnTypeParses input (some type) output

end Solcore.Syntax.DeclarativeGrammar
