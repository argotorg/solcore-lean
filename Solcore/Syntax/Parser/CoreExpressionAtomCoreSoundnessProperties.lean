import Solcore.Syntax.Parser.CoreExpressionAtomCoreDiagnosticReflectionProperties
import Solcore.Syntax.Parser.CoreExpressionAtomDispatcherLookaheadProperties
import Solcore.Syntax.Parser.CoreExpressionCollectionAtomSoundnessProperties

/-!
Exact diagnostic-free soundness for the ordered Core expression-atom
dispatcher.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/--
Every diagnostic-free Core atom success follows exactly one of the seven
ordered declarative branches, with all earlier executable guards excluded.
-/
theorem expressionAtomCore_success_sound
    (nested : Parser Expr) (block : Parser Block)
    (nestedParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (blockParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {nestedInput nestedNext : State} {nestedValue : Expr},
      nestedNext.diagnosticsRev = [] →
      nested nestedInput = .ok nestedValue nestedNext →
      nestedParses nestedInput.declarativeRemainder nestedValue
        nestedNext.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    (blockReflects : Parser.ReflectsDiagnosticFreeOnSuccess block)
    (blockSound : ∀ {blockInput blockNext : State} {blockValue : Block},
      blockNext.diagnosticsRev = [] →
      block blockInput = .ok blockValue blockNext →
      blockParses blockInput.declarativeRemainder blockValue
        blockNext.declarativeRemainder)
    {input next : State} {value : Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : expressionAtomCore nested block input = .ok value next) :
    DeclarativeGrammar.ExpressionAtomCoreParses nestedParses blockParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold expressionAtomCore at result
  split at result
  next literalPresent =>
    exact .literal (literalExpression_success_sound result)
  next literalAbsent =>
    have literalAbsentEq : isCoreLiteral input = false :=
      Bool.eq_false_iff.mpr literalAbsent
    have noLiteral :=
      not_coreLiteralStartsAt_of_isCoreLiteral_eq_false literalAbsentEq
    split at result
    next namePresent =>
      exact .identifier noLiteral
        (identifierExpression_success_sound result)
    next nameAbsent =>
      have nameAbsentEq :
          (isBooleanValue input || isIdentifier input) = false :=
        Bool.eq_false_iff.mpr nameAbsent
      have noName :=
        not_expressionNameStartsAt_of_expressionNameGuard_eq_false
          nameAbsentEq
      split at result
      next dotPresent =>
        exact .dotConstructor noLiteral noName
          (dotConstructor_success_sound nested nestedParses nestedReflects
            nestedSound nestedShape diagnosticFree result)
      next dotAbsent =>
        have dotAbsentEq : isSymbol input .dot = false :=
          Bool.eq_false_iff.mpr dotAbsent
        have noDot := symbolAbsentAt_of_isSymbol_eq_false .dot dotAbsentEq
        split at result
        next atPresent =>
          exact .proxy noLiteral noName noDot
            (proxyExpression_success_sound result)
        next atAbsent =>
          have atAbsentEq : isSymbol input .at = false :=
            Bool.eq_false_iff.mpr atAbsent
          have noAt := symbolAbsentAt_of_isSymbol_eq_false .at atAbsentEq
          split at result
          next leftParenPresent =>
            exact .parenthesized noLiteral noName noDot noAt
              (parenthesized_success_sound nested nestedParses nestedReflects
                nestedSound diagnosticFree result)
          next leftParenAbsent =>
            have leftParenAbsentEq : isSymbol input .leftParen = false :=
              Bool.eq_false_iff.mpr leftParenAbsent
            have noLeftParen := symbolAbsentAt_of_isSymbol_eq_false
              .leftParen leftParenAbsentEq
            split at result
            next leftBracketPresent =>
              exact .array noLiteral noName noDot noAt noLeftParen
                (arrayLiteral_success_sound nested nestedParses nestedReflects
                  nestedSound nestedShape diagnosticFree result)
            next leftBracketAbsent =>
              have leftBracketAbsentEq :
                  isSymbol input .leftBracket = false :=
                Bool.eq_false_iff.mpr leftBracketAbsent
              have noLeftBracket := symbolAbsentAt_of_isSymbol_eq_false
                .leftBracket leftBracketAbsentEq
              split at result
              next lambdaPresent =>
                exact .lambda noLiteral noName noDot noAt noLeftParen
                  noLeftBracket
                  (lambdaExpression_success_sound block blockParses
                    blockReflects blockSound diagnosticFree result)
              next lambdaAbsent =>
                simp [rejectAt] at result

end Solcore.Syntax.Parser.ExpressionAtomInternals
