import Solcore.Syntax.Parser.CoreExpressionBinaryLayerSoundnessProperties
import Solcore.Syntax.Parser.CoreExpressionConditionalSoundnessProperties
import Solcore.Syntax.Parser.CoreExpressionUnarySoundnessProperties

/-!
Aggregate diagnostic reflection and exact declarative soundness for one Core
expression recursion layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A complete expression layer reflects diagnostic freedom through every
precedence layer and its supplied recursive and postfix parsers. -/
theorem expressionLayer_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (postfixReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (expressionPostfix nested block)) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (expressionLayer nested block) := by
  let unary := ExpressionInternals.expressionUnary nested block
  let multiply := ExpressionInternals.leftAssociative unary 8
  let add := ExpressionInternals.leftAssociative multiply 7
  let bitAnd := ExpressionInternals.leftAssociative add 6
  let bitXor := ExpressionInternals.leftAssociative bitAnd 5
  let bitOr := ExpressionInternals.leftAssociative bitXor 4
  let relational := ExpressionInternals.nonAssociative bitOr 3
  let equality := ExpressionInternals.nonAssociative relational 2
  let logicalAnd := ExpressionInternals.leftAssociative equality 1
  let logicalOr := ExpressionInternals.leftAssociative logicalAnd 0
  have unaryReflects : Parser.ReflectsDiagnosticFreeOnSuccess unary :=
    ExpressionInternals.expressionUnary_reflectsDiagnosticFreeOnSuccess
      nested block postfixReflects
  have multiplyReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess multiply :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      unary unaryReflects 8
  have addReflects : Parser.ReflectsDiagnosticFreeOnSuccess add :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      multiply multiplyReflects 7
  have bitAndReflects : Parser.ReflectsDiagnosticFreeOnSuccess bitAnd :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      add addReflects 6
  have bitXorReflects : Parser.ReflectsDiagnosticFreeOnSuccess bitXor :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      bitAnd bitAndReflects 5
  have bitOrReflects : Parser.ReflectsDiagnosticFreeOnSuccess bitOr :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      bitXor bitXorReflects 4
  have relationalReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess relational :=
    ExpressionInternals.nonAssociative_reflectsDiagnosticFreeOnSuccess
      bitOr bitOrReflects 3
  have equalityReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess equality :=
    ExpressionInternals.nonAssociative_reflectsDiagnosticFreeOnSuccess
      relational relationalReflects 2
  have logicalAndReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess logicalAnd :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      equality equalityReflects 1
  have logicalOrReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess logicalOr :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      logicalAnd logicalAndReflects 0
  exact ExpressionInternals.conditional_reflectsDiagnosticFreeOnSuccess
    nested logicalOr nestedReflects logicalOrReflects

/-- Every diagnostic-free successful expression layer follows the exact
parser-independent unary, precedence, associativity, and conditional grammar. -/
theorem expressionLayer_success_sound
    (nested : Parser Expr) (block : Parser Block)
    (nestedParses postfixParses :
      DeclarativeGrammar.Remainder → Expr →
        DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → nested input = .ok value next →
        nestedParses input.declarativeRemainder value
          next.declarativeRemainder)
    (postfixReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (expressionPostfix nested block))
    (postfixSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] →
        expressionPostfix nested block input =
          .ok value next →
        postfixParses input.declarativeRemainder value
          next.declarativeRemainder)
    {input next : State} {value : Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : expressionLayer nested block input = .ok value next) :
    DeclarativeGrammar.ExpressionLayerParses nestedParses postfixParses
      input.declarativeRemainder value next.declarativeRemainder := by
  let unary := ExpressionInternals.expressionUnary nested block
  let multiply := ExpressionInternals.leftAssociative unary 8
  let add := ExpressionInternals.leftAssociative multiply 7
  let bitAnd := ExpressionInternals.leftAssociative add 6
  let bitXor := ExpressionInternals.leftAssociative bitAnd 5
  let bitOr := ExpressionInternals.leftAssociative bitXor 4
  let relational := ExpressionInternals.nonAssociative bitOr 3
  let equality := ExpressionInternals.nonAssociative relational 2
  let logicalAnd := ExpressionInternals.leftAssociative equality 1
  let logicalOr := ExpressionInternals.leftAssociative logicalAnd 0
  let unaryParses :=
    DeclarativeGrammar.ExpressionUnaryParses postfixParses
  let multiplyParses :=
    DeclarativeGrammar.LeftAssociativeParses unaryParses 8
  let addParses :=
    DeclarativeGrammar.LeftAssociativeParses multiplyParses 7
  let bitAndParses :=
    DeclarativeGrammar.LeftAssociativeParses addParses 6
  let bitXorParses :=
    DeclarativeGrammar.LeftAssociativeParses bitAndParses 5
  let bitOrParses :=
    DeclarativeGrammar.LeftAssociativeParses bitXorParses 4
  let relationalParses :=
    DeclarativeGrammar.NonAssociativeParses bitOrParses 3
  let equalityParses :=
    DeclarativeGrammar.NonAssociativeParses relationalParses 2
  let logicalAndParses :=
    DeclarativeGrammar.LeftAssociativeParses equalityParses 1
  let logicalOrParses :=
    DeclarativeGrammar.LeftAssociativeParses logicalAndParses 0
  have unaryReflects : Parser.ReflectsDiagnosticFreeOnSuccess unary :=
    ExpressionInternals.expressionUnary_reflectsDiagnosticFreeOnSuccess
      nested block postfixReflects
  have unarySound : ∀ {layerInput layerNext : State} {expression : Expr},
      layerNext.diagnosticsRev = [] →
      unary layerInput = .ok expression layerNext →
      unaryParses layerInput.declarativeRemainder expression
        layerNext.declarativeRemainder := by
    intro layerInput layerNext expression layerFree layerResult
    exact ExpressionInternals.expressionUnary_success_sound
      nested block postfixParses postfixReflects postfixSound
        layerFree layerResult
  have multiplyReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess multiply :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      unary unaryReflects 8
  have multiplySound :
      ∀ {layerInput layerNext : State} {expression : Expr},
        layerNext.diagnosticsRev = [] →
        multiply layerInput = .ok expression layerNext →
        multiplyParses layerInput.declarativeRemainder expression
          layerNext.declarativeRemainder := by
    intro layerInput layerNext expression layerFree layerResult
    exact ExpressionInternals.leftAssociative_success_sound
      unary unaryParses unaryReflects unarySound 8 layerFree layerResult
  have addReflects : Parser.ReflectsDiagnosticFreeOnSuccess add :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      multiply multiplyReflects 7
  have addSound : ∀ {layerInput layerNext : State} {expression : Expr},
      layerNext.diagnosticsRev = [] →
      add layerInput = .ok expression layerNext →
      addParses layerInput.declarativeRemainder expression
        layerNext.declarativeRemainder := by
    intro layerInput layerNext expression layerFree layerResult
    exact ExpressionInternals.leftAssociative_success_sound
      multiply multiplyParses multiplyReflects multiplySound 7
        layerFree layerResult
  have bitAndReflects : Parser.ReflectsDiagnosticFreeOnSuccess bitAnd :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      add addReflects 6
  have bitAndSound : ∀ {layerInput layerNext : State} {expression : Expr},
      layerNext.diagnosticsRev = [] →
      bitAnd layerInput = .ok expression layerNext →
      bitAndParses layerInput.declarativeRemainder expression
        layerNext.declarativeRemainder := by
    intro layerInput layerNext expression layerFree layerResult
    exact ExpressionInternals.leftAssociative_success_sound
      add addParses addReflects addSound 6 layerFree layerResult
  have bitXorReflects : Parser.ReflectsDiagnosticFreeOnSuccess bitXor :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      bitAnd bitAndReflects 5
  have bitXorSound : ∀ {layerInput layerNext : State} {expression : Expr},
      layerNext.diagnosticsRev = [] →
      bitXor layerInput = .ok expression layerNext →
      bitXorParses layerInput.declarativeRemainder expression
        layerNext.declarativeRemainder := by
    intro layerInput layerNext expression layerFree layerResult
    exact ExpressionInternals.leftAssociative_success_sound
      bitAnd bitAndParses bitAndReflects bitAndSound 5 layerFree layerResult
  have bitOrReflects : Parser.ReflectsDiagnosticFreeOnSuccess bitOr :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      bitXor bitXorReflects 4
  have bitOrSound : ∀ {layerInput layerNext : State} {expression : Expr},
      layerNext.diagnosticsRev = [] →
      bitOr layerInput = .ok expression layerNext →
      bitOrParses layerInput.declarativeRemainder expression
        layerNext.declarativeRemainder := by
    intro layerInput layerNext expression layerFree layerResult
    exact ExpressionInternals.leftAssociative_success_sound
      bitXor bitXorParses bitXorReflects bitXorSound 4 layerFree layerResult
  have relationalReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess relational :=
    ExpressionInternals.nonAssociative_reflectsDiagnosticFreeOnSuccess
      bitOr bitOrReflects 3
  have relationalSound :
      ∀ {layerInput layerNext : State} {expression : Expr},
        layerNext.diagnosticsRev = [] →
        relational layerInput = .ok expression layerNext →
        relationalParses layerInput.declarativeRemainder expression
          layerNext.declarativeRemainder := by
    intro layerInput layerNext expression layerFree layerResult
    exact ExpressionInternals.nonAssociative_success_sound
      bitOr bitOrParses bitOrReflects bitOrSound 3 layerFree layerResult
  have equalityReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess equality :=
    ExpressionInternals.nonAssociative_reflectsDiagnosticFreeOnSuccess
      relational relationalReflects 2
  have equalitySound :
      ∀ {layerInput layerNext : State} {expression : Expr},
        layerNext.diagnosticsRev = [] →
        equality layerInput = .ok expression layerNext →
        equalityParses layerInput.declarativeRemainder expression
          layerNext.declarativeRemainder := by
    intro layerInput layerNext expression layerFree layerResult
    exact ExpressionInternals.nonAssociative_success_sound
      relational relationalParses relationalReflects relationalSound 2
        layerFree layerResult
  have logicalAndReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess logicalAnd :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      equality equalityReflects 1
  have logicalAndSound :
      ∀ {layerInput layerNext : State} {expression : Expr},
        layerNext.diagnosticsRev = [] →
        logicalAnd layerInput = .ok expression layerNext →
        logicalAndParses layerInput.declarativeRemainder expression
          layerNext.declarativeRemainder := by
    intro layerInput layerNext expression layerFree layerResult
    exact ExpressionInternals.leftAssociative_success_sound
      equality equalityParses equalityReflects equalitySound 1
        layerFree layerResult
  have logicalOrReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess logicalOr :=
    ExpressionInternals.leftAssociative_reflectsDiagnosticFreeOnSuccess
      logicalAnd logicalAndReflects 0
  have logicalOrSound :
      ∀ {layerInput layerNext : State} {expression : Expr},
        layerNext.diagnosticsRev = [] →
        logicalOr layerInput = .ok expression layerNext →
        logicalOrParses layerInput.declarativeRemainder expression
          layerNext.declarativeRemainder := by
    intro layerInput layerNext expression layerFree layerResult
    exact ExpressionInternals.leftAssociative_success_sound
      logicalAnd logicalAndParses logicalAndReflects logicalAndSound 0
        layerFree layerResult
  exact ExpressionInternals.conditional_success_sound
    nested logicalOr nestedParses logicalOrParses nestedReflects nestedSound
      logicalOrReflects logicalOrSound diagnosticFree result

end Solcore.Syntax.Parser
