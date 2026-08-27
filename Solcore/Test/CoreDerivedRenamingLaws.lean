import Solcore.Core.ComparisonFlags
import Solcore.Core.ShortCircuit
import Solcore.Core.Machine

/-! Focused regressions for arbitrary renaming of older derived builders. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

/-- A genuinely non-insertion renaming: the first two free variables swap. -/
private def swap01 : Renaming
  | 0 => 1
  | 1 => 0
  | index + 2 => index + 2

example (value : Expr) :
    value.boolToWord.rename swap01 = (value.rename swap01).boolToWord :=
  Expr.rename_boolToWord value swap01

example (value : Expr) :
    value.wordToBool.rename swap01 = (value.rename swap01).wordToBool :=
  Expr.rename_wordToBool value swap01

example (value : Expr) :
    value.wordIsZero.rename swap01 = (value.rename swap01).wordIsZero :=
  Expr.rename_wordIsZero value swap01

example (value : Expr) :
    value.wordIsNonzero.rename swap01 = (value.rename swap01).wordIsNonzero :=
  Expr.rename_wordIsNonzero value swap01

example (left right : Expr) :
    (left.boolAnd right).rename swap01 =
      (left.rename swap01).boolAnd (right.rename swap01) :=
  Expr.rename_boolAnd left right swap01

example (left right : Expr) :
    (left.boolOr right).rename swap01 =
      (left.rename swap01).boolOr (right.rename swap01) :=
  Expr.rename_boolOr left right swap01

example (left right : Expr) :
    (left.wordEqFlag right).rename swap01 =
      (left.rename swap01).wordEqFlag (right.rename swap01) :=
  Expr.rename_wordEqFlag left right swap01

example (left right : Expr) :
    (left.wordGtFlag right).rename swap01 =
      (left.rename swap01).wordGtFlag (right.rename swap01) :=
  Expr.rename_wordGtFlag left right swap01

private def testGoldenRenamings : IO Unit := do
  let left : Expr := .var 0
  let right : Expr := .var 1
  let zero : Expr := .word Word.zero
  let one : Expr := .word (Word.ofNatModulo 1)

  assertTrue
    (left.boolToWord.rename swap01 == .ifE (.var 1) one zero)
    "boolToWord did not rename its free operand"
  assertTrue
    (left.wordToBool.rename swap01 ==
      Expr.unary .boolNot (Expr.binary .wordEq (.var 1) zero))
    "wordToBool did not rename its free operand"
  assertTrue
    (left.wordIsZero.rename swap01 ==
      (Expr.binary .wordEq (.var 1) zero).boolToWord)
    "wordIsZero did not rename its free operand"
  assertTrue
    (left.wordIsNonzero.rename swap01 == (Expr.var 1).wordIsNonzero)
    "wordIsNonzero did not rename its free operand"

  assertTrue
    ((left.boolAnd right).rename swap01 ==
      .ifE (.var 1) (.var 0) (.bool false))
    "boolAnd did not preserve condition and selected-branch positions"
  assertTrue
    ((left.boolOr right).rename swap01 ==
      .ifE (.var 1) (.bool true) (.var 0))
    "boolOr did not preserve condition and selected-branch positions"
  assertTrue
    ((left.wordEqFlag right).rename swap01 ==
      (Expr.binary .wordEq (.var 1) (.var 0)).boolToWord)
    "wordEqFlag did not rename both operands"
  assertTrue
    ((left.wordGtFlag right).rename swap01 ==
      (Expr.binary .wordGt (.var 1) (.var 0)).boolToWord)
    "wordGtFlag did not rename both operands"

private def runIn (expression : Expr) (environment : Environment) : RunResult :=
  Solcore.Core.run 32 (State.initial expression environment)

private def testRenamedEvaluation : IO Unit := do
  let one := Word.ofNatModulo 1
  let maximum := Word.maximum

  let conversion := (Expr.var 0).boolToWord.rename swap01
  assertTrue
    (runIn conversion [.word Word.zero, .bool true] == .done (.word one))
    "renamed conversion read the wrong environment position"

  let conjunction := (Expr.boolAnd (.var 0) (.var 1)).rename swap01
  assertTrue
    (runIn conjunction [.bool false, .bool true] == .done (.bool false))
    "renamed short-circuit expression changed its branch meaning"

  let comparison := (Expr.wordGtFlag (.var 0) (.var 1)).rename swap01
  assertTrue
    (runIn comparison [.word Word.zero, .word maximum] == .done (.word one))
    "renamed comparison flag read its operands in the wrong positions"

/-- Cover all eight public laws with a non-insertion mapping and representative
evaluation from each derived-builder family. -/
def testCoreDerivedRenamingLaws : IO Unit := do
  testGoldenRenamings
  testRenamedEvaluation

end Tests
