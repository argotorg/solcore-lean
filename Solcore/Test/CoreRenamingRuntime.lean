import Solcore.Core.RenamingInsertion

/-! Dynamic regressions for evaluation under Core environment renaming. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def one : Word := Word.ofNatModulo 1
private def two : Word := Word.ofNatModulo 2

private theorem renameHeadBoolEmpty
    {environment : Environment} {expr : Expr} {value : Bool}
    (inserted : Value)
    (evaluation : Evaluates environment [] expr (.bool value) []) :
    Evaluates (inserted :: environment) [] (expr.weakenAt 0) (.bool value) [] := by
  obtain ⟨targetValue, targetStore, targetEvaluation, values, stores⟩ :=
    evaluation.rename
      (EnvironmentsRelated.headInsertion inserted environment) .nil
  have valueEquality := ValuesRelated.bool_iff.mp values
  subst targetValue
  cases stores
  simpa using targetEvaluation

private def identityApplication : Expr :=
  .apply (.lambda .word .word (.var 0)) (.var 0)

private theorem lambdaSimulation :
    ∃ targetValue targetStore,
      Evaluates [.bool true, .word one] []
        ((Expr.lambda .word .word (.var 1)).weakenAt 0)
        targetValue targetStore ∧
      ValuesRelated
        (.closure .word .word (.var 1) [.word one]) targetValue ∧
      StoresRelated [] targetStore := by
  have sourceEvaluation :
      Evaluates [.word one] [] (.lambda .word .word (.var 1))
        (.closure .word .word (.var 1) [.word one]) [] :=
    .lambda
  simpa using sourceEvaluation.rename
    (EnvironmentsRelated.headInsertion (.bool true) [.word one]) .nil

private theorem identityApplicationEvaluation :
    Evaluates [.word one] [] identityApplication (.word one) [] := by
  have functionEvaluation :
      Evaluates [.word one] [] (.lambda .word .word (.var 0))
        (.closure .word .word (.var 0) [.word one]) [] :=
    .lambda
  have argumentEvaluation :
      Evaluates [.word one] [] (.var 0) (.word one) [] :=
    .var (by simp)
  have bodyEvaluation :
      Evaluates [.word one, .word one] [] (.var 0) (.word one) [] :=
    .var (by simp)
  exact .apply functionEvaluation argumentEvaluation bodyEvaluation

private theorem identityApplicationTyping :
    HasType [.word] identityApplication .word :=
  infer_sound (by native_decide)

example :
    Evaluates [.bool true, .word one] []
      (identityApplication.weakenAt 0) (.word one) [] :=
  identityApplicationEvaluation.weakenAt_zero_word identityApplicationTyping
    (.cons .word .nil) StoreHasTypes.nil (.bool true)

private def cellRoundTrip : Expr :=
  .letE
    (.newCell .word (.word Word.zero))
    (.letE
      (.storeCell (.var 0) (.word one))
      (.loadCell (.var 1)))

private theorem cellRoundTripEvaluation :
    Evaluates [] [] cellRoundTrip (.word one) [.word one] := by
  have newEvaluation :
      Evaluates [] [] (.newCell .word (.word Word.zero))
        (.cellRef .word 0) [.word Word.zero] :=
    .newCell .word
  have storeEvaluation :
      Evaluates [.cellRef .word 0] [.word Word.zero]
        (.storeCell (.var 0) (.word one)) .unit [.word one] :=
    Evaluates.storeCell
      (elementType := .word) (location := 0)
      (oldValue := .word Word.zero) (newValue := .word one)
      (.var (by simp)) (by simp [Store.read?]) .word
      (by simp [Store.write?])
  have loadEvaluation :
      Evaluates [.unit, .cellRef .word 0] [.word one]
        (.loadCell (.var 1)) (.word one) [.word one] :=
    Evaluates.loadCell (elementType := .word) (location := 0)
      (.var (by simp)) (by simp [Store.read?])
  exact .letE newEvaluation (.letE storeEvaluation loadEvaluation)

private theorem cellRoundTripTyping :
    HasType [] cellRoundTrip .word :=
  infer_sound (by native_decide)

example :
    Evaluates [.bool false] [] (cellRoundTrip.weakenAt 0)
      (.word one) [.word one] :=
  cellRoundTripEvaluation.weakenAt_zero_word cellRoundTripTyping
    .nil StoreHasTypes.nil (.bool false)

private def dataType : DataTypeId := ⟨0⟩
private def constructor : ConstructorId := ⟨dataType, 0⟩

private def namedMatch : Expr :=
  .matchData dataType .bool
    (.construct constructor (.bool true))
    [.var 0]

private theorem namedMatchEvaluation :
    Evaluates [] [] namedMatch (.bool true) [] := by
  have scrutineeEvaluation :
      Evaluates [] [] (.construct constructor (.bool true))
        (.constructed constructor (.bool true)) [] :=
    .construct .bool
  have branchEvaluation :
      Evaluates [.bool true] [] (.var 0) (.bool true) [] :=
    .var (by simp)
  exact .matchData scrutineeEvaluation rfl rfl branchEvaluation

example :
    Evaluates [.word two] [] (namedMatch.weakenAt 0) (.bool true) [] :=
  renameHeadBoolEmpty (.word two) namedMatchEvaluation

private theorem freeWordEvaluation :
    Evaluates [.word two] [] (.var 0) (.word two) [] :=
  .var (by simp)

private theorem freeWordTyping :
    HasType [.word] (.var 0) .word :=
  .var (by simp)

example :
    Evaluates [.bool true, .word two] [] ((Expr.var 0).weakenAt 0)
      (.word two) [] :=
  freeWordEvaluation.weakenAt_zero_word freeWordTyping
    (.cons .word .nil) StoreHasTypes.nil (.bool true)

example :
    HasType [.bool, .word]
      (Expr.wordLt (.word one) ((Expr.var 0).weakenAt 0)) .bool := by
  exact infer_sound (by native_decide)

example :
    HasType [.bool, .word]
      (Expr.wordGe (.word one) ((Expr.var 0).weakenAt 0)) .bool := by
  exact infer_sound (by native_decide)

private def testClosureRelationNotEquality : IO Unit := do
  let source : Value := .closure .word .word (.var 1) [.word one]
  let target : Value :=
    .closure .word .word ((Expr.var 1).rename (Renaming.insertion 0).lift)
      [.bool true, .word one]
  have related : ValuesRelated source target :=
    .closure (Renaming.insertion 0)
      (EnvironmentsRelated.headInsertion (.bool true) [.word one])
  assertTrue (source != target)
    "renamed closures must not require raw structural equality"
  have _ := related
  pure ()

/-- Cover closure relation, application, cells, named matching, and the future
swapped-comparison weakening premise without adding runtime semantics. -/
def testCoreRenamingRuntime : IO Unit := do
  testClosureRelationNotEquality

end Tests
