import Solcore.Resolved.TypingProperties
import Solcore.Resolved.EvaluationProperties
import Solcore.Core.Machine

/-! Concrete resolved-local regressions. These test structured identities, not
source-name resolution; repeated identities intentionally exercise first match. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Resolved

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def pathA : Workspace.ModulePath := ⟨[⟨"A", by decide⟩], by decide⟩
private def pathB : Workspace.ModulePath := ⟨[⟨"B", by decide⟩], by decide⟩
private def outerId : LocalId := ⟨⟨⟨.main, pathA⟩, 0⟩, 0⟩
private def innerId : LocalId := { outerId with binderIndex := 1 }
private def otherDeclaration : LocalId :=
  { outerId with owner := { outerId.owner with declarationIndex := 1 } }
private def otherModule : LocalId := ⟨⟨⟨.main, pathB⟩, 0⟩, 0⟩
private def otherLibrary : LocalId := ⟨⟨⟨.standard, pathA⟩, 0⟩, 0⟩
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def environment : Environment := [(outerId, .bool true)]
private def context : Context := [(outerId, .bool)]
private def stored : Core.Store := [.word (w 19), .bool false]

example : outerId ≠ innerId ∧ outerId ≠ otherDeclaration ∧
    outerId ≠ otherModule ∧ outerId ≠ otherLibrary := by decide

example : LocalScope.index? [outerId] outerId = some 0 ∧
    LocalScope.index? [outerId] innerId = none := by decide

private def noCapture : Expr := .letE innerId (.bool false) (.var outerId)
private def noCaptureCore : Core.Expr := .letE (.bool false) (.var 1)

private theorem noCapture_lowered :
    Lowers (LocalScope.ids environment) noCapture noCaptureCore :=
  .letE .bool (.var (.tail (by decide) .head))

private theorem noCapture_typed : HasType context noCapture .bool :=
  .letE .bool (.var (.tail (by decide) .head))

private theorem noCapture_evaluates (store : Core.Store) :
    Evaluates environment store noCapture (.bool true) store :=
  .letE .bool (.var (.tail (by decide) .head))

example (store : Core.Store) :
    Core.Evaluates (LocalScope.values environment) store noCaptureCore (.bool true) store :=
  (noCapture_evaluates store).toCore noCapture_lowered

example : noCapture.lower? [outerId] = some noCaptureCore := noCapture_lowered.complete
example : infer? context noCapture = some .bool := infer_complete noCapture_typed

private def initializer : Expr := .letE innerId (.var outerId) (.var innerId)
private def initializerCore : Core.Expr := .letE (.var 0) (.var 0)

private theorem initializer_lowered :
    Lowers (LocalScope.ids environment) initializer initializerCore :=
  .letE (.var .head) (.var .head)

private theorem initializer_evaluates (store : Core.Store) :
    Evaluates environment store initializer (.bool true) store :=
  .letE (.var .head) (.var .head)

example (store : Core.Store) :
    Core.Evaluates (LocalScope.values environment) store initializerCore (.bool true) store :=
  (initializer_evaluates store).toCore initializer_lowered

-- A binder is unavailable in its own initializer when absent from the old scope.
private def selfInitializer : Expr := .letE innerId (.var innerId) .unit
example : selfInitializer.lower? [] = none := by decide
example {core : Core.Expr} : ¬ Lowers [] selfInitializer core := by
  intro lowered
  have impossible := lowered.complete
  change none = some core at impossible
  cases impossible
example {value : Core.Value} {store finalStore : Core.Store} :
    ¬ Evaluates [] store selfInitializer value finalStore := by
  intro evaluation
  cases evaluation with
  | letE initializer _ =>
      cases initializer with
      | var found => cases found

-- All expression constructors appear here or in the separate unit case.
private def combined : Expr :=
  .letE outerId (.binary .wordAdd (.word (w 2)) (.word (w 3)))
    (.ifE (.unary .boolNot (.bool false)) (.var outerId) (.word (w 0)))
private def combinedCore : Core.Expr :=
  .letE (.binary .wordAdd (.word (w 2)) (.word (w 3)))
    (.ifE (.unary .boolNot (.bool false)) (.var 0) (.word (w 0)))

private theorem combined_lowered : Lowers [] combined combinedCore :=
  .letE (.binary .word .word) (.ifE (.unary .bool) (.var .head) .word)

private theorem combined_typed : HasType [] combined .word :=
  .letE (.binary .word .word) (.ifE (.unary .bool) (.var .head) .word)

private theorem combined_evaluates (store : Core.Store) :
    Evaluates [] store combined (.word (w 5)) store :=
  .letE (.binary .word .word rfl)
    (.ifTrue (.unary .bool rfl) (.var .head))

example (store : Core.Store) : Core.Evaluates [] store combinedCore (.word (w 5)) store :=
  (combined_evaluates store).toCore combined_lowered
example (store : Core.Store) : Evaluates [] store combined (.word (w 5)) store :=
  Evaluates.ofCore combined_lowered ((combined_evaluates store).toCore combined_lowered)
example : infer? [] combined = some .word := infer_complete combined_typed
example (store : Core.Store) : Evaluates [] store .unit .unit store := .unit
example : Lowers [] .unit .unit := .unit
example : HasType [] .unit .unit := .unit

private def duplicates : Environment := [(outerId, .bool false), (outerId, .bool true)]
example : LocalScope.Lookup duplicates outerId (.bool false) := .head
example : LocalScope.IndexOf (LocalScope.ids duplicates) outerId 0 := .head
example : ¬ LocalScope.Lookup duplicates outerId (.bool true) := by
  intro found
  have impossible := found.value_unique (show LocalScope.Lookup duplicates outerId (.bool false) from .head)
  cases impossible
example (store : Core.Store) : Evaluates duplicates store (.var outerId) (.bool false) store :=
  .var .head

private def badUnary : Expr := .unary .boolNot (.word (w 0))
private def badBinary : Expr := .binary .wordAdd (.bool true) (.word (w 1))
private def badCondition : Expr := .ifE .unit (.bool true) (.bool false)

private theorem rejected_no_type {expr : Expr} (rejected : infer? [] expr = none)
    {type : Core.Ty} : ¬ HasType [] expr type := by
  intro typed
  have accepted := infer_complete typed
  rw [rejected] at accepted
  cases accepted

example {type : Core.Ty} : ¬ HasType [] badUnary type := rejected_no_type (by decide)
example {type : Core.Ty} : ¬ HasType [] badBinary type := rejected_no_type (by decide)
example {type : Core.Ty} : ¬ HasType [] badCondition type := rejected_no_type (by decide)

-- Evaluation selects one branch, but lowering and type checking inspect both.
private def skippedMissing : Expr := .ifE (.bool true) .unit (.var innerId)
private theorem skipped_evaluates (store : Core.Store) :
    Evaluates [] store skippedMissing .unit store := .ifTrue .bool .unit
example : skippedMissing.lower? [] = none := by decide
example {type : Core.Ty} : ¬ HasType [] skippedMissing type := rejected_no_type (by decide)
example {value : Core.Value} {store finalStore : Core.Store}
    (evaluation : Evaluates [] store skippedMissing value finalStore) :
    value = .unit ∧ finalStore = store :=
  evaluation_deterministic evaluation (skipped_evaluates store)
example (store : Core.Store) :
    Evaluates [] store (.ifE (.bool false) (.var innerId) .unit) .unit store :=
  .ifFalse .bool .unit

private def testIdentityAndScope : IO Unit := do
  for other in [innerId, otherDeclaration, otherModule, otherLibrary] do
    assertTrue (decide (outerId ≠ other)) "structured local identity components collided"
  assertTrue (decide (LocalScope.lookup? environment outerId = some (.bool true)))
    "head local lookup failed"
  assertTrue (decide (LocalScope.index? [outerId] outerId = some 0)) "head index was not zero"
  assertTrue (decide (LocalScope.lookup? environment innerId = none)) "absent local was found"
  assertTrue (decide (LocalScope.index? [outerId] innerId = none)) "absence became index zero"
  assertTrue (decide (LocalScope.lookup? duplicates outerId = some (.bool false)))
    "duplicate identity did not use first value"
  assertTrue (decide (LocalScope.index? (LocalScope.ids duplicates) outerId = some 0))
    "duplicate identity did not use first index"
  assertTrue (decide (infer? [(outerId, .bool), (outerId, .word)] (.var outerId) = some .bool))
    "duplicate identity did not use first type"

private def testLoweringAndExecution : IO Unit := do
  let cases : List (Environment × Expr × Core.Expr × Core.Value) := [
    ([], .unit, .unit, .unit),
    (environment, noCapture, noCaptureCore, .bool true),
    (environment, initializer, initializerCore, .bool true),
    ([], combined, combinedCore, .word (w 5)),
    (duplicates, .var outerId, .var 0, .bool false)]
  for (env, expr, core, expected) in cases do
    assertTrue (decide (expr.lower? (LocalScope.ids env) = some core))
      "resolved local lowering produced the wrong positional expression"
    assertTrue (Core.runStateful 40 (Core.State.initial core (LocalScope.values env) stored) ==
      .done expected stored) "lowered local execution changed the value or store"
  assertTrue (decide (selfInitializer.lower? [] = none)) "initializer saw its new binder"
  assertTrue (decide (infer? context noCapture = some .bool)) "outer variable type was captured"
  assertTrue (decide (infer? [] combined = some .word)) "combined local expression was rejected"
  assertTrue (decide (skippedMissing.lower? [] = none)) "lowering skipped an ill-scoped branch"
  assertTrue (decide (infer? [] skippedMissing = none)) "checking skipped an ill-scoped branch"

private def testRejections : IO Unit := do
  let cases : List (Expr × Core.Expr × Core.MachineFault) := [
    (badUnary, .unary .boolNot (.word (w 0)), .invalidUnaryOperand .boolNot (.word (w 0))),
    (badBinary, .binary .wordAdd (.bool true) (.word (w 1)),
      .invalidBinaryOperands .wordAdd (.bool true) (.word (w 1))),
    (badCondition, .ifE .unit (.bool true) (.bool false), .expectedBool .unit)]
  for (expr, core, fault) in cases do
    assertTrue (decide (expr.lower? [] = some core)) "well-scoped ill-typed expression failed lowering"
    assertTrue (decide (infer? [] expr = none)) "ill-typed resolved expression was accepted"
    assertTrue (Core.run 20 (Core.State.initial core) == .fault fault)
      "ill-typed primitive or condition produced the wrong Core fault"

/-- Structured lookup, all local constructors, exact execution, and semantic boundaries. -/
def resolvedLocalSemanticsTests : IO Unit := do
  testIdentityAndScope
  testLoweringAndExecution
  testRejections

end Tests
