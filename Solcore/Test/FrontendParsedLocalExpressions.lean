import Solcore.Syntax.Parser.Term
import Solcore.Frontend.LocalExpressionTyping
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Resolved.Eval
import Solcore.Core.Machine

/-! Executable source-text regressions through the existing canonical lexer,
expression parser, explicit-table frontend checker, and Core machine. This is
test wiring, not a new public source parser or external service endpoint. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def localId (index : Nat) : Resolved.LocalId :=
  ⟨⟨⟨.main, ⟨[⟨"Parsed", by decide⟩], by decide⟩⟩, 0⟩, index⟩
private def names : LocalNameTable :=
  [("c", localId 0), ("t", localId 1), ("e", localId 2), ("d", localId 3),
    ("n", localId 4), ("true", localId 5), ("false", localId 6)]
private def context : Resolved.Context :=
  [(localId 99, .unit), (localId 0, .bool), (localId 1, .word), (localId 2, .word),
    (localId 3, .bool), (localId 4, .word), (localId 5, .bool), (localId 6, .bool)]
private def word (value : Nat) : Core.Value := .word (Core.Word.ofNatModulo value)
private def environment (condition nestedCondition : Bool) : Resolved.Environment :=
  [(localId 99, .unit), (localId 0, .bool condition), (localId 1, word 11), (localId 2, word 22),
    (localId 3, .bool nestedCondition), (localId 4, word 0),
    (localId 5, .bool false), (localId 6, .bool true)]
private def store : Core.Store := [word 91, .bool false]

private def relabel (id : Resolved.LocalId) : Resolved.LocalId :=
  { id with binderIndex := id.binderIndex + 10 }
private theorem relabel_injective : Function.Injective relabel := by
  intro left right same
  cases left with
  | mk leftOwner leftIndex =>
      cases right with
      | mk rightOwner rightIndex =>
          have owners := congrArg Resolved.LocalId.owner same
          have indices := Nat.add_right_cancel (congrArg Resolved.LocalId.binderIndex same)
          cases owners; cases indices; rfl

private def parsedExpression (content : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-local.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  assertTrue lexed.diagnostics.isEmpty s!"{content}: unexpected lexical diagnostic"
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      assertTrue next.atEnd s!"{content}: unconsumed source tokens"
      assertTrue next.diagnostics.isEmpty s!"{content}: unexpected parse diagnostic"
      pure source
  | .reject failure _ => throw (IO.userError s!"{content}: rejected expression {reprStr failure}")
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def checkRun (content : String) (expectedCore : Core.Expr)
    (condition nestedCondition : Bool) (expectedValue : Core.Value) (required : Nat)
    (expectedType : Core.Ty := .word) : IO Unit := do
  let source ← parsedExpression content
  let checked := elaborateLocalExpression? names context source
  assertTrue (decide (checked = some (expectedCore, expectedType))) s!"{content}: wrong checked Core expression"
  let some (actualCore, _) := checked
    | throw (IO.userError s!"{content}: no checked expression")
  let initial := Core.State.initial actualCore
    (Resolved.LocalScope.values (environment condition nestedCondition)) store
  assertTrue (decide (Core.runStateful required initial = .done expectedValue store))
    s!"{content}: wrong value or store at sufficient fuel"
  assertTrue (decide (Core.runStateful (required + 5) initial = .done expectedValue store))
    s!"{content}: larger fuel changed result"
  assertTrue (match Core.runStateful (required - 1) initial with
    | .outOfFuel _ => true
    | _ => false) s!"{content}: expected exhaustion just below exact transition count"

private def checkUnsupported (content : String) : IO Unit := do
  let source ← parsedExpression content
  assertTrue (decide (resolveLocalExpression? names source = none))
    s!"{content}: unsupported or unmapped source unexpectedly resolved"
  assertTrue (decide (elaborateLocalExpression? names context source = none))
    s!"{content}: unsupported or unmapped source unexpectedly checked"

private def checkIllTyped (content : String) : IO Unit := do
  let source ← parsedExpression content
  assertTrue (resolveLocalExpression? names source).isSome s!"{content}: expected name resolution"
  assertTrue (decide (elaborateLocalExpression? names context source = none))
    s!"{content}: ill-typed expression unexpectedly checked"

private def bundledInputs (choice : Bool) : LocalInputs :=
  ((LocalInputs.empty.bindFresh (localId 0).owner "e" .word (word 22) .word).bindFresh
    (localId 0).owner "t" .word (word 11) .word).bindFresh
      (localId 0).owner "c" .bool (.bool choice) .bool

private def checkBundledRun : IO Unit := do
  let source ← parsedExpression "c ? t : e"
  let negatedSource ← parsedExpression "!c ? t : e"
  let conjunction ← parsedExpression "c && !c"
  let disjunction ← parsedExpression "c || !c"
  let complemented ← parsedExpression "~t"
  let literalCondition ← parsedExpression "c ? 7 : ~0xaF"
  let unsupported ← parsedExpression "c ? t : missing"
  for choice in [false, true] do
    let inputs := bundledInputs choice
    let expectedCore : Core.Expr := .ifE (.var 0) (.var 1) (.var 2)
    let expectedValue := if choice then word 11 else word 22
    assertTrue (decide (inputs.check? source = some (expectedCore, .word)))
      "bundled source check returned the wrong Core or type"
    assertTrue (decide (inputs.run? 4 source store = some (.word, .done expectedValue store)))
      "bundled source execution changed the checked type, selected value, or store"
    assertTrue (decide (inputs.run? 0 source store = some (.word,
      .outOfFuel (Core.State.initial expectedCore
        (Resolved.LocalScope.values inputs.environment) store))))
      "bundled source fuel exhaustion was lost or confused with failed checking"
    assertTrue (decide (inputs.run? 4 unsupported store = none))
      "bundled source execution skipped whole-expression checking"
    let extended := inputs.bindFresh (localId 0).owner "extra" .unit .unit .unit
    assertTrue (decide (extended.check? source = some (expectedCore.weakenAt 0, .word)))
      "adding an unused source name did not preserve the checked type and shift free positions"
    assertTrue (decide (extended.run? 4 source store = inputs.run? 4 source store))
      "adding an unused source name changed the completed conditional result"
    assertTrue (decide (inputs.run? 6 negatedSource store =
      some (.word, .done (if choice then word 22 else word 11) store)))
      "bundled source negation did not select the opposite branch"
    assertTrue (decide (extended.run? 6 negatedSource store = inputs.run? 6 negatedSource store))
      "unused input insertion changed a parsed negated condition"
    assertTrue (decide (inputs.run? (if choice then 6 else 4) conjunction store =
      some (.bool, .done (.bool false) store))) "bundled conjunction did not short-circuit correctly"
    assertTrue (decide (inputs.run? (if choice then 4 else 6) disjunction store =
      some (.bool, .done (.bool true) store))) "bundled disjunction did not short-circuit correctly"
    assertTrue (decide (inputs.run? 3 complemented store =
      some (.word, .done (.word (Core.Word.ofNatModulo 11).bitNot) store)))
      "bundled Word complement did not preserve the Word-only result"
    assertTrue (decide (extended.run? 6 conjunction store = inputs.run? 6 conjunction store ∧
      extended.run? 6 disjunction store = inputs.run? 6 disjunction store))
      "unused input insertion changed parsed short-circuit execution"
    let literalValue := if choice then word 7 else .word (Core.Word.ofNatModulo 175).bitNot
    let literalFuel := if choice then 4 else 6
    assertTrue (decide (inputs.run? literalFuel literalCondition store =
      some (.word, .done literalValue store) ∧
      extended.run? literalFuel literalCondition store = inputs.run? literalFuel literalCondition store))
      "parsed literal branches changed under unused input insertion"
    let renamed := extended.mapIds relabel relabel_injective
    for checkedSource in [source, negatedSource, conjunction, disjunction, complemented,
        literalCondition, unsupported] do
      assertTrue (decide (renamed.check? checkedSource = extended.check? checkedSource))
        "identity relabeling changed parsed checked Core or type"
      for fuel in [0, 2, 4, 6] do
        assertTrue (decide (renamed.run? fuel checkedSource store = extended.run? fuel checkedSource store))
          "identity relabeling changed a parsed result or exact suspended state"

private def checkShortCircuitRuns : IO Unit := do
  let conjunction : Core.Expr := .ifE (.var 1) (.var 4) (.bool false)
  let disjunction : Core.Expr := .ifE (.var 1) (.bool true) (.var 4)
  for choice in [false, true] do
    for rightChoice in [false, true] do
      checkRun "c && d" conjunction choice rightChoice (.bool (choice && rightChoice)) 4 .bool
      checkRun "c || d" disjunction choice rightChoice (.bool (choice || rightChoice)) 4 .bool
      checkRun "c && !d ? t : e"
        (.ifE (.ifE (.var 1) (.unary .boolNot (.var 4)) (.bool false)) (.var 2) (.var 3))
        choice rightChoice (if choice && !rightChoice then word 11 else word 22)
        (if choice then 9 else 7)
      checkRun "c || !d ? t : e"
        (.ifE (.ifE (.var 1) (.bool true) (.unary .boolNot (.var 4))) (.var 2) (.var 3))
        choice rightChoice (if choice || !rightChoice then word 11 else word 22)
        (if choice then 7 else 9)
  let precedence : Core.Expr := .ifE
    (.ifE (.var 1) (.bool true) (.ifE (.var 4) (.unary .boolNot (.var 6)) (.bool false)))
    (.var 2) (.var 3)
  checkRun "c || d && !true ? t : e" precedence true false (word 11) 7
  checkRun "c || d && !true ? t : e" precedence false true (word 11) 12
  checkRun "c || d && !true ? t : e" precedence false false (word 22) 10
  checkRun "(c || d) && !false ? t : e"
    (.ifE (.ifE disjunction (.unary .boolNot (.var 7)) (.bool false)) (.var 2) (.var 3))
    true false (word 22) 12
  let nested : Core.Expr := .ifE
    (.ifE (.var 1) (.ifE (.var 4) (.unary .boolNot (.var 1)) (.var 1)) (.bool false))
    (.var 2) (.var 3)
  checkRun "c && (d ? !c : c) ? t : e" nested false true (word 22) 7
  checkRun "c && (d ? !c : c) ? t : e" nested true true (word 22) 12
  checkRun "c && (d ? !c : c) ? t : e" nested true false (word 11) 10
  checkUnsupported "c && missing"
  checkIllTyped "c || 7"
  checkUnsupported "c || \"7\""
  checkIllTyped "c & d"
  checkIllTyped "c | d"
  checkIllTyped "c ^ d"
  checkIllTyped "c && n"
  checkIllTyped "n || c"

private def checkWordComplementRuns : IO Unit := do
  checkRun "~n" (.unary .wordNot (.var 5)) false false (.word Core.Word.maximum) 3
  checkRun "~~n" (.unary .wordNot (.unary .wordNot (.var 5))) true true (word 0) 5
  checkRun "~((t))" (.unary .wordNot (.var 2)) false false
    (.word (Core.Word.ofNatModulo 11).bitNot) 3
  for choice in [false, true] do
    checkRun "~(c ? t : e)" (.unary .wordNot (.ifE (.var 1) (.var 2) (.var 3)))
      choice false (.word (Core.Word.ofNatModulo (if choice then 11 else 22)).bitNot) 6
    checkRun "c ? t : ~e" (.ifE (.var 1) (.var 2) (.unary .wordNot (.var 3)))
      choice true (if choice then word 11 else .word (Core.Word.ofNatModulo 22).bitNot)
      (if choice then 4 else 6)
  checkUnsupported "~missing"
  checkRun "~7" (.unary .wordNot (.word (Core.Word.ofNatModulo 7)))
    false false (.word (Core.Word.ofNatModulo 7).bitNot) 3
  checkRun "~~((0007))" (.unary .wordNot (.unary .wordNot (.word (Core.Word.ofNatModulo 7))))
    false false (word 7) 5
  checkUnsupported "~\"7\""
  checkIllTyped "!7"
  checkIllTyped "!~n"
  checkIllTyped "~(!c)"
  checkIllTyped "(~n) ? t : e"

def frontendParsedLocalExpressionTests : IO Unit := do
  let simple : Core.Expr := .ifE (.var 1) (.var 2) (.var 3)
  checkRun "c ? t : e" simple true false (word 11) 4
  checkRun "c ? t : e" simple false true (word 22) 4
  checkRun "(c) ? ((t)) : e" simple true false (word 11) 4
  checkRun " /* before */ c ? /* branch */ t : e " simple false false (word 22) 4
  let rightNested : Core.Expr := .ifE (.var 1) (.var 2) (.ifE (.var 4) (.var 3) (.var 5))
  checkRun "c ? t : d ? e : n" rightNested true false (word 11) 4
  checkRun "c ? t : d ? e : n" rightNested false true (word 22) 7
  checkRun "c ? t : d ? e : n" rightNested false false (word 0) 7
  checkRun "c ? d ? t : e : n"
    (.ifE (.var 1) (.ifE (.var 4) (.var 2) (.var 3)) (.var 5)) true false (word 22) 7
  checkRun "(c ? d : false) ? t : e"
    (.ifE (.ifE (.var 1) (.var 4) (.var 7)) (.var 2) (.var 3)) false false (word 11) 7
  checkRun "true ? t : e" (.ifE (.var 6) (.var 2) (.var 3)) true true (word 22) 4
  checkRun "false ? t : e" (.ifE (.var 7) (.var 2) (.var 3)) false false (word 11) 4
  let negatedCondition : Core.Expr := .ifE (.unary .boolNot (.var 1)) (.var 2) (.var 3)
  checkRun "!c ? t : e" negatedCondition false false (word 11) 6
  checkRun "(!c) ? t : e" negatedCondition true true (word 22) 6
  checkRun "!!c ? t : e"
    (.ifE (.unary .boolNot (.unary .boolNot (.var 1))) (.var 2) (.var 3)) true false (word 11) 8
  checkRun "c ? t : (!d ? e : n)"
    (.ifE (.var 1) (.var 2) (.ifE (.unary .boolNot (.var 4)) (.var 3) (.var 5)))
    false false (word 22) 9
  checkRun "!true ? t : e"
    (.ifE (.unary .boolNot (.var 6)) (.var 2) (.var 3)) true true (word 11) 6
  checkRun "!false ? t : e"
    (.ifE (.unary .boolNot (.var 7)) (.var 2) (.var 3)) false false (word 22) 6
  checkUnsupported "c ? t : missing"
  for choice in [false, true] do
    checkRun "c ? t : 7" (.ifE (.var 1) (.var 2) (.word (Core.Word.ofNatModulo 7)))
      choice false (if choice then word 11 else word 7) 4
    checkRun "c ? 7 : 0xaF"
      (.ifE (.var 1) (.word (Core.Word.ofNatModulo 7)) (.word (Core.Word.ofNatModulo 175)))
      choice true (if choice then word 7 else word 175) 4
  checkUnsupported "c ? t : \"7\""
  checkIllTyped "7 ? t : e"
  checkIllTyped "c ? 7 : d"
  checkRun "t + e" (.binary .wordAdd (.var 2) (.var 3)) false false (word 33) 5
  checkRun "t - e" (.binary .wordSub (.var 2) (.var 3)) false false
    (.word ((Core.Word.ofNatModulo 11).sub (Core.Word.ofNatModulo 22))) 5
  checkRun "t * e" (.binary .wordMul (.var 2) (.var 3)) false false (word 242) 5
  checkUnsupported "t(e)"
  checkIllTyped "~c"
  checkIllTyped "n ? t : e"
  checkIllTyped "c ? t : d"
  checkIllTyped "c ? t : (d ? e : c)"
  checkIllTyped "(!n) ? t : e"
  let rejectsTrailingTokens ← try
    let _ ← parsedExpression "t e"
    pure false
  catch error => pure (error.toString == "t e: unconsumed source tokens")
  assertTrue rejectsTrailingTokens "source-text test helper accepted an incomplete expression parse"
  checkBundledRun
  checkShortCircuitRuns
  checkWordComplementRuns

end Tests
