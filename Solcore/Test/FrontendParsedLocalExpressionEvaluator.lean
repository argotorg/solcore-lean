import Solcore.Syntax.Parser.Term
import Solcore.Frontend.LocalExpressionEvaluatorExecutionProperties

/-! Original parsed expressions, independently specified values/Core/costs, and
actual first-match inputs. Raw selected success is not whole-source acceptance. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"DirectEvaluator", by decide⟩], by decide⟩⟩, 17⟩
private def other : Resolved.DeclarationId := { owner with declarationIndex := 71 }
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def w (n : Nat) : Core.Value := .word (word n)
private def literal (n : Nat) : Core.Expr := .word (word n)
private def stores : List Core.Store := [[], [.cellRef .word 40, .bool true, w 91]]
private def inputs (l r : Nat) (c d : Bool) : LocalInputs := ⟨[
  ⟨"c", ⟨owner, 2⟩, .bool, .bool c, .bool⟩, ⟨"d", ⟨other, 5⟩, .bool, .bool d, .bool⟩,
  ⟨"r", ⟨other, 999⟩, .word, w r, .word⟩, ⟨"l", ⟨owner, 7⟩, .word, w l, .word⟩], by
    change ([⟨owner, 2⟩, ⟨other, 5⟩, ⟨other, 999⟩, ⟨owner, 7⟩] : List Resolved.LocalId).Nodup
    decide⟩
private def parsed? (content : String) : IO (Option Syntax.Expr) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "direct-evaluator.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"lexer invariant: {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      assertTrue (decide (source.span.source = file.id ∧ source.span.startByte < source.span.endByte ∧
        source.span.endByte ≤ content.utf8ByteSize)) "parsed source range changed"
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"parser invariant: {reprStr error}")
private def parsed (content : String) : IO Syntax.Expr := do
  let some source ← parsed? content | throw (IO.userError s!"incomplete expression: {content}")
  return source

private def raw (table : LocalNameTable) (environment : Resolved.Environment)
    (source : Syntax.Expr) (expected : Option (Core.Value × Nat)) : IO Unit := do
  assertTrue (decide (evaluateLocalExpressionWithCost? table environment source = expected))
    s!"independent raw value/cost disagreed: {reprStr source.value}"
  for store in stores do
    match evaluated : evaluateLocalExpressionWithCost? table environment source with
    | none => have _ := (evaluateLocalExpressionWithCost?_eq_none_iff store).mp evaluated; pure ()
    | some (_, cost) =>
        let evidence := evaluateLocalExpressionWithCost?_sound evaluated store
        have _ := evaluateLocalExpressionWithCost?_complete evidence
        have _ := (evaluateLocalExpressionWithCost?_iff store).mpr evidence
        have _ := localExpressionEvaluatesWithCost_iff_evaluate.mp evidence
        have _ := (evaluateLocalExpressionWithCost?_exists_cost_iff store).mp ⟨cost, evaluated⟩
        have _ := (evaluateLocalExpressionWithCost?_value_iff store).mpr evidence.erase
        pure ()

private def checked (content : String) (actual : LocalInputs) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost : Nat) : IO Unit := do
  let source ← parsed content
  raw actual.names actual.environment source (some (value, cost))
  assertTrue (decide (actual.check? source = some (core, type) ∧
    Core.infer? actual.context.values core = some type)) s!"wrong independent Core/type: {content}"
  match accepted : actual.check? source, evaluated : evaluateLocalExpressionWithCost? actual.names actual.environment source with
  | some (checkedCore, checkedType), some (found, steps) =>
      let typing := LocalInputs.check?_iff_hasType.mp ⟨checkedCore, accepted⟩
      have _ := elaborateLocalExpression?_typed_evaluator_exists accepted actual.sameIds actual.environmentTyped
      for store in stores do
        have _ := actual.typed_evaluator_execution typing store
        for continuation in [[], [.letBody (.var 0) []], [.unaryApply .wordNot]] do
          have _ := evaluateLocalExpressionWithCost?_checked_toStepsWithContinuation
            (store := store) evaluated accepted actual.sameIds continuation
          pure () -- An endpoint before the continuation runs is not a whole-run guarantee.
        for fuel in List.range (cost + 3) do
          have _ := evaluateLocalExpressionWithCost?_checked_runStateful_done_iff
            (fuel := fuel) (store := store) evaluated accepted actual.sameIds
          have _ := evaluateLocalExpressionWithCost?_checked_runStateful_outOfFuel_iff
            (fuel := fuel) (store := store) evaluated accepted actual.sameIds
          have _ := elaborateLocalExpression?_run_done_iff_evaluator (value := found)
            (fuel := fuel) (initialStore := store) (finalStore := store) accepted actual.sameIds
          have _ := LocalInputs.run?_done_iff_evaluator (inputs := actual) (source := source)
            (type := checkedType) (value := found) (fuel := fuel) (initialStore := store) (finalStore := store)
          have _ := LocalInputs.run?_outOfFuel_iff_evaluator (inputs := actual) (source := source)
            (type := checkedType) (fuel := fuel) (store := store)
          assertTrue (decide (actual.run? fuel source store =
            some (type, Core.runStateful fuel (Core.State.initial core actual.environment.values store))))
            "full actual-Core result changed"
          assertTrue (match actual.run? fuel source store with
            | some (t, .done v s) => decide (cost ≤ fuel ∧ t = type ∧ v = value ∧ s = store)
            | some (t, .outOfFuel checkpoint) => decide (fuel < cost ∧ t = type ∧ checkpoint.store = store)
            | _ => false) "wrong independent threshold/value/own store"
        for spent in List.range cost do
          let some (_, .outOfFuel checkpoint) := actual.run? spent source store
            | throw (IO.userError "genuine checkpoint missing")
          assertTrue (decide (Core.runStateful (cost - spent) checkpoint = .done value store))
            "actual checkpoint did not finish at the independently specified remainder"
        match core with
        | .binary op (.var left) (.var right) =>
            let some l := actual.environment.values[left]? | throw (IO.userError "left fixture value missing")
            let some r := actual.environment.values[right]? | throw (IO.userError "right fixture value missing")
            assertTrue (decide (actual.run? 2 source store = some (type, .outOfFuel
              ⟨.ret l, [.binaryRight op (.var right) actual.environment.values], store⟩) ∧
              actual.run? 4 source store = some (type, .outOfFuel ⟨.ret r, [.binaryApply op l], store⟩)))
              "strict original left/right checkpoints changed"
        | _ => pure ()
      assertTrue (steps == cost) "proof-derived cost replaced the independent expected cost"
  | _, _ => throw (IO.userError "positive raw or whole evidence disappeared")

private def contrast (content : String) (actual : LocalInputs) (expected : Option (Core.Value × Nat)) : IO Unit := do
  let source ← parsed content
  raw actual.names actual.environment source expected
  assertTrue (actual.check? source).isNone s!"raw success bypassed whole checking: {content}"
  for store in stores do
    for fuel in [0, 1, 30] do
      assertTrue (actual.run? fuel source store).isNone "whole rejection exposed execution"

private def checkOpaque (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) : IO Unit := do
  for c in [false, true] do
    let actual := (LocalInputs.empty.bindFresh owner "x" type value typed).bindFresh other "c" .bool (.bool c) .bool
    checked "x" actual (.var 1) type value 1
    checked "c ? x : x" actual (.ifE (.var 0) (.var 1) (.var 1)) type value 4
    contrast "c && x" actual (some (if c then value else .bool false, 4))
    contrast "c || x" actual (some (if c then .bool true else value, 4))
    for store in stores do
      let continuation : List Core.Frame := [.unaryApply .wordNot]
      assertTrue (match Core.runStateful 1 ⟨.eval (.var 1) actual.environment.values, continuation, store⟩ with
        | .fault _ checkpoint => decide (checkpoint = ⟨.ret value, continuation, store⟩)
        | _ => false) "retained Word continuation was incorrectly guaranteed to exhaust for opaque values"

private def operators (l r : Nat) : List (String × Syntax.BinaryOp × Core.Expr × Core.Ty × Core.Value × Nat) :=
  let a : Core.Expr := .var 3
  let b : Core.Expr := .var 2
  let lt : Core.Expr := .letE a (.letE (.var 3) (.binary .wordGt (.var 0) (.var 1)))
  [("+", .add, .binary .wordAdd a b, .word, w (l + r), 3),
   ("-", .subtract, .binary .wordSub a b, .word, w (l + Core.wordModulus - r), 3),
   ("*", .multiply, .binary .wordMul a b, .word, w (l * r), 3),
   ("/", .divide, .binary .wordDiv a b, .word, w (if r == 0 then 0 else l / r), 3),
   ("%", .modulo, .binary .wordMod a b, .word, w (if r == 0 then 0 else l % r), 3),
   ("&", .bitAnd, .binary .wordAnd a b, .word, w (l &&& r), 3),
   ("|", .bitOr, .binary .wordOr a b, .word, w (l ||| r), 3),
   ("^", .bitXor, .binary .wordXor a b, .word, w (l ^^^ r), 3),
   (">", .greater, .binary .wordGt a b, .bool, .bool (decide (l > r)), 3),
   ("<", .less, lt, .bool, .bool (decide (l < r)), 9),
   ("==", .equal, .binary .wordEq a b, .bool, .bool (l == r), 3),
   ("!=", .notEqual, .unary .boolNot (.binary .wordEq a b), .bool, .bool (l != r), 5),
   ("<=", .lessEqual, .unary .boolNot (.binary .wordGt a b), .bool, .bool (decide (l ≤ r)), 5),
   (">=", .greaterEqual, .unary .boolNot lt, .bool, .bool (decide (l ≥ r)), 11)]

def frontendParsedLocalExpressionEvaluatorTests : IO Unit := do
  let numbers := [0, 1, 3, 7, 2 ^ 255, Core.wordModulus - 1]
  for l in numbers do
    for r in numbers do
      for (symbol, op, core, type, value, overhead) in operators l r do
        let content := s!"l {symbol} r"
        let source ← parsed content
        assertTrue (match source.value with
          | .binary ⟨_, .identifier left⟩ ⟨span, actualOp⟩ ⟨_, .identifier right⟩ =>
              actualOp == op && left.value == "l" && right.value == "r" &&
                decide (left.span.endByte ≤ span.startByte ∧ span.endByte ≤ right.span.startByte)
          | _ => false) "original operand order/operator range changed"
        assertTrue (decide (evaluateLocalWordBinaryWithCost? op (word l) (word r) = some (value, overhead)))
          "strict operator helper changed result/overhead"
        checked content (inputs l r true false) core type value (overhead + 2)
    checked "~l" (inputs l 0 true false) (.unary .wordNot (.var 3)) .word (w (Core.wordModulus - 1 - l)) 3
  for c in [false, true] do
    for d in [false, true] do
      let actual := inputs 7 3 c d
      checked "!c" actual (.unary .boolNot (.var 0)) .bool (.bool (!c)) 3
      checked "c && !d" actual (.ifE (.var 0) (.unary .boolNot (.var 1)) (.bool false))
        .bool (.bool (c && !d)) (if c then 6 else 4)
      checked "c || !d" actual (.ifE (.var 0) (.bool true) (.unary .boolNot (.var 1)))
        .bool (.bool (c || !d)) (if c then 4 else 6)
      checked "(c ? (l - r) : r)" actual (.ifE (.var 0) (.binary .wordSub (.var 3) (.var 2)) (.var 2))
        .word (w (if c then 4 else 3)) (if c then 8 else 4)
      contrast "c && missing" actual (if c then none else some (.bool false, 4))
      contrast "c || missing" actual (if c then some (.bool true, 4) else none)
      contrast "c ? l : missing" actual (if c then some (w 7, 4) else none)
      contrast "c ? f(l) : r" actual (if c then none else some (w 3, 4))
    for depth in [0, 1, 3, 7] do
      let content := (List.range depth).foldl (fun inner _ => "c ? (" ++ inner ++ ") : r") "l - r"
      let core := (List.range depth).foldl (fun inner _ => Core.Expr.ifE (.var 0) inner (.var 2))
        (.binary .wordSub (.var 3) (.var 2))
      checked content (inputs 7 3 c false) core .word (w (if c || depth == 0 then 4 else 3))
        (if c || depth == 0 then 5 + 3 * depth else 4)
  let actual := inputs 7 3 true false
  for (symbol, op) in [("/", Core.BinaryOp.wordDiv), ("%", .wordMod)] do
    checked s!"~l {symbol} 0" actual (.binary op (.unary .wordNot (.var 3)) (literal 0)) .word (w 0) 7
    checked s!"l {symbol} (r - r)" actual (.binary op (.var 3) (.binary .wordSub (.var 2) (.var 2))) .word (w 0) 9
    contrast s!"missing {symbol} 0" actual none
    contrast s!"0 {symbol} missing" actual none
    contrast s!"0 {symbol} c" actual none
    contrast s!"l {symbol} (c ? 0 : missing)" actual (some (w 0, 8))
  for content in ["!l", "~c", "l + c", "c - r", "l && missing", "missing", "f(l)", "l.x", "l[0]", "[l]", "(l,r)", "\"7\""] do
    contrast content actual none
  for op in [Syntax.BinaryOp.logicalAnd, .logicalOr] do
    assertTrue (evaluateLocalWordBinaryWithCost? op (word 1) (word 0)).isNone "short circuit acquired strict Word meaning"
  for (content, n) in [("0", 0), (" /*a*/ ((0007)) /*b*/ ", 7), ("0xaBcD", 43981),
      (toString (Core.wordModulus - 1), Core.wordModulus - 1)] do
    checked content LocalInputs.empty (literal n) .word (w n) 1
  for content in [toString Core.wordModulus, "0x1" ++ String.ofList (List.replicate 64 '0')] do
    contrast content LocalInputs.empty none
  checkOpaque (.cell .word) (.cellRef .word 999) .cellRef
  checkOpaque (.function .word .word) (.closure .word .word (.var 0) []) (.closure .nil (.var rfl))
  for value in [Core.Value.cellRef .word 999, .closure .word .bool (.var 999) [w 12],
      .constructed ⟨⟨81⟩, 4⟩ (.pair .unit (w 8)), .unit] do
    let table : LocalNameTable := [("x", ⟨owner, 7⟩), ("c", ⟨other, 999⟩)]
    for c in [false, true] do
      let environment : Resolved.Environment := [(⟨owner, 7⟩, value), (⟨other, 999⟩, .bool c)]
      for content in ["x", "((x))"] do raw table environment (← parsed content) (some (value, 1))
      raw table environment (← parsed "c ? x : x") (some (value, 4))
      raw table environment (← parsed "c && x") (some (if c then value else .bool false, 4))
      raw table environment (← parsed "c || x") (some (if c then .bool true else value, 4))
      let context : Resolved.Context := [(⟨owner, 7⟩, .cell .word), (⟨other, 999⟩, .bool)]
      assertTrue ((elaborateLocalExpression? table context (← parsed "c && x")).isNone &&
        (elaborateLocalExpression? table context (← parsed "c || x")).isNone) "raw forwarded value became a Bool typing rule"
  let id : Resolved.LocalId := ⟨owner, 7⟩
  let second : Resolved.LocalId := ⟨other, 999⟩
  let source ← parsed "x"
  let table : LocalNameTable := [("x", id), ("x", second)]
  raw table [(id, w 9), (id, w 2), (second, w 5)] source (some (w 9, 1))
  raw table [(id, w 2), (id, w 9), (second, w 5)] source (some (w 2, 1))
  raw table [(id, .bool true), (id, w 9)] (← parsed "x - x") none
  raw table [(second, w 5)] source none
  raw [("x", second), ("x", id)] [(id, w 9)] source none
  let unaligned : Resolved.Environment := [(second, w 2), (id, w 9)]
  raw table unaligned source (some (w 9, 1))
  assertTrue (decide (elaborateLocalExpression? table [(id, .word), (second, .word)] source = some (.var 0, .word) ∧
    unaligned.ids ≠ [id, second] ∧ Core.runStateful 1 (Core.State.initial (.var 0) unaligned.values []) = .done (w 2) []))
    "unaligned raw lookup was incorrectly replaced by positional Core execution"
  let span : Syntax.SourceSpan := ⟨⟨.main, "not-lexed.sol"⟩, 900, 2⟩
  let manual := fun payload => (⟨span, .literal ⟨⟨⟨.main, "other.sol"⟩, 33, 1⟩, payload⟩⟩ : Syntax.Expr)
  raw [] [] (manual (.decimal "0007")) (some (w 7, 1))
  for payload in [Syntax.CoreLiteralValue.decimal "", .decimal "-1", .decimal "1_0", .decimal "٤",
      .hexadecimal "0x", .hexadecimal "0X1", .hexadecimal "0xg", .string "7", .decimal (toString Core.wordModulus)] do
    raw [] [] (manual payload) none
  for content in ["", "l +", "c ? l", "c ? l :", "7 8", "0x", "0Xff", "1_000", "0x1g", "-1", "٤"] do
    assertTrue (← parsed? content).isNone s!"malformed complete source parsed: {content}"

end Tests
