import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunction
import Solcore.Frontend.ReturnBody

/-! Parsed unsigned Word less-than-or-equal retains ordered greater-than beneath
a negation frame. Five and six transitions are genuine, distinct checkpoints. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedLessEqual", by decide⟩], by decide⟩⟩, 24⟩
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def literal (value : Nat) : Core.Expr := .word (word value)
private def le (left right : Core.Expr) : Core.Expr := .unary .boolNot (.binary .wordGt left right)
private def store : Core.Store := [.word (word 91), .bool false]
private def types : TypeNameTable :=
  [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit), (["Cell"], .cell .word),
    (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩)]
private def inputs (choice : Bool) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner "l" .word (.word (word 7)) .word).bindFresh
    owner "r" .word (.word (word 9)) .word).bindFresh owner "c" .bool (.bool choice) .bool

private def parsed? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) :
    IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-lessEqual.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match parser (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def expression (content : String) : IO Syntax.Expr := do
  let some source ← parsed? Syntax.Parser.expression content
    | throw (IO.userError s!"{content}: expected a complete diagnostic-free expression")
  return source

private def checkRun (supplied : LocalInputs) (content : String) (expectedCore : Core.Expr)
    (expectedType : Core.Ty) (expected : Core.Value) (cost : Nat) : IO Unit := do
  let source ← expression content
  assertTrue (decide (supplied.check? source = some (expectedCore, expectedType))) "wrong exact nested Core/type"
  assertTrue (decide (cost ≤ localExpressionFuelBound source)) "source budget was insufficient"
  let initial := Core.State.initial expectedCore supplied.environment.values store
  for fuel in List.range (cost + 3) do
    let observed := supplied.run? fuel source store
    assertTrue (decide (observed = some (expectedType, Core.runStateful fuel initial)))
      s!"{content}: full checked machine result changed"
    assertTrue (match observed with
      | some (type, .done value finalStore) =>
          decide (cost ≤ fuel ∧ type = expectedType ∧ value = expected ∧ finalStore = store)
      | some (type, .outOfFuel suspended) => decide (fuel < cost ∧ type = expectedType ∧ suspended.store = store)
      | _ => false) s!"{content}: wrong value, store, or exact cost"

private def checkPending (run : Nat → Option (Core.Ty × Core.StatefulRunResult))
    (left right : Core.Word) : IO Unit := do
  let five : Core.State := ⟨.ret (.word right),
    [.binaryApply .wordGt (.word left), .unaryApply .boolNot], store⟩
  let six : Core.State := ⟨.ret (.bool (decide (left > right))), [.unaryApply .boolNot], store⟩
  let expected := Core.Value.bool (!(decide (left > right)))
  let some (.bool, .outOfFuel actualFive) := run 5
    | throw (IO.userError "lessEqual lost the genuine five-fuel checkpoint")
  let some (.bool, .outOfFuel actualSix) := run 6
    | throw (IO.userError "lessEqual lost the genuine six-fuel checkpoint")
  assertTrue (decide (actualFive = five ∧ actualSix = six ∧ five ≠ six))
    "ordered greater-than and negation checkpoints changed"
  assertTrue (decide (Core.runStateful 0 actualFive = .outOfFuel five ∧
    Core.runStateful 1 actualFive = .outOfFuel six ∧ Core.runStateful 0 actualSix = .outOfFuel six ∧
    Core.runStateful 2 actualFive = .done expected store ∧ Core.runStateful 1 actualSix = .done expected store ∧
    run 7 = some (.bool, .done expected store))) "remaining two/one transitions changed"
  for remaining in List.range 5 do
    assertTrue (decide (run (5 + remaining) = some (.bool, Core.runStateful remaining actualFive) ∧
      run (6 + remaining) = some (.bool, Core.runStateful remaining actualSix)))
      "genuine checkpoint resumption changed the full result"

private def checkLeaf (content : String) (left right : Core.Expr)
    (leftWord rightWord : Core.Word) : IO Unit := do
  let supplied := inputs true
  checkRun supplied content (le left right) .bool (.bool (!(decide (leftWord > rightWord)))) 7
  let source ← expression content
  assertTrue (localExpressionFuelBound source == 7) "leaf lessEqual source budget changed"
  checkPending (fun fuel => supplied.run? fuel source store) leftWord rightWord

private def checkRejected (supplied : LocalInputs) (content : String) (resolves : Bool) : IO Unit := do
  let source ← expression content
  assertTrue ((resolveLocalExpression? supplied.names source).isSome == resolves) "wrong resolution boundary"
  assertTrue (supplied.check? source).isNone s!"{content}: invalid lessEqual checked"
  for fuel in [0, 5, 6, 7, 30] do
    assertTrue (supplied.run? fuel source store).isNone "whole checking was bypassed"
  let text := "function rejected(l: Word, r: Word, c: Bool) returns (Bool) { return " ++ content ++ "; }"
  let some declaration ← parsed? (Syntax.Parser.functionDecl .module) text
    | throw (IO.userError "wrapped rejection declaration did not parse")
  assertTrue (compileRuntimeFunction? types owner declaration).isNone "invalid whole body compiled"
  for choice in [false, true] do
    let arguments : List TypedRuntimeArgument :=
      [⟨.word, .word (word 7), .word⟩, ⟨.word, .word (word 9), .word⟩, ⟨.bool, .bool choice, .bool⟩]
    assertTrue (prepareRuntimeFunction? types owner declaration arguments).isNone "invalid whole entry prepared"
    for fuel in [0, 7, 30] do
      assertTrue (runRuntimeFunction? types owner declaration arguments fuel store).isNone
        "a skipped invalid branch bypassed whole entry rejection"

private def checkParameterPositions : IO Unit := do
  for arity in [2, 3, 4] do
    let indices := List.range arity
    let parameters := String.intercalate ", " (indices.map fun index => s!"p{index}: Word")
    for left in indices do
      for right in indices do
        let content := s!"function lessEqual_{arity}_{left}_{right}({parameters}) returns (Bool)"
          ++ " { return " ++ s!"p{left} <= p{right};" ++ " }"
        let some declaration ← parsed? (Syntax.Parser.functionDecl .module) content
          | throw (IO.userError "ordered parameter declaration did not parse")
        assertTrue (match declaration.value.body.value with
          | [⟨_, .returnStmt (some ⟨_, .binary ⟨_, .identifier l⟩ ⟨_, .lessEqual⟩ ⟨_, .identifier r⟩⟩)⟩] =>
              l.value == s!"p{left}" && r.value == s!"p{right}"
          | _ => false) "canonical lessEqual or ordered references changed"
        assertTrue (returnBodyFuelBound declaration.value.body == 7) "parsed lessEqual body budget changed"
        let some compiled := compileRuntimeFunction? types owner declaration
          | throw (IO.userError "ordered parameter declaration did not compile")
        assertTrue (decide (compiled.core = le (.var (arity - 1 - left)) (.var (arity - 1 - right)) ∧
          compiled.returnType = .bool ∧ compiled.inputs.context.values = List.replicate arity Core.Ty.word))
          "wrong exact nested Core, Bool result, or parameter context"
        assertTrue (decide (compiled.inputs.names = (indices.map fun index =>
          (s!"p{index}", (⟨owner, index⟩ : Resolved.LocalId))).reverse)) "wrong ordered source IDs/names"
        let arguments : List TypedRuntimeArgument := indices.map fun index =>
          ⟨.word, .word (word (10 * index + 1)), .word⟩
        let some prepared := prepareRuntimeFunction? types owner declaration arguments
          | throw (IO.userError "matching actual arguments failed preparation")
        let values := arguments.reverse.map (·.value)
        assertTrue (decide (prepared.inputs.environment.values = values ∧ prepared.core = compiled.core ∧
          prepared.returnType = .bool ∧ prepared.inputs.context = compiled.inputs.context))
          "preparation changed ordered actual values or the compiled projection"
        let initial := Core.State.initial compiled.core values store
        let run := fun fuel => runRuntimeFunction? types owner declaration arguments fuel store
        for fuel in List.range 11 do
          assertTrue (decide (run fuel = some (.bool, Core.runStateful fuel initial)))
            "same-fuel full compiled result differs"
        checkPending run (word (10 * left + 1)) (word (10 * right + 1))

private def checkArithmeticEntry : IO Unit := do
  let some declaration ← parsed? (Syntax.Parser.functionDecl .module)
    "function guard(l: Word, r: Word) returns (Word) { return l * r <= r ? l - r : l; }"
    | throw (IO.userError "arithmetic lessEqual entry did not parse")
  let some compiled := compileRuntimeFunction? types owner declaration
    | throw (IO.userError "arithmetic lessEqual entry did not compile")
  assertTrue (decide (compiled.core = .ifE (le (.binary .wordMul (.var 1) (.var 0)) (.var 0))
    (.binary .wordSub (.var 1) (.var 0)) (.var 1) ∧ compiled.returnType = .word))
    "arithmetic lessEqual changed exact compiled Core or type"
  assertTrue (returnBodyFuelBound declaration.value.body == 18) "arithmetic guard source bound changed"
  for left in [0, 1, 7, Core.Word.maximum.val] do
    for right in [0, 1, 9] do
      let arguments : List TypedRuntimeArgument :=
        [⟨.word, .word (word left), .word⟩, ⟨.word, .word (word right), .word⟩]
      let selected := !(decide ((word left).mul (word right) > word right))
      let expected := Core.Value.word (if selected then (word left).sub (word right) else word left)
      let cost := if selected then 18 else 14
      let initial := Core.State.initial compiled.core (arguments.reverse.map (·.value)) store
      for fuel in List.range 21 do
        let observed := runRuntimeFunction? types owner declaration arguments fuel store
        assertTrue (decide (observed = some (.word, Core.runStateful fuel initial))) "compiled guard execution changed"
        assertTrue (match observed with
          | some (.word, .done value finalStore) => decide (cost ≤ fuel ∧ value = expected ∧ finalStore = store)
          | some (.word, .outOfFuel suspended) => decide (fuel < cost ∧ suspended.store = store)
          | _ => false) "arithmetic lessEqual changed the exact 14/18 path cost or result"

private def checkReturnContract : IO Unit := do
  let some declaration ← parsed? (Syntax.Parser.functionDecl .module)
    "function wrong(l: Word, r: Word) returns (Word) { return l <= r; }"
    | throw (IO.userError "wrong return contract did not parse")
  let arguments : List TypedRuntimeArgument := [⟨.word, .word (word 7), .word⟩, ⟨.word, .word (word 9), .word⟩]
  let some bound := bindRuntimeParameters? types owner declaration.value.signature.parameters.elements arguments
    | throw (IO.userError "wrong return contract parameters did not bind")
  assertTrue (decide (bound.checkReturnBody? declaration.value.body = some (le (.var 1) (.var 0), .bool)))
    "body-only checker lost Bool lessEqual"
  assertTrue (compileRuntimeFunction? types owner declaration).isNone "Bool lessEqual compiled with Word return"
  assertTrue (prepareRuntimeFunction? types owner declaration arguments).isNone "Bool lessEqual prepared with Word return"
  for fuel in [0, 7, 30] do
    assertTrue (runRuntimeFunction? types owner declaration arguments fuel store).isNone "return contract bypassed"

def frontendParsedWordLessEqualTests : IO Unit := do
  let supplied := inputs true
  checkLeaf "l <= r" (.var 2) (.var 1) (word 7) (word 9)
  checkLeaf "r <= l" (.var 1) (.var 2) (word 9) (word 7)
  checkLeaf "l <= l" (.var 2) (.var 2) (word 7) (word 7)
  for left in [0, 1, 2 ^ 255, Core.Word.maximum.val] do
    for right in [0, 1, 2 ^ 255, Core.Word.maximum.val] do
      checkLeaf s!"{left} <= {right}" (literal left) (literal right) (word left) (word right)
  checkLeaf "/* left */ 0x09 <= /* right */ 0009" (literal 9) (literal 9) (word 9) (word 9)
  checkLeaf "((r)) <= (l)" (.var 1) (.var 2) (word 9) (word 7)
  let relationalLeft ← expression "l <= r == c"
  assertTrue (match relationalLeft.value with
    | .binary ⟨_, .binary _ ⟨_, .lessEqual⟩ _⟩ ⟨_, .equal⟩ _ => true
    | _ => false) "relational precedence no longer exceeds equality on the left"
  let relationalRight ← expression "c != l <= r"
  assertTrue (match relationalRight.value with
    | .binary _ ⟨_, .notEqual⟩ ⟨_, .binary _ ⟨_, .lessEqual⟩ _⟩ => true
    | _ => false) "relational precedence no longer exceeds inequality on the right"
  checkRun supplied "8 - 2 * 3 | 1 <= 3" (le (.binary .wordOr
    (.binary .wordSub (literal 8) (.binary .wordMul (literal 2) (literal 3))) (literal 1)) (literal 3))
    .bool (.bool true) 19
  checkRun supplied "1 | 2 ^ 3 & 4 + 5 * 2 <= 3" (le (.binary .wordOr (literal 1)
    (.binary .wordXor (literal 2) (.binary .wordAnd (literal 3)
      (.binary .wordAdd (literal 4) (.binary .wordMul (literal 5) (literal 2)))))) (literal 3))
    .bool (.bool true) 27
  let forward := le (.var 2) (.var 1)
  let reversed := le (.var 1) (.var 2)
  checkRun supplied "r <= l && l <= r" (.ifE reversed forward (.bool false)) .bool (.bool false) 10
  checkRun supplied "l <= r && r <= l" (.ifE forward reversed (.bool false)) .bool (.bool false) 16
  checkRun supplied "l <= r || r <= l" (.ifE forward (.bool true) reversed) .bool (.bool true) 10
  checkRun supplied "r <= l || l <= r" (.ifE reversed (.bool true) forward) .bool (.bool true) 16
  for choice in [false, true] do
    let selected := inputs choice
    checkRun selected "r <= l || l <= r && c" (.ifE reversed (.bool true)
      (.ifE forward (.var 0) (.bool false))) .bool (.bool choice) 19
    checkRun selected "c ? l <= r : r <= l" (.ifE (.var 0) forward reversed) .bool (.bool choice) 10
    for content in ["c <= l", "l <= c", "c <= c", "(l <= r) <= l", "l <= (r <= l)",
        "l <= r == c", "c == l <= r", "c != l <= r", "l <= r == l", "l == r <= l",
        "c ? l <= r : c <= c", "l <= r || c <= c", "r <= l && c <= c"] do
      checkRejected selected content true
    for content in ["missing <= 0", "0 <= missing", s!"{Core.wordModulus} <= 0", s!"0 <= {Core.wordModulus}",
        "l <= r || missing <= 0", "r <= l && 0 <= missing", s!"l <= r || 0 <= {Core.wordModulus}",
        "c ? l <= r : missing <= 0", s!"c ? {Core.wordModulus} <= 0 : r <= l"] do
      checkRejected selected content false
  for name in ["Bool", "Unit", "Cell", "Fn", "Opaque"] do
    let content := s!"function same(x: {name}, y: {name}) returns (Bool)" ++ " { return x <= y; }"
    let some declaration ← parsed? (Syntax.Parser.functionDecl .module) content
      | throw (IO.userError "same non-Word operand declaration did not parse")
    assertTrue (compileRuntimeFunction? types owner declaration).isNone "matching non-Word types enabled lessEqual"
  let unit : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
  let cell : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 40, .cellRef⟩
  let closure : TypedRuntimeArgument :=
    ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  for (name, argument) in [("Unit", unit), ("Cell", cell), ("Fn", closure)] do
    let some declaration ← parsed? (Syntax.Parser.functionDecl .module)
      (s!"function same(x: {name}, y: {name}) returns (Bool)" ++ " { return x <= y; }")
      | throw (IO.userError "actual non-Word fixture did not parse")
    assertTrue (prepareRuntimeFunction? types owner declaration [argument, argument]).isNone
      "two actual non-Word values enabled lessEqual"
    for fuel in [0, 7, 30] do
      assertTrue (runRuntimeFunction? types owner declaration [argument, argument] fuel store).isNone
        "rejected actual non-Word lessEqual entered execution"
  for content in ["l(c)", "r(c)"] do
    checkRejected supplied content false
  checkParameterPositions
  checkReturnContract
  checkArithmeticEntry
  for content in ["l <= r <= l", "l <= r > l", "l > r <= l", "l <=", "-1 <= 0", "+1 <= 0",
      "l <= r trailing", "l <= r 0"] do
    assertTrue (← parsed? Syntax.Parser.expression content).isNone "non-associative or incomplete source accepted"
  assertTrue (← parsed? (Syntax.Parser.functionDecl .module)
    "function trailing(l: Word) returns (Bool) { return l <= 0; } trailing").isNone
    "function parser helper accepted only a valid prefix"

end Tests
