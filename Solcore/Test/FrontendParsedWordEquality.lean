import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunction
import Solcore.Frontend.ReturnBody

/-! Complete source parsing connects monomorphic Word equality to Bool results,
ordered pending frames, conservative budgets, and genuine one-step resumption. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedEquality", by decide⟩], by decide⟩⟩, 22⟩
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def literal (value : Nat) : Core.Expr := .word (word value)
private def store : Core.Store := [.word (word 91), .bool false]
private def types : TypeNameTable :=
  [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit), (["Cell"], .cell .word),
    (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩)]
private def inputs (choice : Bool) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner "l" .word (.word (word 7)) .word).bindFresh
    owner "r" .word (.word (word 9)) .word).bindFresh owner "c" .bool (.bool choice) .bool

private def parsed? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) :
    IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-equality.sol"⟩, content }
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
  let checked := supplied.check? source
  assertTrue (decide (checked = some (expectedCore, expectedType))) s!"{content}: wrong exact Core/type"
  assertTrue (decide (cost ≤ localExpressionFuelBound source)) s!"{content}: source budget was insufficient"
  let some (actualCore, _) := checked | throw (IO.userError "missing checked Core")
  let initial := Core.State.initial actualCore supplied.environment.values store
  for fuel in List.range (cost + 3) do
    let observed := supplied.run? fuel source store
    assertTrue (decide (observed = some (expectedType, Core.runStateful fuel initial)))
      s!"{content}: full checked machine result changed"
    assertTrue (match observed with
      | some (type, .done value finalStore) =>
          decide (cost ≤ fuel ∧ type = expectedType ∧ value = expected ∧ finalStore = store)
      | some (type, .outOfFuel suspended) => decide (fuel < cost ∧ type = expectedType ∧ suspended.store = store)
      | _ => false) s!"{content}: wrong value, store, or exact cost"

private def checkLeaf (content : String) (left right : Core.Expr)
    (leftWord rightWord : Core.Word) : IO Unit := do
  let supplied := inputs true
  let expected := Core.Value.bool (leftWord == rightWord)
  checkRun supplied content (.binary .wordEq left right) .bool expected 5
  let source ← expression content
  assertTrue (localExpressionFuelBound source == 5) s!"{content}: leaf equality budget changed"
  let some (.bool, .outOfFuel checkpoint) := supplied.run? 4 source store
    | throw (IO.userError "leaf equality did not yield its genuine four-fuel checkpoint")
  let pending : Core.State := ⟨.ret (.word rightWord), [.binaryApply .wordEq (.word leftWord)], store⟩
  assertTrue (decide (checkpoint = pending ∧ Core.runStateful 0 checkpoint = .outOfFuel pending ∧
    Core.runStateful 1 checkpoint = .done expected store)) "ordered frame or one-step residual path changed"

private def checkRejected (supplied : LocalInputs) (content : String) (resolves : Bool) : IO Unit := do
  let source ← expression content
  assertTrue ((resolveLocalExpression? supplied.names source).isSome == resolves)
    s!"{content}: wrong resolution boundary"
  assertTrue (supplied.check? source).isNone s!"{content}: invalid equality checked"
  for fuel in [0, 4, 30] do
    assertTrue (supplied.run? fuel source store).isNone s!"{content}: whole checking was bypassed"
  let text := "function rejected(l: Word, r: Word, c: Bool) returns (Bool) { return " ++ content ++ "; }"
  let some declaration ← parsed? (Syntax.Parser.functionDecl .module) text
    | throw (IO.userError s!"{content}: wrapped declaration did not parse")
  assertTrue (compileRuntimeFunction? types owner declaration).isNone s!"{content}: invalid whole body compiled"
  for choice in [false, true] do
    let arguments : List TypedRuntimeArgument :=
      [⟨.word, .word (word 7), .word⟩, ⟨.word, .word (word 9), .word⟩, ⟨.bool, .bool choice, .bool⟩]
    assertTrue (prepareRuntimeFunction? types owner declaration arguments).isNone
      "a skipped invalid branch bypassed preparation"
    for fuel in [0, 5, 30] do
      assertTrue (runRuntimeFunction? types owner declaration arguments fuel store).isNone
        "a rejected whole entry produced an execution result"

/-- All 4 + 9 + 16 ordered pairs preserve source IDs, reverse environment
positions, and distinct pending states even though terminal equality commutes. -/
private def checkParameterPositions : IO Unit := do
  for arity in [2, 3, 4] do
    let indices := List.range arity
    let parameters := String.intercalate ", " (indices.map fun index => s!"p{index}: Word")
    for left in indices do
      for right in indices do
        let content := s!"function equality_{arity}_{left}_{right}({parameters}) returns (Bool)"
          ++ " { return " ++ s!"p{left} == p{right};" ++ " }"
        let some declaration ← parsed? (Syntax.Parser.functionDecl .module) content
          | throw (IO.userError s!"{content}: expected complete declaration")
        assertTrue (match declaration.value.body.value with
          | [⟨_, .returnStmt (some ⟨_, .binary ⟨_, .identifier l⟩ ⟨_, .equal⟩ ⟨_, .identifier r⟩⟩)⟩] =>
              l.value == s!"p{left}" && r.value == s!"p{right}"
          | _ => false) s!"{content}: source operator or ordered references changed"
        assertTrue (returnBodyFuelBound declaration.value.body == 5) "parsed equality body budget changed"
        let some compiled := compileRuntimeFunction? types owner declaration
          | throw (IO.userError s!"{content}: value-free compilation failed")
        let expectedCore := Core.Expr.binary .wordEq (.var (arity - 1 - left)) (.var (arity - 1 - right))
        assertTrue (decide (compiled.core = expectedCore ∧ compiled.returnType = .bool ∧
          compiled.inputs.context.values = List.replicate arity Core.Ty.word)) "wrong open Core/type/context"
        assertTrue (decide (compiled.inputs.names = (indices.map fun index =>
          (s!"p{index}", (⟨owner, index⟩ : Resolved.LocalId))).reverse)) "wrong ordered source IDs/names"
        let arguments : List TypedRuntimeArgument := indices.map fun index =>
          ⟨.word, .word (word (10 * index + 1)), .word⟩
        let some prepared := prepareRuntimeFunction? types owner declaration arguments
          | throw (IO.userError "matching actual arguments failed preparation")
        let values := arguments.reverse.map (·.value)
        assertTrue (decide (prepared.inputs.environment.values = values ∧ prepared.core = compiled.core ∧
          prepared.returnType = .bool ∧ prepared.inputs.context = compiled.inputs.context))
          "preparation changed actual ordered values or the compiled projection"
        let initial := Core.State.initial compiled.core values store
        for fuel in List.range 8 do
          assertTrue (decide (runRuntimeFunction? types owner declaration arguments fuel store =
            some (.bool, Core.runStateful fuel initial))) "same-fuel full compiled result differs"
        let pending : Core.State := ⟨.ret (.word (word (10 * right + 1))),
          [.binaryApply .wordEq (.word (word (10 * left + 1)))], store⟩
        let some (.bool, .outOfFuel checkpoint) := runRuntimeFunction? types owner declaration arguments 4 store
          | throw (IO.userError "equality entry lost its genuine fuel-four checkpoint")
        assertTrue (decide (checkpoint = pending ∧ Core.runStateful 0 checkpoint = .outOfFuel pending ∧
          Core.runStateful 1 checkpoint = .done (.bool (left == right)) store))
          "source order, retained left value, or residual one-step result changed"
        if left != right then
          let swapped : Core.State := ⟨.ret (.word (word (10 * left + 1))),
            [.binaryApply .wordEq (.word (word (10 * right + 1)))], store⟩
          assertTrue (decide (pending ≠ swapped ∧ Core.runStateful 1 pending = Core.runStateful 1 swapped))
            "commutativity incorrectly identified ordered intermediate states"

private def checkReturnContract : IO Unit := do
  let some declaration ← parsed? (Syntax.Parser.functionDecl .module)
    "function wrong(l: Word, r: Word) returns (Word) { return l == r; }"
    | throw (IO.userError "wrong return contract did not parse")
  let arguments : List TypedRuntimeArgument := [⟨.word, .word (word 7), .word⟩, ⟨.word, .word (word 9), .word⟩]
  let some bound := bindRuntimeParameters? types owner declaration.value.signature.parameters.elements arguments
    | throw (IO.userError "wrong return contract parameters did not bind")
  assertTrue (decide (bound.checkReturnBody? declaration.value.body =
    some (.binary .wordEq (.var 1) (.var 0), .bool))) "body-only checker lost Bool equality"
  assertTrue (compileRuntimeFunction? types owner declaration).isNone "Bool equality compiled with Word return"
  assertTrue (prepareRuntimeFunction? types owner declaration arguments).isNone "Bool equality prepared with Word return"
  for fuel in [0, 5, 30] do
    assertTrue (runRuntimeFunction? types owner declaration arguments fuel store).isNone "return contract bypassed"

private def checkArithmeticEntry : IO Unit := do
  let some declaration ← parsed? (Syntax.Parser.functionDecl .module)
    "function guard(l: Word, r: Word) returns (Word) { return l * r == r ? l - r : l; }"
    | throw (IO.userError "arithmetic equality entry did not parse")
  let some compiled := compileRuntimeFunction? types owner declaration
    | throw (IO.userError "arithmetic equality entry did not compile")
  assertTrue (decide (compiled.core = .ifE
    (.binary .wordEq (.binary .wordMul (.var 1) (.var 0)) (.var 0))
    (.binary .wordSub (.var 1) (.var 0)) (.var 1) ∧ compiled.returnType = .word))
    "arithmetic equality guard changed exact compiled Core or type"
  assertTrue (returnBodyFuelBound declaration.value.body == 16) "arithmetic guard lost its source bound"
  for left in [0, 1, 7, Core.Word.maximum.val] do
    for right in [0, 1, 9] do
      let arguments : List TypedRuntimeArgument :=
        [⟨.word, .word (word left), .word⟩, ⟨.word, .word (word right), .word⟩]
      let selected := (word left).mul (word right) == word right
      let expected := Core.Value.word (if selected then (word left).sub (word right) else word left)
      let cost := if selected then 16 else 12
      let initial := Core.State.initial compiled.core (arguments.reverse.map (·.value)) store
      for fuel in List.range 19 do
        let observed := runRuntimeFunction? types owner declaration arguments fuel store
        assertTrue (decide (observed = some (.word, Core.runStateful fuel initial)))
          "arithmetic entry diverged from its actual compiled machine"
        assertTrue (match observed with
          | some (.word, .done value finalStore) => decide (cost ≤ fuel ∧ value = expected ∧ finalStore = store)
          | some (.word, .outOfFuel suspended) => decide (fuel < cost ∧ suspended.store = store)
          | _ => false) "arithmetic equality changed the exact 12/16 path cost or result"

def frontendParsedWordEqualityTests : IO Unit := do
  let supplied := inputs true
  checkLeaf "l == r" (.var 2) (.var 1) (word 7) (word 9)
  checkLeaf "r == l" (.var 1) (.var 2) (word 9) (word 7)
  checkLeaf "l == l" (.var 2) (.var 2) (word 7) (word 7)
  for left in [0, 1, 2 ^ 255, Core.Word.maximum.val] do
    for right in [0, 1, 2 ^ 255, Core.Word.maximum.val] do
      checkLeaf s!"{left} == {right}" (literal left) (literal right) (word left) (word right)
  checkLeaf "/* left */ 0x09 == /* right */ 0009" (literal 9) (literal 9) (word 9) (word 9)
  checkLeaf "((r)) == (l)" (.var 1) (.var 2) (word 9) (word 7)
  checkRun supplied "8 - 2 * 3 | 1 == 3" (.binary .wordEq (.binary .wordOr
    (.binary .wordSub (literal 8) (.binary .wordMul (literal 2) (literal 3))) (literal 1)) (literal 3))
    .bool (.bool true) 17
  checkRun supplied "1 | 2 ^ 3 & 4 + 5 * 2 == 3" (.binary .wordEq (.binary .wordOr (literal 1)
    (.binary .wordXor (literal 2) (.binary .wordAnd (literal 3)
      (.binary .wordAdd (literal 4) (.binary .wordMul (literal 5) (literal 2)))))) (literal 3))
    .bool (.bool false) 25
  checkRun supplied "l * r == r ? l - r : l" (.ifE
    (.binary .wordEq (.binary .wordMul (.var 2) (.var 1)) (.var 1))
    (.binary .wordSub (.var 2) (.var 1)) (.var 2)) .word (.word (word 7)) 12
  checkRun supplied "l * r == 63 ? l - r : l" (.ifE
    (.binary .wordEq (.binary .wordMul (.var 2) (.var 1)) (literal 63))
    (.binary .wordSub (.var 2) (.var 1)) (.var 2)) .word (.word ((word 7).sub (word 9))) 16
  let unequal := Core.Expr.binary .wordEq (.var 2) (.var 1)
  let equal := Core.Expr.binary .wordEq (.var 2) (.var 2)
  checkRun supplied "l == r && l == l" (.ifE unequal equal (.bool false)) .bool (.bool false) 8
  checkRun supplied "l == l && l == r" (.ifE equal unequal (.bool false)) .bool (.bool false) 12
  checkRun supplied "l == l || l == r" (.ifE equal (.bool true) unequal) .bool (.bool true) 8
  checkRun supplied "l == r || l == l" (.ifE unequal (.bool true) equal) .bool (.bool true) 12
  for choice in [false, true] do
    let selected := inputs choice
    checkRun selected "l == r || l == l && c" (.ifE unequal (.bool true)
      (.ifE equal (.var 0) (.bool false))) .bool (.bool choice) 15
    checkRun selected "c ? l == r : l == l" (.ifE (.var 0) unequal equal) .bool (.bool (!choice)) 8
    for content in ["c == l", "l == c", "c == c", "(l == r) == l", "l == (r == l)",
        "l > r == c", "c == l > r", "c ? l == r : c == c", "l == l || c == c", "l == r && c == c"] do
      checkRejected selected content true
    for content in ["missing == 0", "0 == missing", s!"{Core.wordModulus} == 0", s!"0 == {Core.wordModulus}",
        "l == l || missing == 0", "l == r && 0 == missing", s!"l == l || 0 == {Core.wordModulus}",
        "c ? l == r : missing == 0", s!"c ? {Core.wordModulus} == 0 : r == l"] do
      checkRejected selected content false
  for name in ["Bool", "Unit", "Cell", "Fn", "Opaque"] do
    let content := s!"function same(x: {name}, y: {name}) returns (Bool)" ++ " { return x == y; }"
    let some declaration ← parsed? (Syntax.Parser.functionDecl .module) content
      | throw (IO.userError "same non-Word operand declaration did not parse")
    assertTrue (compileRuntimeFunction? types owner declaration).isNone
      "same non-Word operand types accidentally enabled polymorphic equality"
  let unit : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
  let cell : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 40, .cellRef⟩
  let closure : TypedRuntimeArgument :=
    ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  for (name, argument) in [("Unit", unit), ("Cell", cell), ("Fn", closure)] do
    let some declaration ← parsed? (Syntax.Parser.functionDecl .module)
      (s!"function same(x: {name}, y: {name}) returns (Bool)" ++ " { return x == y; }")
      | throw (IO.userError "actual non-Word fixture did not parse")
    assertTrue (prepareRuntimeFunction? types owner declaration [argument, argument]).isNone
      "two equal actual non-Word values enabled polymorphic equality"
    for fuel in [0, 5, 30] do
      assertTrue (runRuntimeFunction? types owner declaration [argument, argument] fuel store).isNone
        "rejected actual non-Word equality entered execution"
  checkRun supplied "l != r" (.unary .boolNot (.binary .wordEq (.var 2) (.var 1))) .bool (.bool true) 7
  checkRun supplied "l <= r" (.unary .boolNot (.binary .wordGt (.var 2) (.var 1))) .bool (.bool true) 7
  for content in ["l(c)", "r(c)"] do
    checkRejected supplied content false
  checkParameterPositions
  checkReturnContract
  checkArithmeticEntry
  for content in ["l == r == l", "l ==", "-1 == 0", "+1 == 0", "l == r trailing", "l == r 0"] do
    assertTrue (← parsed? Syntax.Parser.expression content).isNone
      s!"{content}: non-associative, prefix, incomplete, or unconsumed source accepted"
  assertTrue (← parsed? (Syntax.Parser.functionDecl .module)
    "function trailing(l: Word) returns (Bool) { return l == 0; } trailing").isNone
    "function parser helper accepted only a valid prefix"

end Tests
