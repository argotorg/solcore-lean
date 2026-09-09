import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunctionEntry

/-! Fully parsed declarations enter the restricted runtime profile through
their actual header, parameter list, and body. No function lookup or call
continuation is simulated by this external-entry test. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def parsed? (content : String) (location : Syntax.Parser.FunctionLocation := .module) :
    IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-runtime-function.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionDecl location (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Entry", by decide⟩], by decide⟩⟩, 0⟩
private def seven : Core.Word := ⟨7, by decide⟩
private def nine : Core.Word := ⟨9, by decide⟩
private def store : Core.Store := [.word nine, .bool true]
private def types : TypeNameTable :=
  [(["Bool"], .bool), (["Word"], .word), (["U"], .unit), (["Pkg", "Flag"], .bool),
   (["Cell"], .cell .word), (["Fn"], .function .bool .bool)]
private def boolArg (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def wordArg (value : Core.Word) : TypedRuntimeArgument := ⟨.word, .word value, .word⟩
private def closure : Core.Value := .closure .bool .bool (.var 0) []
private theorem closureTyped : Core.ValueHasType closure (.function .bool .bool) :=
  .closure .nil (.var rfl)

private def checkOrder (source : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (inputs : LocalInputs) : IO Unit := do
  let names ← source.value.signature.parameters.elements.mapM fun parameter => do
    let .typed none name _ := parameter.value
      | throw (IO.userError "accepted a non-runtime parameter")
    pure name.value
  assertTrue (decide (names.length = arguments.length)) "accepted mismatched arity"
  let expected : List (String × Resolved.LocalId × Core.Ty × Core.Value) :=
    (names.zip arguments).zipIdx.map fun (entry, index) =>
      (entry.1, (⟨owner, index⟩ : Resolved.LocalId), entry.2.type, entry.2.value)
  let actual := inputs.bindings.map fun binding =>
    (binding.name, binding.id, binding.type, binding.value)
  assertTrue (decide (actual = expected.reverse))
    "entry changed argument pairing, identity allocation, or runtime row order"

private def checkAccepted (table : TypeNameTable) (content : String)
    (arguments : List TypedRuntimeArgument) (expectedCore : Core.Expr) (type : Core.Ty)
    (value : Core.Value) (cost : Nat) (initialStore : Core.Store := store) : IO Unit := do
  let some source ← parsed? content
    | throw (IO.userError s!"{content}: expected a complete declaration")
  let some prepared := prepareRuntimeFunction? table owner source arguments
    | throw (IO.userError s!"{content}: valid restricted entry was rejected")
  checkOrder source arguments prepared.inputs
  assertTrue (decide (prepared.core = expectedCore ∧ prepared.returnType = type))
    s!"{content}: wrong exact Core or declared return type"
  assertTrue (decide (prepared.inputs.checkReturnBody? source.value.body =
    some (prepared.core, prepared.returnType))) s!"{content}: prepared a substitute Core"
  assertTrue (decide (runRuntimeFunction? table owner source arguments 0 initialStore =
    some (type, .outOfFuel (Core.State.initial prepared.core prepared.inputs.environment.values initialStore))))
    s!"{content}: zero fuel did not expose the actual prepared initial state"
  for fuel in [0, 1, 3, 4, 5, 6, 8, cost - 1, cost, cost + 5] do
    assertTrue (decide (runRuntimeFunction? table owner source arguments fuel initialStore =
      prepared.inputs.runReturnBody? fuel source.value.body initialStore))
      s!"{content}: entry changed body execution or a suspended state"
  for fuel in [0, cost - 1] do
    match runRuntimeFunction? table owner source arguments fuel initialStore with
    | some (actualType, .outOfFuel _) =>
        assertTrue (decide (actualType = type)) s!"{content}: exhaustion changed the return type"
    | _ => throw (IO.userError s!"{content}: execution did not exhaust below its exact cost")
  for fuel in [cost, cost + 5] do
    assertTrue (decide (runRuntimeFunction? table owner source arguments fuel initialStore =
      some (type, .done value initialStore)))
      s!"{content}: wrong value, preserved store, or exact completion threshold"

private def checkRejected (content : String) (arguments : List TypedRuntimeArgument := [])
    (location : Syntax.Parser.FunctionLocation := .module) : IO Unit := do
  let some source ← parsed? content location
    | throw (IO.userError s!"{content}: profile rejection case should parse without diagnostics")
  assertTrue (prepareRuntimeFunction? types owner source arguments).isNone
    s!"{content}: unsupported or mismatched declaration entered the runtime profile"
  for fuel in [0, 1, 4, 20] do
    assertTrue (runRuntimeFunction? types owner source arguments fuel store).isNone
      s!"{content}: running bypassed whole declaration preparation"

private def checkInferredLocal : IO Unit := do
  let some source ← parsed? "function local() returns (Word) { let x = 7; return x; }"
    | throw (IO.userError "original inferred local declaration did not parse")
  assertTrue (match source.value.body.value with
    | [⟨ls,.letDecl name none (some ⟨_,.literal ⟨_,.decimal spelling⟩⟩)⟩,
        ⟨rs,.returnStmt (some ⟨_,.identifier returned⟩)⟩] =>
        decide (name.value = "x" ∧ returned.value = "x" ∧ spelling = "7") &&
        source.value.body.span.contains ls && source.value.body.span.contains rs
    | _ => false) "original missing annotation or written initializer was changed"
  let core : Core.Expr := .letE (.word seven) (.var 0)
  let some prepared := prepareRuntimeFunction? types owner source []
    | throw (IO.userError "inferred initialized local was rejected")
  checkOrder source [] prepared.inputs
  assertTrue (decide (prepared.core = core ∧ prepared.returnType = .word) &&
    (prepared.inputs.checkReturnBody? source.value.body).isNone)
    "inferred local changed exact Core or broadened the old singleton body"
  for initialStore in [store, []] do
    have paths (k : List Core.Frame) : Core.Steps 4 ⟨.eval core [], k, initialStore⟩
        ⟨.ret (.word seven), k, initialStore⟩ :=
      .cons .enterLet (.cons .word (.cons .bindLet (.cons (.var rfl) .refl)))
    have _ := paths []
    for fuel in List.range 7 ++ [20] do
      assertTrue (match runRuntimeFunction? types owner source [] fuel initialStore with
        | some (.word,.done value final) => decide (4 ≤ fuel ∧ value = .word seven ∧ final = initialStore)
        | some (.word,.outOfFuel saved) => decide (fuel < 4 ∧ saved.store = initialStore)
        | _ => false) "inferred local changed its independently counted four steps"
    let saved : Core.State := ⟨.ret (.word seven),[.letBody (.var 0) []],initialStore⟩
    assertTrue (decide (runRuntimeFunction? types owner source [] 2 initialStore = some (.word,.outOfFuel saved) ∧
      Core.runStateful 2 saved = .done (.word seven) initialStore)) "inferred local lost its genuine pending let"

private def checkDiscardLiteral : IO Unit := do
  let some source ← parsed? "function before() { 7; return; }"
    | throw (IO.userError "original discarded literal declaration did not parse")
  assertTrue (match source.value.body.value with
    | [⟨ss,.expression ⟨es,.literal ⟨_,.decimal spelling⟩⟩ true⟩, ⟨rs,.returnStmt none⟩] =>
        decide (spelling = "7") && ss.contains es && source.value.body.span.contains ss &&
        source.value.body.span.contains rs
    | _ => false) "original expression, semicolon or bare return was changed"
  let core : Core.Expr := .letE (.word seven) .unit
  let some prepared := prepareRuntimeFunction? types owner source []
    | throw (IO.userError "strict discarded literal was rejected")
  checkOrder source [] prepared.inputs
  assertTrue (decide (prepared.core = core ∧ prepared.returnType = .unit) &&
    (prepared.inputs.checkReturnBody? source.value.body).isNone)
    "discard changed exact Core or widened the old singleton adapter"
  for initialStore in [store, []] do
    have paths (k : List Core.Frame) : Core.Steps 4 ⟨.eval core [], k, initialStore⟩
        ⟨.ret .unit, k, initialStore⟩ :=
      .cons .enterLet (.cons .word (.cons .bindLet (.cons .unit .refl)))
    have _ := paths []
    for fuel in List.range 7 ++ [20] do
      assertTrue (match runRuntimeFunction? types owner source [] fuel initialStore with
        | some (.unit,.done value final) => decide (4 ≤ fuel ∧ value = .unit ∧ final = initialStore)
        | some (.unit,.outOfFuel saved) => decide (fuel < 4 ∧ saved.store = initialStore)
        | _ => false) "discarded literal work was skipped or counted twice"
    for spent in List.range 4 do
      let some (.unit,.outOfFuel saved) := runRuntimeFunction? types owner source [] spent initialStore
        | throw (IO.userError "genuine discard checkpoint absent")
      for remaining in List.range 7 do
        assertTrue (decide (Core.runStateful remaining saved =
          Core.runStateful (spent + remaining) (.initial core [] initialStore))) "discard checkpoint was restarted"
    let saved : Core.State := ⟨.ret (.word seven),[.letBody .unit []],initialStore⟩
    assertTrue (decide (runRuntimeFunction? types owner source [] 2 initialStore = some (.unit,.outOfFuel saved) ∧
      Core.runStateful 2 saved = .done .unit initialStore)) "discard lost the actual pending expression value"

private def checkTerminalBlock : IO Unit := do
  let some source ← parsed? "function nested() { { return; } }"
    | throw (IO.userError "original nested declaration did not parse")
  match atBody : source.value.body with
  | ⟨outerSpan, [⟨innerSpan, .block [⟨returnSpan, .returnStmt none⟩]⟩]⟩ =>
      have _ : TypedLetReturnTreeElaborates types owner .empty source.value.body .unit .unit := by
        rw [atBody]; exact .block (.single .bare)
      assertTrue (outerSpan.contains innerSpan && innerSpan.contains returnSpan &&
        decide (outerSpan.startByte < innerSpan.startByte ∧ innerSpan.endByte < outerSpan.endByte))
        "original inner braces were replaced by the outer block range"
  | _ => throw (IO.userError "original nested return AST changed")
  let some prepared := prepareRuntimeFunction? types owner source []
    | throw (IO.userError "terminal block was rejected")
  checkOrder source [] prepared.inputs
  assertTrue (decide (prepared.core = .unit ∧ prepared.returnType = .unit) &&
    (prepared.inputs.checkReturnBody? source.value.body).isNone) "wrapper changed Core or the old adapter"
  for initialStore in [store, []] do
    have paths (k : List Core.Frame) : Core.Steps 1 ⟨.eval .unit [], k, initialStore⟩
        ⟨.ret .unit, k, initialStore⟩ := .cons .unit .refl
    have _ := paths []
    for fuel in List.range 4 ++ [20] do
      assertTrue (decide (runRuntimeFunction? types owner source [] fuel initialStore =
        some (.unit, Core.runStateful fuel (.initial .unit [] initialStore)))) "wrapper added a transition"
      assertTrue (match runRuntimeFunction? types owner source [] fuel initialStore with
        | some (.unit, .done value final) => decide (1 ≤ fuel ∧ value = .unit ∧ final = initialStore)
        | some (.unit, .outOfFuel cp) => decide (fuel = 0 ∧ cp = .initial .unit [] initialStore ∧
            Core.runStateful 1 cp = .done .unit initialStore)
        | _ => false) "wrapped return changed its genuine one-step residual"

def frontendParsedRuntimeFunctionEntryTests : IO Unit := do
  checkInferredLocal
  checkDiscardLiteral
  checkTerminalBlock
  checkAccepted types "function empty() { return; }" [] .unit .unit .unit 1
  checkAccepted types "function explicit() returns (U,) { return; }" [] .unit .unit .unit 1
  checkAccepted types "/* lead */ function literal() returns (Word) { return ((0007)); }"
    [] (.word seven) .word (.word seven) 1
  checkAccepted types "function invert() returns (Word) { return ~7; }"
    [] (.unary .wordNot (.word seven)) .word (.word seven.bitNot) 3
  for left in [false, true] do
    for right in [false, true] do
      checkAccepted types "function first(left: Bool, right: Bool) returns (Bool) { return left; }"
        [boolArg left, boolArg right] (.var 1) .bool (.bool left) 1
      checkAccepted types "function last(left: Bool, right: Bool) returns (Bool) { return right; }"
        [boolArg left, boolArg right] (.var 0) .bool (.bool right) 1
  for choice in [false, true] do
    let arguments := [boolArg choice, wordArg seven, wordArg nine]
    checkAccepted types
      "function choose(c: Pkg /* qualified */ . Flag, t: Word, f: Word,) returns (Word) { return c ? t : f; }"
      arguments (.ifE (.var 2) (.var 1) (.var 0)) .word (.word (if choice then seven else nine)) 4
    checkAccepted types
      "function selected(c: Bool, t: Word, f: Word) returns (Word) { return c ? ~t : f; }"
      arguments (.ifE (.var 2) (.unary .wordNot (.var 1)) (.var 0)) .word
      (.word (if choice then seven.bitNot else nine)) (if choice then 6 else 4)
    checkAccepted types
      "function logical(c: Bool, t: Word, f: Word) returns (Bool) { return c && !c; }"
      arguments (.ifE (.var 2) (.unary .boolNot (.var 2)) (.bool false)) .bool (.bool false)
      (if choice then 6 else 4)
    checkAccepted types
      "function bitwise(c: Bool, t: Word, f: Word) returns (Word) { return t ^ f; }"
      arguments (.binary .wordXor (.var 1) (.var 0)) .word (.word (seven.bitXor nine)) 5
    checkRejected "function missing(c: Bool, t: Word, f: Word) returns (Word) { return c ? t : missing; }"
      arguments
    checkRejected "function branches(c: Bool, t: Word, f: Word) returns (Word) { return c ? t : c; }"
      arguments
  checkAccepted [(["Word"], .bool)] "function alias(x: Word) returns (Word) { return x; }"
    [boolArg true] (.var 0) .bool (.bool true) 1
  checkAccepted types "function cell(x: Cell) returns (Cell) { return x; }"
    [⟨.cell .word, .cellRef .word 40, .cellRef⟩] (.var 0) (.cell .word) (.cellRef .word 40) 1 []
  checkAccepted types "function closure(x: Fn) returns (Fn) { return x; }"
    [⟨.function .bool .bool, closure, closureTyped⟩] (.var 0) (.function .bool .bool) closure 1
  -- Every source position is checked across several arities, not only endpoints.
  let pool : List (String × TypedRuntimeArgument) :=
    [("Bool", boolArg false), ("Word", wordArg seven), ("Bool", boolArg true), ("Word", wordArg nine),
     ("U", ⟨.unit, .unit, .unit⟩), ("Cell", ⟨.cell .word, .cellRef .word 40, .cellRef⟩),
     ("Fn", ⟨.function .bool .bool, closure, closureTyped⟩), ("Word", wordArg seven.bitNot)]
  for arity in [1, 2, 3, 4, 5, 6, 7, 8] do
    let rows := pool.take arity
    let parameters := String.intercalate ", " (rows.zipIdx.map fun (row, index) => s!"p{index}: {row.1}")
    for (selected, index) in rows.zipIdx do
      let content := s!"function projection_{arity}_{index}({parameters}) returns ({selected.1})"
        ++ " { return " ++ s!"p{index};" ++ " }"
      checkAccepted types content (rows.map Prod.snd) (.var (arity - 1 - index))
        selected.2.type selected.2.value 1 []
  let mismatch := "function mismatch() returns (Bool) { return 7; }"
  let some mismatched ← parsed? mismatch
    | throw (IO.userError "return mismatch example did not parse")
  assertTrue (decide (LocalInputs.empty.checkReturnBody? mismatched.value.body =
    some (.word seven, .word))) "entry contract incorrectly changed the body-only endpoint"
  checkRejected mismatch
  checkAccepted types "function addition() returns (Word) { return 7 + 9; }" []
    (.binary .wordAdd (.word seven) (.word nine)) .word (.word (seven.add nine)) 5
  checkAccepted types "function subtraction() returns (Word) { return 7 - 9; }" []
    (.binary .wordSub (.word seven) (.word nine)) .word (.word (seven.sub nine)) 5
  checkAccepted types "function multiplication() returns (Word) { return 7 * 9; }" []
    (.binary .wordMul (.word seven) (.word nine)) .word (.word (seven.mul nine)) 5
  for content in [
      "function absent() { return 7; }", "function bare() returns (Word) { return; }",
      "function empty() returns () { return; }", "function many() returns (Word, Bool) { return 7; }",
      "function unknown() returns (Unknown) { return; }",
      "function application() returns (Word<Bool>) { return 7; }",
      "function proxy() returns (@Word) { return 7; }",
      "function tuple() returns ((Word, Bool)) { return 7; }",
      "function generic<T>() { return; }", "function constrained() where Word: Eq { return; }",
      "function emptyBody() {}",
      "function repeated() { return; return; }", "function tail() returns (Word) { 7 }",
      "function discarded() { return; missing; }",
      "function call() returns (Word) { return missing(); }"] do
    checkRejected content
  for content in ["function publicOnly() public { return; }",
      "function payableOnly() payable { return; }", "function both() public payable { return; }"] do
    checkRejected content [] .contract
  for (content, arguments) in [
      ("function arity(x: Bool) returns (Bool) { return x; }", []),
      ("function arity() { return; }", [boolArg false]),
      ("function arity(x: Bool) returns (Bool) { return x; }", [boolArg false, boolArg true]),
      ("function duplicate(x: Bool, x: Bool) returns (Bool) { return x; }", [boolArg false, boolArg true]),
      ("function mismatch(x: Word) returns (Word) { return x; }", [boolArg true]),
      ("function compile(comptime x: Bool) returns (Bool) { return x; }", [boolArg true])] do
    checkRejected content arguments
  for content in ["", "function f()", "function f() { return;", "function f() { return 7 }",
      "function f() { return; } trailing", "function f() public { return; }"] do
    assertTrue (← parsed? content).isNone
      s!"{content}: accepted malformed, diagnosed, or incompletely consumed declaration text"

end Tests
