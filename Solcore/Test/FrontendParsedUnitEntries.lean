import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunctionEvaluatorProperties
import Solcore.Frontend.RuntimeFunctionFuelBoundProperties
import Solcore.Frontend.RuntimeFunctionResumptionProperties

/-! Complete original Unit entries keep header/argument gates and strict bindings.
Original-source certificates and explicitly written Core paths are independent. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace UnitEntries
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"UnitEntry", by decide⟩], by decide⟩⟩, 17⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool),
  (["Unit"], .unit), (["UnitAlias"], .unit), (["UnitPair"], .product .unit .unit)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, w n, .word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def stores : List Core.Store := [[], [.cellRef .word 40, .bool true, w 91]]
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := { id := ⟨.main, "unit-entry.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  assertTrue lexed.diagnostics.isEmpty "unexpected lexing diagnostic"
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "complete declaration did not parse")
  assertTrue (next.atEnd && next.diagnostics.isEmpty && decide (source.span.source = file.id ∧
    source.span.startByte = 0 ∧ source.span.endByte = content.utf8ByteSize) && source.span.contains source.value.body.span)
    "original declaration range or completion changed"
  return source
private structure Expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost table env store source value store cost
private def expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table env store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "independent name missing")
      | some id =>
          match found : env.lookup? id with
          | none => throw (IO.userError "independent actual value missing")
          | some value => return ⟨value, 1, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | ⟨_, .tuple ⟨_, []⟩⟩ => return ⟨.unit, 1, by rw [sourceAt]; exact .unit⟩
  | ⟨_, .group inner⟩ =>
      let child ← expression table env store inner
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .group child.costed⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let first ← expression table env store left
      let second ← expression table env store right
      return ⟨.pair first.value second.value, first.cost + second.cost + 3, by
        rw [sourceAt]; exact .pair first.costed second.costed⟩
  | _ => throw (IO.userError "expression outside independent unit script")
termination_by sizeOf source
private structure Body (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TypedLetReturnTreeEvaluatesWithCost owner table env store source value store cost
private def body (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Block) : IO (Body table env store source) := do
  match sourceAt : source with
  | ⟨span, ⟨_, .letDecl name (some _) (some initializer)⟩ :: rest⟩ =>
      let first ← expression table env store initializer
      let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let second ← body ((name.value, id) :: table) ((id, first.value) :: env) store ⟨span, rest⟩
      return ⟨second.value, first.cost + second.cost + 2, by rw [sourceAt]; exact .binding first.costed second.costed⟩
  | ⟨_, [⟨_, .ifThen condition yes (some no)⟩]⟩ =>
      let guard ← expression table env store condition
      match selected : guard.value with
      | .bool true =>
          let child ← body table env store yes
          return ⟨child.value, guard.cost + child.cost + 2, by rw [sourceAt]; exact .ifTrue (selected ▸ guard.costed) child.costed⟩
      | .bool false =>
          let child ← body table env store no
          return ⟨child.value, guard.cost + child.cost + 2, by rw [sourceAt]; exact .ifFalse (selected ▸ guard.costed) child.costed⟩
      | _ => throw (IO.userError "independent guard not Boolean")
  | ⟨_, [⟨_, .returnStmt (some operand)⟩]⟩ =>
      let child ← expression table env store operand
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .single (.expression child.costed)⟩
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ => return ⟨.unit, 1, by rw [sourceAt]; exact .single .bare⟩
  | _ => throw (IO.userError "body outside independent unit script")
termination_by sizeOf source
private def check (content : String) (arguments : List TypedRuntimeArgument) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost : Nat)
    (steps : ∀ store k, Core.Steps cost ⟨.eval core (arguments.reverse.map (·.value)), k, store⟩
      ⟨.ret value, k, store⟩) : IO Syntax.FunctionDecl := do
  let source ← parsed content
  let some compiled := compileRuntimeFunction? types owner source | throw (IO.userError "unit entry did not compile")
  let names ← source.value.signature.parameters.elements.mapM fun parameter => do
    let .typed none name annotation := parameter.value | throw (IO.userError "original parameter shape changed")
    assertTrue (source.span.contains parameter.span && parameter.span.contains name.span && parameter.span.contains annotation.span)
      "original parameter range changed"
    pure name.value
  assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧
    compiled.inputs.names = (names.zipIdx.map (fun (name, index) => (name, (⟨owner, index⟩ : Resolved.LocalId)))).reverse ∧
    compiled.inputs.context.values = (arguments.map (·.type)).reverse ∧ compiled.inputs.bindings.length = arguments.length))
    "fixed ordered Core/type or original parameter-only layout changed"
  match preparedAt : prepareRuntimeFunction? types owner source arguments with
  | none => throw (IO.userError "unit arguments did not prepare")
  | some prepared =>
      let preparation := prepareRuntimeFunction?_sound preparedAt
      assertTrue (decide (prepared.core = core ∧ prepared.returnType = type ∧ prepared.inputs.names = compiled.inputs.names ∧
        prepared.inputs.bindings.length = arguments.length ∧ prepared.inputs.environment.values = arguments.reverse.map (·.value)))
        "unit flattened arguments or leaked local bindings into parameter records"
      for store in stores do
        let raw ← body prepared.inputs.names prepared.inputs.environment store source.value.body
        assertTrue (decide (raw.value = value ∧ raw.cost = cost))
          "separate source/Core certificates disagreed with independent fixture"
        let independent := RuntimeFunctionEvaluatesWithCost.intro preparation raw.costed
        have direct := (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp independent).2
        have _ := (runtimeFunctionEvaluatesWithCost_iff_evaluate (initialStore := store) (finalStore := store)).mpr ⟨rfl, direct⟩
        have _ := independent.cost_le_fuelBound
        have _ := (steps store []).runStateful_done_iff (fuel := cost)
        assertTrue (decide (evaluateRuntimeFunctionWithCost? types owner source arguments = some (type, value, cost))) "entry triple changed"
        let run := fun fuel => runRuntimeFunction? types owner source arguments fuel store
        let start := Core.State.initial core (arguments.reverse.map (·.value)) store
        for fuel in List.range (cost + 3) do
          have _ := independent.run_done_iff (fuel := fuel)
          have _ := independent.run_outOfFuel_iff (fuel := fuel)
          assertTrue (decide (run fuel = some (type, Core.runStateful fuel start))) "entry changed fixed Core or full checkpoint"
          assertTrue (match run fuel with
            | some (t, .done v s) => decide (cost ≤ fuel ∧ t = type ∧ v = value ∧ s = store)
            | some (t, .outOfFuel checkpoint) => decide (fuel < cost ∧ t = type ∧ checkpoint.store = store)
            | _ => false) "entry threshold, ordered value or own store changed"
        for spent in List.range cost do
          match exhausted : run spent with
          | some (t, .outOfFuel checkpoint) =>
              for remaining in List.range (cost - spent + 3) do
                have _ := runRuntimeFunction?_resume exhausted remaining
                assertTrue (decide (run (spent + remaining) = some (t, Core.runStateful remaining checkpoint))) "entry residual path changed"
              assertTrue (decide (Core.runStateful (cost - spent) checkpoint = .done value store)) "actual remaining cost changed"
              if 0 < spent then assertTrue (decide (run (cost - spent) ≠ some (type, .done value store))) "restart pretended to resume"
          | _ => throw (IO.userError "below-cost entry checkpoint missing")
  return source
private def rejected (source : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) : IO Unit := do
  assertTrue (prepareRuntimeFunction? types owner source arguments).isNone "invalid unit gate prepared"
  assertTrue (evaluateRuntimeFunctionWithCost? types owner source arguments).isNone "invalid unit gate produced a result"
  for store in stores do
    for fuel in [0, 1, 40] do assertTrue (runRuntimeFunction? types owner source arguments fuel store).isNone "invalid unit gate exposed a checkpoint"
end UnitEntries
open UnitEntries

def frontendParsedUnitEntryTests : IO Unit := do
  for declaration in ["function empty(){return ();}",
      "function alias() returns(UnitAlias){return ();}",
      "function grouped(){return (());}", "function trailing(){return ((),);}"] do
    let source ← check declaration [] .unit .unit .unit 1 (by intro store k; exact .cons .unit .refl)
    for store in stores do
      assertTrue (decide (runRuntimeFunction? types owner source [] 0 store = some (.unit,
        .outOfFuel (Core.State.initial .unit [] store)) ∧
        runRuntimeFunction? types owner source [] 1 store = some (.unit, .done .unit store)))
        "constant entry did not use exactly one Core step"
  let bare ← check "function bare(){return;}" [] .unit .unit .unit 1 (by intro store k; exact .cons .unit .refl)
  let explicit ← parsed "function explicit(){return ();}"
  assertTrue (match bare.value.body.value, explicit.value.body.value with
    | [⟨_, .returnStmt none⟩], [⟨_, .returnStmt (some ⟨_, .tuple ⟨_, []⟩⟩)⟩] => true
    | _, _ => false)
    "bare return and explicit original tuple syntax were identified"
  let boundCore : Core.Expr := .letE .unit (.var 0)
  let bound ← check "function bound() returns(Unit){let u: Unit=();return u;}" [] boundCore .unit .unit 4
    (by intro store k; exact .cons .enterLet (.cons .unit (.cons .bindLet (.cons (.var rfl) .refl))))
  for store in stores do
    assertTrue (decide (runRuntimeFunction? types owner bound [] 2 store = some (.unit,
      .outOfFuel ⟨.ret .unit, [.letBody (.var 0) []], store⟩) ∧
      runRuntimeFunction? types owner bound [] 3 store = some (.unit,
      .outOfFuel ⟨.eval (.var 0) [.unit], [], store⟩))) "strict Unit binding skipped a transition"
  let unitPair : Core.Ty := .product .unit .unit
  let pairValue : Core.Value := .pair .unit .unit
  let pair ← check "function pair() returns(UnitPair){return ((),());}" [] (.pair .unit .unit) unitPair pairValue 5
    (by intro store k; exact .cons .enterPair (.cons .unit (.cons .enterPairRight (.cons .unit (.cons .applyPair .refl)))))
  for store in stores do
    assertTrue (decide (runRuntimeFunction? types owner pair [] 2 store = some (unitPair,
      .outOfFuel ⟨.ret .unit, [.pairRight .unit []], store⟩) ∧
      runRuntimeFunction? types owner pair [] 4 store = some (unitPair,
      .outOfFuel ⟨.ret .unit, [.pairApply .unit], store⟩))) "pair of units was flattened or lost its continuation"
  let _ ← check "function boundPair() returns(UnitPair){let u: Unit=();return (u,());}" []
    (.letE .unit (.pair (.var 0) .unit)) unitPair pairValue 8
    (by intro store k; exact .cons .enterLet (.cons .unit (.cons .bindLet (.cons .enterPair
      (.cons (.var rfl) (.cons .enterPairRight (.cons .unit (.cons .applyPair .refl))))))))
  for n in [0, 9, Core.wordModulus - 1] do
    for choice in [false, true] do
      let arguments := [wordArg n, boolArg choice]
      let unused ← check "function unused(x: Word,c: Bool) returns(UnitAlias){return ();}" arguments .unit .unit .unit 1
        (by intro store k; exact .cons .unit .refl)
      for wrong in [[], [wordArg n], [boolArg choice, wordArg n], [wordArg n, boolArg choice, wordArg 0]] do rejected unused wrong
      let _ ← check "function named(Unit: Word) returns(Word){return Unit;}" [wordArg n] (.var 0) .word (w n) 1
        (by intro store k; exact .cons (.var rfl) .refl)
      let _ ← check "function branches(c: Bool) returns(Unit){if(c){return ();}else{let u: Unit=();return u;}}"
        [boolArg choice] (.ifE (.var 0) .unit boundCore) .unit .unit (if choice then 4 else 7)
        (by intro store k; cases choice <;>
            first
            | exact .cons .enterIf (.cons (.var rfl) (.cons .chooseTrue (.cons .unit .refl)))
            | exact .cons .enterIf (.cons (.var rfl) (.cons .chooseFalse
                (.cons .enterLet (.cons .unit (.cons .bindLet (.cons (.var rfl) .refl)))))))
  for declaration in ["function wrong() returns(Word){return ();}",
      "function unknown() returns(Unknown){return ();}", "function emptyHeader() returns(){return ();}",
      "function emptyType() returns(()){return ();}", "function many() returns(Unit,Unit){return ();}",
      "function unknownUnused(x: Unknown){return ();}",
      "function unselected(c: Bool){if(c){return ();}else{return missing;}}"] do
    let source ← parsed declaration
    let arguments := if declaration.startsWith "function unselected" then [boolArg true] else []
    let table := if arguments.isEmpty then [] else [("c", (⟨owner, 0⟩ : Resolved.LocalId))]
    let env := if arguments.isEmpty then [] else [(⟨owner, 0⟩, Core.Value.bool true)]
    for store in stores do
      let raw ← body table env store source.value.body
      assertTrue (decide (raw.value = .unit ∧ raw.cost = if arguments.isEmpty then 1 else 4))
        "entry gate rejection lost independently successful raw Unit"
    if declaration.startsWith "function unknownUnused" then rejected source [wordArg 0]
    else rejected source arguments
  let overridden ← parsed "function overridden() returns(Unit){return ();}"
  let overrideTypes : TypeNameTable := [(["Unit"], .word)]
  assertTrue (compileRuntimeFunction? overrideTypes owner overridden).isNone "Unit alias was silently reserved"
  assertTrue (evaluateRuntimeFunctionWithCost? overrideTypes owner overridden []).isNone "Unit alias bypassed return typing"
  for declaration in ["function noFlatten() returns(Unit){return ((),());}",
      "function inferred(){return ((),());}", "function noAlias() returns(MissingUnit){return ();}"] do
    let source ← parsed declaration
    rejected source []
end Tests
