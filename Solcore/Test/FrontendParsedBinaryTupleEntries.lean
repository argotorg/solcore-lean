import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunctionEvaluatorProperties
import Solcore.Frontend.RuntimeFunctionFuelBoundProperties
import Solcore.Frontend.RuntimeFunctionResumptionProperties

/-! Complete original declarations use named product aliases, not tuple type
syntax or multiple returns. Raw source and fixed Core certificates are separate. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace BinaryTupleEntries
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TupleEntry", by decide⟩], by decide⟩⟩, 17⟩
private def pairType : Core.Ty := .product .word .bool
private def nestedType : Core.Ty := .product pairType .word
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Pair"], pairType),
  (["Nested"], nestedType), (["Cell"], .cell .word), (["Fn"], .function .word .word),
  (["OpaquePair"], .product (.cell .word) (.function .word .word)),
  (["Nominal"], .namedData ⟨91⟩), (["NominalPair"], .product (.namedData ⟨91⟩) .bool)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, w n, .word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def stores : List Core.Store := [[], [.cellRef .word 40, .bool true, w 91]]
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := { id := ⟨.main, "tuple-entry.sol"⟩, content }
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
  | ⟨_, .group inner⟩ =>
      let child ← expression table env store inner
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .group child.costed⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let first ← expression table env store left
      let second ← expression table env store right
      return ⟨.pair first.value second.value, first.cost + second.cost + 3, by
        rw [sourceAt]; exact .pair first.costed second.costed⟩
  | _ => throw (IO.userError "expression outside independent tuple script")
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
  | _ => throw (IO.userError "body outside independent tuple script")
termination_by sizeOf source
private structure Path (env : Core.Environment) (store : Core.Store) (core : Core.Expr) where
  value : Core.Value
  cost : Nat
  steps : ∀ k, Core.Steps cost ⟨.eval core env, k, store⟩ ⟨.ret value, k, store⟩
private def path (env : Core.Environment) (store : Core.Store) (core : Core.Expr) : IO (Path env store core) := do
  match coreAt : core with
  | .var index =>
      match found : env[index]? with
      | none => throw (IO.userError "independent Core position missing")
      | some value => return ⟨value, 1, by intro k; rw [coreAt]; exact .cons (.var found) .refl⟩
  | .pair left right =>
      let first ← path env store left
      let second ← path env store right
      return ⟨.pair first.value second.value, first.cost + second.cost + 3, by
        intro k; rw [coreAt]
        have steps := Core.Steps.cons .enterPair ((first.steps (.pairRight right env :: k)).trans
          (.cons .enterPairRight ((second.steps (.pairApply first.value :: k)).trans (.cons .applyPair .refl))))
        simpa only [Nat.add_assoc] using steps⟩
  | .letE initializer tail =>
      let first ← path env store initializer
      let second ← path (first.value :: env) store tail
      return ⟨second.value, first.cost + second.cost + 2, by
        intro k; rw [coreAt]
        have steps := Core.Steps.cons .enterLet ((first.steps _).trans (.cons .bindLet (second.steps k)))
        simpa only [Nat.add_assoc] using steps⟩
  | .ifE condition yes no =>
      let guard ← path env store condition
      match selected : guard.value with
      | .bool true =>
          let child ← path env store yes
          return ⟨child.value, guard.cost + child.cost + 2, by
            intro k; rw [coreAt]
            have before := guard.steps (.ifBranches yes no env :: k)
            rw [selected] at before
            have steps := Core.Steps.cons .enterIf (before.trans (.cons .chooseTrue (child.steps k)))
            simpa only [Nat.add_assoc] using steps⟩
      | .bool false =>
          let child ← path env store no
          return ⟨child.value, guard.cost + child.cost + 2, by
            intro k; rw [coreAt]
            have before := guard.steps (.ifBranches yes no env :: k)
            rw [selected] at before
            have steps := Core.Steps.cons .enterIf (before.trans (.cons .chooseFalse (child.steps k)))
            simpa only [Nat.add_assoc] using steps⟩
      | _ => throw (IO.userError "independent Core guard not Boolean")
  | _ => throw (IO.userError "Core outside fixed tuple script")
termination_by sizeOf core
private def check (content : String) (arguments : List TypedRuntimeArgument) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost : Nat) : IO Syntax.FunctionDecl := do
  let source ← parsed content
  let some compiled := compileRuntimeFunction? types owner source | throw (IO.userError "tuple entry did not compile")
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
  | none => throw (IO.userError "tuple arguments did not prepare")
  | some prepared =>
      let preparation := prepareRuntimeFunction?_sound preparedAt
      assertTrue (decide (prepared.core = core ∧ prepared.returnType = type ∧ prepared.inputs.names = compiled.inputs.names ∧
        prepared.inputs.bindings.length = arguments.length ∧ prepared.inputs.environment.values = arguments.reverse.map (·.value)))
        "tuple flattened arguments or leaked local bindings into parameter records"
      for store in stores do
        let raw ← body prepared.inputs.names prepared.inputs.environment store source.value.body
        let fixed ← path (arguments.reverse.map (·.value)) store core
        assertTrue (decide (raw.value = value ∧ raw.cost = cost ∧ fixed.value = value ∧ fixed.cost = cost))
          "separate source/Core certificates disagreed with independent fixture"
        let independent := RuntimeFunctionEvaluatesWithCost.intro preparation raw.costed
        have direct := (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp independent).2
        have _ := (runtimeFunctionEvaluatesWithCost_iff_evaluate (initialStore := store) (finalStore := store)).mpr ⟨rfl, direct⟩
        have _ := independent.cost_le_fuelBound
        have _ := (fixed.steps []).runStateful_done_iff (fuel := cost)
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
  assertTrue (prepareRuntimeFunction? types owner source arguments).isNone "invalid tuple gate prepared"
  assertTrue (evaluateRuntimeFunctionWithCost? types owner source arguments).isNone "invalid tuple gate produced a result"
  for store in stores do
    for fuel in [0, 1, 40] do assertTrue (runRuntimeFunction? types owner source arguments fuel store).isNone "invalid tuple gate exposed a checkpoint"
end BinaryTupleEntries
open BinaryTupleEntries

def frontendParsedBinaryTupleEntryTests : IO Unit := do
  for n in [2, 9, Core.wordModulus - 1] do
    for choice in [false, true] do
      let arguments := [wordArg n, boolArg choice]
      let value := Core.Value.pair (w n) (.bool choice)
      let simple ← check "function pair(x: Word,c: Bool) returns(Pair){return (x,c);}" arguments
        (.pair (.var 1) (.var 0)) pairType value 5
      for store in stores do
        assertTrue (decide (runRuntimeFunction? types owner simple arguments 2 store = some (pairType,
          .outOfFuel ⟨.ret (w n), [.pairRight (.var 0) [.bool choice, w n]], store⟩)))
          "entry pair checkpoint lost source parameter positions or actual saved environment"
      for wrong in [[], [wordArg n], [boolArg choice, wordArg n], [wordArg n, boolArg choice, wordArg 0]] do rejected simple wrong
      let _ ← check "function grouped(x: Word,c: Bool) returns(Pair){return (((x,),c,));}" arguments
        (.pair (.var 1) (.var 0)) pairType value 5
      let _ ← check "function nested(x: Word,c: Bool) returns(Nested){return ((x,c),x);}" arguments
        (.pair (.pair (.var 1) (.var 0)) (.var 1)) nestedType (.pair value (w n)) 9
      let bound ← check "function bound(x: Word,c: Bool) returns(Nested){let p: Pair=(x,c);return (p,x);}" arguments
        (.letE (.pair (.var 1) (.var 0)) (.pair (.var 0) (.var 2))) nestedType (.pair value (w n)) 12
      for store in stores do
        assertTrue (decide (runRuntimeFunction? types owner bound arguments 6 store = some (nestedType,
          .outOfFuel ⟨.ret value, [.letBody (.pair (.var 0) (.var 2)) [.bool choice, w n]], store⟩) ∧
          runRuntimeFunction? types owner bound arguments 7 store = some (nestedType,
          .outOfFuel ⟨.eval (.pair (.var 0) (.var 2)) [value, .bool choice, w n], [], store⟩)))
          "tuple initializer bound the tail early or changed the actual local product"
      let _ ← check "function branches(x: Word,c: Bool) returns(Pair){if(c){let p: Pair=(x,c);return p;}else{return (x,c);}}" arguments
        (.ifE (.var 0) (.letE (.pair (.var 1) (.var 0)) (.var 0)) (.pair (.var 1) (.var 0))) pairType value (if choice then 11 else 8)
      let pairArgument : TypedRuntimeArgument := ⟨pairType, value, .pair .word .bool⟩
      let _ ← check "function reuse(p: Pair) returns(Pair){return p;}" [pairArgument] (.var 0) pairType value 1
      for declaration in ["function wrong(x: Word,c: Bool) returns(Bool){return (x,c);}",
          "function unknown(x: Word,c: Bool) returns(Unknown){return (x,c);}",
          "function many(x: Word,c: Bool) returns(Word,Bool){return (x,c);}",
          "function tupleType(x: Word,c: Bool) returns((Word,Bool)){return (x,c);}",
          "function unused(x: Word,c: Bool) returns(Pair){if(c){return (x,c);}else{return (missing,c);}}"] do
        let source ← parsed declaration
        let some actual := bindRuntimeParameters? types owner source.value.signature.parameters.elements arguments
          | throw (IO.userError "raw gate contrast lost original actual arguments")
        if choice || !declaration.startsWith "function unused" then
          for store in stores do
            let raw ← body actual.names actual.environment store source.value.body
            assertTrue (decide (raw.value = value ∧ raw.cost = if declaration.startsWith "function unused" then 8 else 5))
              "whole rejection lost independently successful raw tuple"
        rejected source arguments
  let cell : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 999, .cellRef⟩
  let closure : TypedRuntimeArgument := ⟨.function .word .word, .closure .word .word (.var 1) [w 7], .closure (.cons .word .nil) (.var rfl)⟩
  let _ ← check "function opaque(x: Cell,f: Fn) returns(OpaquePair){return (x,f);}" [cell, closure]
    (.pair (.var 1) (.var 0)) (.product cell.type closure.type) (.pair cell.value closure.value) 5
  let nominal ← parsed "function nominal(x: Nominal,c: Bool) returns(NominalPair){return (x,c);}"
  assertTrue (decide ((compileRuntimeFunction? types owner nominal).map (fun c => (c.core, c.returnType)) =
    some (.pair (.var 1) (.var 0), .product (.namedData ⟨91⟩) .bool))) "nominal product static compilation required an inhabitant"
  have _ (id : Core.DataTypeId) : ¬ ∃ value, Core.ValueHasType value (.namedData id) := by
    rintro ⟨_, typed⟩; cases typed with
    | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
  rejected nominal [wordArg 9, boolArg true]
  for operand in ["()", "(x,c,x)", "[x,c]", "(x,c).first", "(x,c)[0]"] do
    let source ← parsed ("function unsupported(x: Word,c: Bool) returns(Pair){return " ++ operand ++ ";}")
    rejected source [wordArg 9, boolArg true]

end Tests
