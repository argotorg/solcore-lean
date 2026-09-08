import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunctionFuelBoundProperties
import Solcore.Frontend.RuntimeFunctionResumptionProperties
import Solcore.Frontend.RuntimeFunctionOwnerProperties
import Solcore.Frontend.RuntimeFunctionStoreProperties
import Solcore.Frontend.RuntimeFunctionCompilationTypeExtensionProperties
import Solcore.Frontend.TypedLetReturnBodyFuelBoundProperties

/-! Complete declarations retain independently specified Core and original
parameters. Selected source certificates fix values and costs before executing
the entry; genuine checkpoints retain branch-local values and captured frames. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"RecursiveLetEntries", by decide⟩], by decide⟩⟩, 17⟩
private def otherOwner : Resolved.DeclarationId := { owner with declarationIndex := 71 }
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, .word (word n), .word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩), (["Pkg", "Token"], .namedData ⟨92⟩)]
private def extended := types ++ [(["Word"], Core.Ty.bool), (["Fresh"], .namedData ⟨93⟩)]
private theorem grows : TypeNameTable.Extends types extended := TypeNameTable.Extends.append_right _ _
private def stores : List Core.Store := [[.word (word 91), .cellRef .word 40], [.closure .bool .bool (.var 0) [], .bool true, .word Core.Word.maximum]]
private def parsed? (content : String) : IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-recursive-let-entries.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) with
  | .ok source next => return if next.atEnd && next.diagnostics.isEmpty then some source else none
  | .reject _ _ => return none
  | .invariant _ => throw (IO.userError "parser invariant")
private structure Entry where
  source : Syntax.FunctionDecl
  compiled : CompiledRuntimeFunction
  provenance : RuntimeFunctionCompiles types owner source compiled
private theorem excludeWrong {source : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (provenance : RuntimeFunctionCompiles types owner source compiled) {wrong : Core.Expr} (different : wrong ≠ compiled.core) :
    ¬ RuntimeFunctionCompiles types owner source { compiled with core := wrong } := by
  intro other
  exact different (congrArg CompiledRuntimeFunction.core (other.result_unique provenance))
private def compile (content : String) (core : Core.Expr) (type : Core.Ty) (parameters : List Core.Ty) (bound : Nat) : IO Entry := do
  let some source ← parsed? content | throw (IO.userError "positive declaration did not completely parse")
  match accepted : compileRuntimeFunction? types owner source with
  | none => throw (IO.userError "recursive typed entry rejected")
  | some compiled =>
      let names ← source.value.signature.parameters.elements.mapM fun parameter => do
        let .typed none name annotation := parameter.value | throw (IO.userError "parameter shape changed")
        assertTrue (source.span.contains parameter.span && parameter.span.contains name.span && parameter.span.contains annotation.span) "parameter source positions changed"
        pure name.value
      assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧ compiled.inputs.context.values = parameters.reverse ∧
        compiled.inputs.names = (names.zipIdx.map (fun (name, index) => (name, (⟨owner, index⟩ : Resolved.LocalId)))).reverse ∧
        compiled.inputs.bindings.length = parameters.length ∧ Core.infer? parameters.reverse core = some type ∧ typedLetReturnTreeFuelBound source.value.body = bound) &&
        (elaborateTypedLetReturnBody? types owner compiled.inputs source.value.body).isNone) "exact Core/type/bound or original parameter-only rows changed"
      have proof := compileRuntimeFunction?_sound accepted
      have _ := proof.core_hasType
      have _ := compileRuntimeFunction?_some_of_extends grows accepted
      assertTrue (decide ((compileRuntimeFunction? extended owner source).map (fun c => (c.core, c.returnType, c.inputs.names, c.inputs.context.values)) =
        some (core, type, compiled.inputs.names, parameters.reverse))) "annotation extension changed compiled provenance"
      let wrong := Core.Expr.ifE (.bool true) core core
      if different : wrong ≠ compiled.core then
        have _ := excludeWrong proof different
        assertTrue (decide (Core.infer? parameters.reverse wrong = some type)) "wrong Core did not retain the same type"
      else throw (IO.userError "wrong-Core contrast became identical")
      return ⟨source, compiled, proof⟩

private structure Expression (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost table environment store source value store cost
private def expression (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) :
    IO (Expression table environment store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "independent source name missing")
      | some id =>
          match found : environment.lookup? id with
          | none => throw (IO.userError "independent actual value missing")
          | some value => return ⟨value, 1, by rw [sourceAt]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | ⟨_, .unary ⟨_, .bitNot⟩ operand⟩ =>
      let child ← expression table environment store operand
      match valueAt : child.value with
      | .word value => return ⟨.word value.bitNot, child.cost + 2, by rw [sourceAt]; exact .bitNot (valueAt ▸ child.costed)⟩
      | _ => throw (IO.userError "word-not fixture had nonword value")
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let l ← expression table environment store left
      let r ← expression table environment store right
      match leftAt : l.value, rightAt : r.value with
      | .word x, .word y => return ⟨.word (x.sub y), l.cost + r.cost + 3, by rw [sourceAt]; exact .subtract (leftAt ▸ l.costed) (rightAt ▸ r.costed)⟩
      | _, _ => throw (IO.userError "subtraction fixture had nonword values")
  | _ => throw (IO.userError "expression outside independent source script")
termination_by sizeOf source
private structure Certificate (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store) (body : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TypedLetReturnTreeEvaluatesWithCost owner table environment store body value store cost
private def certify (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store) (body : Syntax.Block)
    (choices : List Bool) : IO (Certificate table environment store body) := do
  match sourceAt : body with
  | ⟨blockSpan, ⟨_, .letDecl name (some _) (some initializer)⟩ :: rest⟩ =>
      let value ← expression table environment store initializer
      let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let tail ← certify ((name.value, id) :: table) ((id, value.value) :: environment) store ⟨blockSpan, rest⟩ choices
      return ⟨tail.value, value.cost + tail.cost + 2, by rw [sourceAt]; exact .binding value.costed tail.costed⟩
  | ⟨_, [⟨_, .ifThen condition left (some right)⟩]⟩ =>
      let choice :: rest := choices | throw (IO.userError "missing selected branch")
      let guard ← expression table environment store condition
      if agrees : guard.value = .bool choice then
        match choiceAt : choice with
        | true =>
            let tail ← certify table environment store left rest
            return ⟨tail.value, guard.cost + tail.cost + 2, by rw [sourceAt]; exact .ifTrue (by simpa only [agrees, choiceAt] using guard.costed) tail.costed⟩
        | false =>
            let tail ← certify table environment store right rest
            return ⟨tail.value, guard.cost + tail.cost + 2, by rw [sourceAt]; exact .ifFalse (by simpa only [agrees, choiceAt] using guard.costed) tail.costed⟩
      else throw (IO.userError "independent branch disagreed with actual value")
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ =>
      assertTrue choices.isEmpty "branch script continued after bare return"
      return ⟨.unit, 1, by rw [sourceAt]; exact .single .bare⟩
  | ⟨_, [⟨_, .returnStmt (some operand)⟩]⟩ =>
      assertTrue choices.isEmpty "branch script continued after return"
      let value ← expression table environment store operand
      return ⟨value.value, value.cost, by rw [sourceAt]; exact .single (.expression value.costed)⟩
  | _ => throw (IO.userError "body outside independent source script")
termination_by sizeOf body
private def observation (result : Option (Core.Ty × Core.StatefulRunResult)) (expected : TypedRuntimeArgument) (store : Core.Store) (cost fuel : Nat) : Bool :=
  match result with
  | some (type, .done value finalStore) => decide (type = expected.type ∧ value = expected.value ∧ finalStore = store ∧ cost ≤ fuel)
  | some (type, .outOfFuel state) => decide (type = expected.type ∧ state.store = store ∧ fuel < cost)
  | _ => false
private def checkCase (entry : Entry) (arguments : List TypedRuntimeArgument) (choices : List Bool) (expected : TypedRuntimeArgument) (cost : Nat) : IO Unit := do
  if matching : arguments.map (·.type) = entry.compiled.inputs.context.values.reverse then
    match preparedAt : prepareRuntimeFunction? types owner entry.source arguments with
    | none => throw (IO.userError "matching original arguments rejected")
    | some prepared =>
      let preparation := prepareRuntimeFunction?_sound preparedAt
      have _ := prepareRuntimeFunction?_factorization types owner entry.source arguments
      assertTrue (decide (prepared.core = entry.compiled.core ∧ prepared.returnType = expected.type ∧
        prepared.inputs.names = entry.compiled.inputs.names ∧ prepared.inputs.context.values = entry.compiled.inputs.context.values ∧
        prepared.inputs.bindings.length = arguments.length ∧ prepared.inputs.environment.values = arguments.reverse.map (·.value))) "branch locals leaked into parameters or argument order changed"
      for store in stores do
        let source ← certify prepared.inputs.names prepared.inputs.environment store entry.source.value.body choices
        assertTrue (decide (source.value = expected.value ∧ source.cost = cost)) "independent source value or cost differs"
        have costed := RuntimeFunctionEvaluatesWithCost.intro preparation source.costed
        have _ := costed.compiled_toSteps entry.provenance
        have _ := costed.cost_le_fuelBound
        let bound := typedLetReturnTreeFuelBound entry.source.value.body
        have _ := preparation.hasType.run_done_of_fuelBound store bound (Nat.le_refl _)
        have _ := entry.provenance.run_done_of_fuelBound arguments matching store bound (Nat.le_refl _)
        let initial := Core.State.initial entry.compiled.core (arguments.reverse.map (·.value)) store
        let run := fun fuel => runRuntimeFunction? types owner entry.source arguments fuel store
        for fuel in List.range (bound + 3) do
          have _ := entry.provenance.run_eq arguments matching fuel store
          have _ := runRuntimeFunction?_owner_eq types owner otherOwner entry.source arguments fuel store
          assertTrue (decide (run fuel = some (expected.type, Core.runStateful fuel initial) ∧
            run fuel = prepared.inputs.runTypedLetReturnTree? types owner fuel entry.source.value.body store ∧
            run fuel = runRuntimeFunction? extended owner entry.source arguments fuel store ∧
            run fuel = runRuntimeFunction? types otherOwner entry.source arguments fuel store) && observation (run fuel) expected store cost fuel)
            "entry changed exact Core, independent threshold, owner, dictionary or actual checkpoint"
          for replacement in stores do
            have _ := runRuntimeFunction?_done_store_iff types owner entry.source arguments fuel store replacement expected.type expected.value
            have _ := runRuntimeFunction?_outOfFuel_store_iff types owner entry.source arguments fuel store replacement expected.type
            assertTrue (observation (runRuntimeFunction? types owner entry.source arguments fuel replacement) expected replacement cost fuel) "own-store observation changed"
        for spent in List.range cost do
          match exhausted : run spent with
          | some (type, .outOfFuel checkpoint) =>
            if sameType : type = prepared.returnType then
              have actualOut : run spent = some (prepared.returnType, .outOfFuel checkpoint) := by simpa only [sameType] using exhausted
              have _ := costed.residual_of_outOfFuel actualOut
              if actualCore : Core.runStateful spent initial = .outOfFuel checkpoint then
                have _ := costed.compiled_residual_of_outOfFuel entry.provenance actualCore
                pure ()
              else throw (IO.userError "entry checkpoint differs from actual compiled path")
              for remaining in List.range (cost - spent + 3) do
                have _ := runRuntimeFunction?_resume exhausted remaining
                assertTrue (decide (run (spent + remaining) = some (type, Core.runStateful remaining checkpoint)) &&
                  observation (some (type, Core.runStateful remaining checkpoint)) expected store (cost - spent) remaining) "actual residual replay changed"
              let middle := (cost - spent) / 2
              let .outOfFuel next := Core.runStateful middle checkpoint | throw (IO.userError "middle checkpoint missing")
              for last in [0, cost - spent - middle - 1, cost - spent - middle, cost - spent - middle + 2] do
                assertTrue (decide (run (spent + middle + last) = some (type, Core.runStateful last next))) "three chunks lost captured branch-local values"
              if 0 < spent then assertTrue (decide (run (cost - spent) ≠ some (expected.type, .done expected.value store))) "restart was mistaken for resumption"
            else throw (IO.userError "entry changed declared result type")
          | _ => throw (IO.userError "missing genuine below-cost checkpoint")
  else throw (IO.userError "positive fixture has wrong argument types")
private def rejectArguments (entry : Entry) (arguments : List TypedRuntimeArgument) : IO Unit := do
  assertTrue (decide (arguments.map (·.type) ≠ entry.compiled.inputs.context.values.reverse)) "negative argument list unexpectedly matched"
  for store in stores do
    for fuel in [0, typedLetReturnTreeFuelBound entry.source.value.body, 60] do
      have _ := runRuntimeFunction?_factorization types owner entry.source arguments fuel store
      assertTrue ((prepareRuntimeFunction? types owner entry.source arguments).isNone && (runRuntimeFunction? types owner entry.source arguments fuel store).isNone) "wrong arity/type produced a state"
private def alternating (depth level : Nat) (annotation : String) : String × Core.Expr :=
  match depth with
  | 0 => ("return " ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";", .var (if level = 0 then 1 else 0))
  | count + 1 =>
      let (tail, core) := alternating count (level + 1) annotation
      let recursive := s!"let z{level}: {annotation}=" ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";" ++ tail
      let leaf := s!"let z{level}: {annotation}=y;return z{level};"
      let next := Core.Expr.letE (.var (if level = 0 then 1 else 0)) core
      let short := Core.Expr.letE (.var level) (.var 0)
      if level % 2 = 0 then ("if(c){" ++ recursive ++ "}else{" ++ leaf ++ "}", .ifE (.var (level + 3)) next short)
      else ("if(d){" ++ leaf ++ "}else{" ++ recursive ++ "}", .ifE (.var (level + 2)) short next)

def frontendParsedRecursiveTypedLetRuntimeEntryTests : IO Unit := do
  for depth in [1, 2, 5, 12] do
    let (body, core) := alternating depth 0 "Word"
    let entry ← compile ("function recursive(c: Bool,d: Bool,x: Word,y: Word) returns (Word){" ++ body ++ "}") core .word [.bool, .bool, .word, .word] (6 * depth + 1)
    for c in [false, true] do
      for d in [false, true] do
        let choices := if !c then [false] else if depth = 1 then [true] else if d then [true, true] else (List.range depth).map fun n => n % 2 == 0
        checkCase entry [boolArg c, boolArg d, wordArg 9, wordArg 2] choices (if c && (depth == 1 || !d) then wordArg 9 else wordArg 2)
          (if !c || depth == 1 then 7 else if d then 13 else 6 * depth + 1)
    for args in [[], [boolArg true], [wordArg 9, wordArg 2, boolArg true, boolArg false], [boolArg true, boolArg false, wordArg 9, wordArg 2, wordArg 7]] do rejectArguments entry args
  let ordered ← compile "function ordered(c: Bool,d: Bool,x: Word,y: Word) returns (Word){if(c){let z: Word=x - y;if(d){let w: Word=z;return ~w;}else{let w: Word=y - z;return w;}}else{let z: Word=y - x;return y;}}"
    (.ifE (.var 3) (.letE (.binary .wordSub (.var 1) (.var 0)) (.ifE (.var 3) (.letE (.var 0) (.unary .wordNot (.var 0)))
      (.letE (.binary .wordSub (.var 1) (.var 0)) (.var 0)))) (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 1))) .word [.bool, .bool, .word, .word] 21
  for (x, y) in [(9, 2), (2, 9), (0, Core.Word.maximum.val), (2 ^ 255, 7)] do
    for c in [false, true] do
      for d in [false, true] do
        checkCase ordered [boolArg c, boolArg d, wordArg x, wordArg y] (if c then [true, d] else [false])
          ⟨.word, .word (if c then if d then ((word x).sub (word y)).bitNot else (word y).sub ((word x).sub (word y)) else word y), .word⟩ (if c then if d then 19 else 21 else 11)
  let closure : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩
  for (name, x, y) in [("Cell", (⟨.cell .word, .cellRef .word 17, .cellRef⟩ : TypedRuntimeArgument), ⟨.cell .word, .cellRef .word 29, .cellRef⟩),
      ("Fn", closure, ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩), ("Unit", ⟨.unit, .unit, .unit⟩, ⟨.unit, .unit, .unit⟩)] do
    let entry ← compile (s!"function opaque(c: Bool,x: {name},y: {name}) returns ({name})" ++ "{if(c){let z: " ++ name ++ "=x;if(c){let w: " ++ name ++ "=y;return z;}else{return z;}}else{let z: " ++ name ++ "=y;return z;}}")
      (.ifE (.var 2) (.letE (.var 1) (.ifE (.var 3) (.letE (.var 1) (.var 1)) (.var 0))) (.letE (.var 0) (.var 0))) x.type [.bool, x.type, y.type] 13
    for c in [false, true] do checkCase entry [boolArg c, x, y] (if c then [true, true] else [false]) (if c then x else y) (if c then 13 else 7)
  let simple ← compile "function simple(c: Bool,x: Word) returns (Word){if(c){let z: Word=x;return z;}else{return x;}}"
    (.ifE (.var 1) (.letE (.var 0) (.var 0)) (.var 0)) .word [.bool, .word] 7
  assertTrue (decide (typedLetReturnBodyFuelBound simple.source.value.body = 4)) "old bound changed or no longer contrasts with seven steps"
  for c in [false, true] do checkCase simple [boolArg c, wordArg 9] [c] (wordArg 9) (if c then 7 else 4)
  for store in stores do
    let env := [Core.Value.word (word 9), .bool true]
    for (spent, state) in [(2, (⟨.ret (.bool true), [.ifBranches (.letE (.var 0) (.var 0)) (.var 0) env], store⟩ : Core.State)),
        (4, ⟨.eval (.var 0) env, [.letBody (.var 0) env], store⟩), (5, ⟨.ret (.word (word 9)), [.letBody (.var 0) env], store⟩),
        (6, ⟨.eval (.var 0) (.word (word 9) :: env), [], store⟩)] do
      assertTrue (decide (runRuntimeFunction? types owner simple.source [boolArg true, wordArg 9] spent store = some (.word, .outOfFuel state))) "independent if/initializer/tail checkpoint changed"
  have _ (id : Core.DataTypeId) : ¬ ∃ value, Core.ValueHasType value (.namedData id) := by
    rintro ⟨value, typed⟩
    cases typed with
    | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
  for (name, type) in [("Opaque", Core.Ty.namedData ⟨91⟩), ("Pkg.Token", .namedData ⟨92⟩)] do
    for depth in [1, 3, 8] do
      let (body, core) := alternating depth 0 name
      let entry ← compile (s!"function nominal(c: Bool,d: Bool,x: {name},y: {name}) returns ({name})" ++ "{" ++ body ++ "}") core type [.bool, .bool, type, type] (6 * depth + 1)
      for value in [wordArg 9, boolArg true, closure, (⟨.cell .word, .cellRef .word 17, .cellRef⟩ : TypedRuntimeArgument)] do rejectArguments entry [boolArg true, boolArg false, value, value]
  let closedBody := "{if(0==0){let z: Word=7;return z;}else{return 7;}}"
  for header in ["function generic<T>() returns (Word)", "function many() returns (Word,Bool)", "function empty() returns ()",
      "function unknown() returns (Unknown)", "function duplicate(x: Word,x: Bool) returns (Word)",
      "function staged(comptime x: Word) returns (Word)", "function unknownParameter(x: Unknown) returns (Word)",
      "function wrong() returns (Bool)", "function absent()"] do
    let some source ← parsed? (header ++ closedBody) | throw (IO.userError "negative header failed to parse")
    assertTrue (decide (LocalInputs.empty.checkTypedLetReturnTree? types owner source.value.body =
      some (.ifE (.binary .wordEq (.word .zero) (.word .zero)) (.letE (.word (word 7)) (.var 0)) (.word (word 7)), .word)) &&
      (compileRuntimeFunction? types owner source).isNone) "header rejection lost its independently valid recursive body"
    for args in [[], [wordArg 9], [wordArg 9, boolArg true]] do
      for store in stores do
        for fuel in [0, 11, 60] do
          assertTrue ((prepareRuntimeFunction? types owner source args).isNone &&
            (runRuntimeFunction? types owner source args fuel store).isNone) "invalid header, parameter or return contract acquired execution"
  let some invalid ← parsed? "function hidden(c: Bool,x: Word) returns (Word){if(c){let z: Word=x;return z;}else{let z: Unknown=x;return z;}}"
    | throw (IO.userError "raw-versus-whole contrast failed to parse")
  let some actual := bindRuntimeParameters? types owner invalid.value.signature.parameters.elements [boolArg true, wordArg 9]
    | throw (IO.userError "raw-versus-whole contrast had invalid parameters")
  for store in stores do
    let raw ← certify actual.names actual.environment store invalid.value.body [true]
    assertTrue (decide (raw.value = .word (word 9) ∧ raw.cost = 7) && (compileRuntimeFunction? types owner invalid).isNone &&
      (runRuntimeFunction? types owner invalid [boolArg true, wordArg 9] 7 store).isNone) "selected raw success hid an invalid unselected annotation"
  for body in ["{if(c){let z=x;return z;}else{return x;}}", "{if(c){let z: Word;return x;}else{return x;}}",
      "{if(c){let z: Unknown=x;return x;}else{return x;}}", "{if(c){let z: Bool=x;return x;}else{return x;}}", "{if(c){let x: Word=x;return x;}else{return x;}}",
      "{if(c){let z: Word=z;return x;}else{return x;}}", "{if(c){let z: Word=x;return z;}else{return z;}}",
      "{if(c){let z: Word=x;return z;}else{if(c){return x;}else{return missing;}}}", "{if(c){let z: Word=x;return z;}else{return c;}}",
      "{if(x){let z: Word=x;return z;}else{return x;}}", "{if(c){let z: Word=x;return z;}}", "{if(c){return x;}else{return x;}return x;}", "{}"] do
    let some source ← parsed? ("function invalid(c: Bool,x: Word) returns (Word)" ++ body) | throw (IO.userError "negative body failed to parse")
    assertTrue (decide (interpretRuntimeFunctionHeader? types source.value.signature = some .word) &&
      (bindRuntimeParameters? types owner source.value.signature.parameters.elements [boolArg true, wordArg 9]).isSome &&
      (compileRuntimeFunction? types owner source).isNone) "whole invalid source was accepted or had a bad header/parameters"
    for store in stores do
      for fuel in [0, typedLetReturnTreeFuelBound source.value.body, 60] do
        assertTrue ((runRuntimeFunction? types owner source [boolArg true, wordArg 9] fuel store).isNone) "invalid unselected child acquired execution"
  for content in ["function missing(x){if(x){return;}else{return;}}", "function incomplete(){if(0==0){let z: Word=;return z;}else{return 7;}}",
      "function incomplete(){if(0==0){return 7;}else{return 7;}", "function trailing(){return;} trailing"] do
    assertTrue (← parsed? content).isNone "incomplete source acquired entry meaning"

end Tests
