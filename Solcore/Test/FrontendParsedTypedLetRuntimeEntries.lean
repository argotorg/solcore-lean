import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunctionFuelBoundProperties
import Solcore.Frontend.RuntimeFunctionResumptionProperties
import Solcore.Frontend.RuntimeFunctionOwnerProperties
import Solcore.Frontend.RuntimeFunctionStoreProperties
import Solcore.Frontend.RuntimeFunctionCompilationTypeExtensionProperties
import Solcore.Frontend.TypedLetReturnBodyFuelBoundProperties
import Solcore.Frontend.TerminalReturnTreeFuelBoundProperties

/-! Compile completely parsed prefixes once, then run actual arguments against
independent Core, typed value and source-cost expectations. Prefix locals are
never parameters; actual checkpoints retain their captured original values. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"PrefixEntries", by decide⟩], by decide⟩⟩, 17⟩
private def otherOwner : Resolved.DeclarationId := { owner with declarationIndex := 71 }
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, .word (word n), .word⟩
private def boolArg (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩),
  (["Pkg", "Token"], .namedData ⟨92⟩), (["Pkg.Token"], .bool)]
private def extras : TypeNameTable := [(["Word"], .bool), (["Fresh"], .namedData ⟨93⟩)]
private def extended := types ++ extras
private theorem grows : TypeNameTable.Extends types extended := TypeNameTable.Extends.append_right types extras
private def stores : List Core.Store := [[.word (word 91), .cellRef .word 40],
  [.closure .bool .bool (.var 0) [], .bool true, .word Core.Word.maximum]]
private def parsed? (content : String) : IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-prefix-entries.sol"⟩, content }
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
  oldPrefix : Bool
private theorem excludeWrong {source : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (provenance : RuntimeFunctionCompiles types owner source compiled) {wrong : Core.Expr} (different : wrong ≠ compiled.core) :
    ¬ RuntimeFunctionCompiles types owner source { compiled with core := wrong } := by
  intro other
  exact different (congrArg CompiledRuntimeFunction.core (other.result_unique provenance))
private def compile (content : String) (core : Core.Expr) (type : Core.Ty) (parameterTypes : List Core.Ty) (bound : Nat)
    (oldPrefix : Bool := true) : IO Entry := do
  let some source ← parsed? content | throw (IO.userError "positive whole declaration did not completely parse")
  match accepted : compileRuntimeFunction? types owner source with
  | none => throw (IO.userError "valid typed-prefix entry did not compile")
  | some compiled =>
      let provenance := compileRuntimeFunction?_sound accepted
      let names ← source.value.signature.parameters.elements.mapM fun parameter => do
        let .typed none name annotation := parameter.value | throw (IO.userError "unexpected parameter shape")
        assertTrue (parameter.span.contains name.span && parameter.span.contains annotation.span && source.span.contains parameter.span)
          "source parameter positions changed"
        pure name.value
      assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧ compiled.inputs.context.values = parameterTypes.reverse ∧
        compiled.inputs.names = (names.zipIdx.map (fun (name, index) => (name, (⟨owner, index⟩ : Resolved.LocalId)))).reverse ∧
        compiled.inputs.bindings.length = parameterTypes.length ∧ Core.infer? parameterTypes.reverse core = some type ∧
        typedLetReturnTreeFuelBound source.value.body = bound ∧ terminalReturnTreeFuelBound source.value.body = 0))
        "compiled prefix changed exact Core/type/bound or leaked locals into original parameter rows"
      if oldPrefix then assertTrue (typedLetReturnBodyFuelBound source.value.body == bound) "old successful prefix bound changed"
      assertTrue ((elaborateTerminalReturnTree? compiled.inputs.names compiled.inputs.context source.value.body).isNone)
        "entry integration broadened the old tree adapter"
      have _ := provenance.core_hasType
      have _ := provenance.extend_types grows
      have _ := compileRuntimeFunction?_some_of_extends grows accepted
      assertTrue (decide ((compileRuntimeFunction? extended owner source).map (fun changed =>
        (changed.core, changed.returnType, changed.inputs.names, changed.inputs.context.values)) =
          some (core, type, compiled.inputs.names, parameterTypes.reverse))) "type extension changed the exact compiled record"
      let wrong := Core.Expr.ifE (.bool true) core core
      if different : wrong ≠ compiled.core then
        have _ := excludeWrong provenance different
        assertTrue (decide (Core.infer? parameterTypes.reverse wrong = some type)) "wrong-Core contrast was not equally typed"
      else throw (IO.userError "wrong-Core contrast became identical")
      return ⟨source, compiled, provenance, oldPrefix⟩
private def observation (observed : Option (Core.Ty × Core.StatefulRunResult))
    (expected : TypedRuntimeArgument) (store : Core.Store) (cost fuel : Nat) : Bool :=
  match observed with
  | some (type, .done value finalStore) => decide (type = expected.type ∧ value = expected.value ∧ finalStore = store ∧ cost ≤ fuel)
  | some (type, .outOfFuel checkpoint) => decide (type = expected.type ∧ checkpoint.store = store ∧ fuel < cost)
  | _ => false
private def checkCase (entry : Entry) (arguments : List TypedRuntimeArgument) (expected : TypedRuntimeArgument) (cost : Nat) : IO Unit := do
  let bound := typedLetReturnTreeFuelBound entry.source.value.body
  assertTrue (decide (expected.type = entry.compiled.returnType ∧ 0 < cost ∧ cost ≤ bound)) "independent value type or source cost disagreed"
  if matching : arguments.map (·.type) = entry.compiled.inputs.context.values.reverse then
    match preparedAt : prepareRuntimeFunction? types owner entry.source arguments with
    | none => throw (IO.userError "matching actual arguments did not prepare")
    | some prepared =>
      let preparation := prepareRuntimeFunction?_sound preparedAt
      have _ := entry.provenance.prepare_arguments arguments matching
      have _ := prepareRuntimeFunction?_factorization types owner entry.source arguments
      assertTrue (decide (prepared.core = entry.compiled.core ∧ prepared.returnType = expected.type ∧
        prepared.inputs.names = entry.compiled.inputs.names ∧ prepared.inputs.context.values = entry.compiled.inputs.context.values ∧
        prepared.inputs.environment.values = arguments.reverse.map (·.value) ∧ prepared.inputs.bindings.length = arguments.length ∧
        prepared.inputs.checkTypedLetReturnTree? types owner entry.source.value.body = some (entry.compiled.core, expected.type)))
        "preparation rebound prefix locals as parameters or changed original ordered actual values"
      if entry.oldPrefix then assertTrue (decide (prepared.inputs.checkTypedLetReturnBody? types owner entry.source.value.body =
        some (entry.compiled.core, expected.type))) "old successful prefix checker changed"
      for store in stores do
        have _ := entry.provenance.run_done_of_fuelBound arguments matching store bound (Nat.le_refl _)
        have _ := preparation.hasType.run_done_of_fuelBound store bound (Nat.le_refl _)
        let initial := Core.State.initial entry.compiled.core (arguments.reverse.map (·.value)) store
        let run := fun fuel => runRuntimeFunction? types owner entry.source arguments fuel store
        match entry.compiled.core with
        | .letE initializer tail =>
            let checkpoint : Core.State := ⟨.eval initializer (arguments.reverse.map (·.value)), [.letBody tail (arguments.reverse.map (·.value))], store⟩
            assertTrue (decide (run 1 = some (expected.type, .outOfFuel checkpoint))) "entry charged wrapper steps or lost its original pending let frame"
        | _ => throw (IO.userError "prefix compiled without ordered Core lets")
        for fuel in List.range (bound + 3) do
          have _ := entry.provenance.run_eq arguments matching fuel store
          have _ := (entry.provenance.extend_types grows).run_eq arguments matching fuel store
          have _ := runRuntimeFunction?_factorization types owner entry.source arguments fuel store
          have _ := runRuntimeFunction?_owner_eq types owner otherOwner entry.source arguments fuel store
          assertTrue (decide (run fuel = some (expected.type, Core.runStateful fuel initial) ∧
            run fuel = prepared.inputs.runTypedLetReturnTree? types owner fuel entry.source.value.body store ∧
            run fuel = runRuntimeFunction? extended owner entry.source arguments fuel store ∧
            run fuel = runRuntimeFunction? types otherOwner entry.source arguments fuel store)) "entry factorization, owner or table extension changed the full result"
          if entry.oldPrefix then
            assertTrue (decide (run fuel = prepared.inputs.runTypedLetReturnBody? types owner fuel entry.source.value.body store))
              "old successful prefix full same-fuel result changed"
          assertTrue (observation (run fuel) expected store cost fuel) "entry changed independent value, cost threshold or own store"
          for replacement in stores do
            have _ := runRuntimeFunction?_done_store_iff types owner entry.source arguments fuel store replacement expected.type expected.value
            have _ := runRuntimeFunction?_outOfFuel_store_iff types owner entry.source arguments fuel store replacement expected.type
            assertTrue (observation (runRuntimeFunction? types owner entry.source arguments fuel replacement) expected replacement cost fuel)
              "store replay changed independent observation"
            if replacement != store then
              assertTrue (decide (run fuel ≠ runRuntimeFunction? types owner entry.source arguments fuel replacement))
                "distinct stores disappeared from complete results"
        for spent in List.range cost do
          match exhausted : run spent with
          | some (type, .outOfFuel checkpoint) =>
              have _ := runRuntimeFunction?_eq_some_compiled_iff.mp exhausted
              assertTrue (decide (Core.runStateful 0 checkpoint = .outOfFuel checkpoint)) "a genuine checkpoint lost pending work"
              for remaining in List.range (cost - spent + 3) do
                have _ := runRuntimeFunction?_resume exhausted remaining
                assertTrue (decide (run (spent + remaining) = some (type, Core.runStateful remaining checkpoint))) "genuine entry resumption changed"
                assertTrue (observation (some (type, Core.runStateful remaining checkpoint)) expected store (cost - spent) remaining)
                  "actual residual threshold disagreed with independent source cost"
              if spent + 1 < cost then
                let .outOfFuel next := Core.runStateful 1 checkpoint | throw (IO.userError "second genuine checkpoint disappeared")
                for last in [0, cost - spent - 1, cost - spent + 1] do
                  assertTrue (decide (run (spent + 1 + last) = some (type, Core.runStateful last next))) "three actual chunks changed their complete result"
              if 0 < spent then assertTrue (decide (run (cost - spent) ≠ some (expected.type, .done expected.value store) ∧
                Core.runStateful (cost - spent) checkpoint = .done expected.value store)) "restarting the entry was mistaken for resumption"
          | _ => throw (IO.userError "expected a genuine checkpoint below independent source cost")
  else throw (IO.userError "positive fixture supplied wrong argument types")
private def rejectArguments (entry : Entry) (arguments : List TypedRuntimeArgument) : IO Unit := do
  assertTrue (decide (arguments.map (·.type) ≠ entry.compiled.inputs.context.values.reverse)) "argument guard contrast became matching"
  for store in stores do
    for fuel in [0, typedLetReturnTreeFuelBound entry.source.value.body, 60] do
      have _ := runRuntimeFunction?_factorization types owner entry.source arguments fuel store
      assertTrue ((prepareRuntimeFunction? types owner entry.source arguments).isNone &&
        (runRuntimeFunction? types owner entry.source arguments fuel store).isNone) "invalid actual arity/type produced a checkpoint"
private def reject (source : Syntax.FunctionDecl) : IO Unit := do
  assertTrue (compileRuntimeFunction? types owner source).isNone "invalid whole entry compiled"
  for arguments in [[], [wordArg 9], [wordArg 9, boolArg true], [wordArg 9, wordArg 2]] do
    for store in stores do
      for fuel in [0, typedLetReturnTreeFuelBound source.value.body, 60] do
        assertTrue ((prepareRuntimeFunction? types owner source arguments).isNone &&
          (runRuntimeFunction? types owner source arguments fuel store).isNone) "whole rejection depended on arguments, store or fuel"

def frontendParsedTypedLetRuntimeEntryTests : IO Unit := do
  for count in [1, 2, 5, 12] do
    let indices := List.range count
    let prefixText := String.join (indices.map fun index => s!"let z{index}: Word=" ++ (if index = 0 then "x" else s!"z{index - 1}") ++ ";")
    let core := indices.foldr (fun index tail => Core.Expr.letE (.var (if index = 0 then 1 else 0)) tail) (.var 0)
    let entry ← compile ("function chain(x: Word,unused: Bool) returns (Word){" ++ prefixText ++ s!"return z{count - 1};" ++ "}") core .word [.word, .bool] (3 * count + 1)
    for value in [0, 9, Core.Word.maximum.val] do
      for flag in [false, true] do checkCase entry [wordArg value, boolArg flag] (wordArg value) (3 * count + 1)
    for arguments in [[], [wordArg 9], [boolArg true, wordArg 9], [wordArg 9, boolArg true, wordArg 7]] do rejectArguments entry arguments
  let ordered ← compile "function ordered(x: Word,r: Word) returns (Word){let y: Word=x;let z: Word=y - r;return z;}"
    (.letE (.var 1) (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 0))) .word [.word, .word] 11
  let unused ← compile "function unused(x: Word,r: Word) returns (Word){let z: Word=x - r;return x;}"
    (.letE (.binary .wordSub (.var 1) (.var 0)) (.var 2)) .word [.word, .word] 8
  let asymmetric ← compile "function asymmetric(c: Bool,d: Bool,x: Word,r: Word) returns (Word){let y: Word=x;if(c){if(d){return ~y;}else{return y - r;}}else{return r;}}"
    (.letE (.var 1) (.ifE (.var 4) (.ifE (.var 3) (.unary .wordNot (.var 0)) (.binary .wordSub (.var 0) (.var 1))) (.var 1))) .word [.bool, .bool, .word, .word] 14
  for (x, r) in [(9, 2), (2, 9), (0, Core.Word.maximum.val), (2 ^ 255, 7)] do
    checkCase ordered [wordArg x, wordArg r] ⟨.word, .word ((word x).sub (word r)), .word⟩ 11
    checkCase unused [wordArg x, wordArg r] (wordArg x) 8
    for c in [false, true] do
      for d in [false, true] do
        checkCase asymmetric [boolArg c, boolArg d, wordArg x, wordArg r]
          ⟨.word, .word (if c then if d then (word x).bitNot else (word x).sub (word r) else word r), .word⟩
          (if c then if d then 12 else 14 else 7)
  let unit : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
  let closure : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  let captured : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩
  for (name, left, right) in [("Cell", (⟨.cell .word, .cellRef .word 17, .cellRef⟩ : TypedRuntimeArgument), ⟨.cell .word, .cellRef .word 29, .cellRef⟩),
      ("Fn", closure, captured), ("Bool", boolArg true, boolArg false), ("Unit", unit, unit)] do
    let entry ← compile (s!"function opaque(x: {name},y: {name}) returns ({name})" ++ "{let a: " ++ name ++ "=y;let b: " ++ name ++ "=x;return a;}")
      (.letE (.var 0) (.letE (.var 2) (.var 1))) left.type [left.type, right.type] 7
    checkCase entry [left, right] right 7
    checkCase entry [right, left] left 7
  let constant ← compile "function constant() returns (Word){let z: Word=7;return z;}" (.letE (.word (word 7)) (.var 0)) .word [] 4
  checkCase constant [] (wordArg 7) 4
  rejectArguments constant [wordArg 7]
  let branch ← compile "function branch(x: Word,c: Bool) returns (Word){let z: Word=x;if(c){let y: Word=z;return y;}else{return x;}}"
    (.letE (.var 1) (.ifE (.var 1) (.letE (.var 0) (.var 0)) (.var 2))) .word [.word, .bool] 10 false
  assertTrue (typedLetReturnBodyFuelBound branch.source.value.body == 7 &&
    (elaborateTypedLetReturnBody? types owner branch.compiled.inputs branch.source.value.body).isNone) "old prefix adapter or bound changed"
  for c in [false, true] do checkCase branch [wordArg 9, boolArg c] (wordArg 9) (if c then 10 else 7)
  have _ (id : Core.DataTypeId) : ¬ ∃ value, Core.ValueHasType value (.namedData id) := by
    rintro ⟨value, typed⟩
    cases typed with
    | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
  for (name, type) in [("Opaque", Core.Ty.namedData ⟨91⟩), ("Pkg.Token", .namedData ⟨92⟩)] do
    for count in [1, 3, 8] do
      let indices := List.range count
      let prefixText := String.join (indices.map fun index => s!"let z{index}: {name}=" ++ (if index = 0 then "x" else s!"z{index - 1}") ++ ";")
      let terminal := Core.Expr.ifE (.var count) (.ifE (.var count) (.var 0) (.var (count + 1))) (.var (count + 1))
      let core := indices.foldr (fun index tail => Core.Expr.letE (.var (if index = 0 then 1 else 0)) tail) terminal
      let entry ← compile (s!"function nominal(x: {name},c: Bool) returns ({name})" ++ "{" ++ prefixText ++
        "if(c){if(c){return " ++ s!"z{count - 1}" ++ ";}else{return x;}}else{return x;}}") core type [type, .bool] (3 * count + 7)
      for argument in [wordArg 9, boolArg true, unit, captured, (⟨.cell .word, .cellRef .word 17, .cellRef⟩ : TypedRuntimeArgument)] do
        rejectArguments entry [argument, boolArg true]
  let validBody := "{let z: Word=7;return z;}"
  for header in ["function generic<T>() returns (Word)", "function many() returns (Word,Bool)", "function empty() returns ()",
      "function unknown() returns (Unknown)", "function duplicate(x: Word,x: Bool) returns (Word)",
      "function staged(comptime x: Word) returns (Word)", "function unknownParameter(x: Unknown) returns (Word)",
      "function wrong() returns (Bool)", "function absent()"] do
    let some source ← parsed? (header ++ validBody) | throw (IO.userError "header/parameter rejection did not parse")
    assertTrue (decide (LocalInputs.empty.checkTypedLetReturnBody? types owner source.value.body =
      some (.letE (.word (word 7)) (.var 0), .word))) "header/parameter contrast did not retain an independently valid body"
    reject source
  let inferred ← compile "function invalid(x: Word,c: Bool) returns (Word){let z=x;return z;}"
    (.letE (.var 1) (.var 0)) .word [.word, .bool] 4 false
  assertTrue (typedLetReturnBodyFuelBound inferred.source.value.body == 0 &&
    (elaborateTypedLetReturnBody? types owner inferred.compiled.inputs inferred.source.value.body).isNone) "old annotated prefix boundary changed"
  checkCase inferred [wordArg 9, boolArg true] (wordArg 9) 4
  for arguments in [[], [wordArg 9], [wordArg 9, wordArg 2]] do rejectArguments inferred arguments
  for body in ["{let z: Word;return x;}", "{let z: Unknown=x;return x;}", "{let z: Bool=x;return x;}",
      "{let x: Word=x;return x;}", "{let z: Word=x;let z: Word=x;return z;}", "{let z: Word=z;return x;}",
      "{let y: Word=z;let z: Word=x;return y;}", "{let z: Word=missing;return x;}", "{let z: Word=x();return x;}",
      "{let z: Word=c ? x : missing;return x;}", "{let z: Word=x;if(c){if(c){return z;}else{return missing;}}else{return x;}}",
      "{let z: Word=x;if(c){return z;}else{return c;}}", "{let z: Word=x;if(x){return z;}else{return x;}}",
      "{let z: Word=x;if(c){return z;}}",
      "{let z: Word=x;return z;return x;}", "{let z: Word=x;z=x;return z;}", "{}"] do
    let some source ← parsed? ("function invalid(x: Word,c: Bool) returns (Word)" ++ body) | throw (IO.userError "bad-prefix fixture did not parse")
    assertTrue (decide (interpretRuntimeFunctionHeader? types source.value.signature = some .word) &&
      (bindRuntimeParameters? types owner source.value.signature.parameters.elements [wordArg 9, boolArg true]).isSome)
      "bad-prefix rejection was caused by header or parameters"
    reject source
  for content in ["function missing(x){let z: Word=7;return z;}", "function incomplete(){let z: Word=;return z;}",
      "function incomplete(){let z: Word=7;return z;", "function trailing(){let z: Word=7;return z;} trailing"] do
    assertTrue (← parsed? content).isNone "incomplete source acquired entry meaning"

end Tests
