import Solcore.Syntax.Parser.Function
import Solcore.Frontend.TypedLetReturnBody
import Solcore.Frontend.RuntimeParameterDeclarations
import Solcore.Frontend.RuntimeFunction

/-! Type dictionaries change, but parsed bodies and their originally declared
input rows do not. First-match preservation is stronger than retaining rows. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"PrefixTypes", by decide⟩], by decide⟩⟩, 17⟩
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def base : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩),
  (["Pkg", "Token"], .namedData ⟨92⟩), (["Pkg.Token"], .word), (["Word"], .bool)]
private def alternate : TypeNameTable := [(["Opaque"], .namedData ⟨91⟩), (["Fn"], .function .bool .bool),
  (["Unit"], .unit), (["Cell"], .cell .word), (["Bool"], .bool), (["Pkg.Token"], .word),
  (["Pkg", "Token"], .namedData ⟨92⟩), (["Word"], .word), (["Opaque"], .word), (["Word"], .unit)]
private def extras : TypeNameTable := [(["WordAlias"], .word), (["Alias"], .namedData ⟨91⟩), (["Word"], .bool)]
private def extended := base ++ extras
private theorem sameLookup (key : List String) : base.lookup? key = alternate.lookup? key := by
  by_cases w : ["Word"] = key
  · subst key; rfl
  by_cases b : ["Bool"] = key
  · subst key; rfl
  by_cases u : ["Unit"] = key
  · subst key; rfl
  by_cases c : ["Cell"] = key
  · subst key; rfl
  by_cases f : ["Fn"] = key
  · subst key; rfl
  by_cases o : ["Opaque"] = key
  · subst key; rfl
  by_cases q : ["Pkg", "Token"] = key
  · subst key; rfl
  by_cases flattened : ["Pkg.Token"] = key
  · subst key; rfl
  simp [base, alternate, TypeNameTable.lookup?, w, b, u, c, f, o, q, flattened]
private theorem fromLookup {old next : TypeNameTable}
    (same : ∀ key, old.lookup? key = next.lookup? key) : TypeNameTable.Extends old next := by
  intro key type found
  exact TypeNameTable.lookup?_iff.mp ((same key).symm.trans (TypeNameTable.lookup?_iff.mpr found))
private theorem forward : TypeNameTable.Extends base alternate := fromLookup sameLookup
private theorem backward : TypeNameTable.Extends alternate base := fromLookup (fun key => (sameLookup key).symm)
private theorem grows : TypeNameTable.Extends base extended := TypeNameTable.Extends.append_right base extras
private def stores : List Core.Store := [[.word (word 91), .cellRef .word 40],
  [.closure .bool .bool (.var 0) [], .bool true, .word Core.Word.maximum]]
private def parsed {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO α := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-prefix-type-extensions.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  let .ok source next := parser (Syntax.Parser.State.initial file lexed) | throw (IO.userError s!"fixture did not parse: {content}")
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd) "incomplete or diagnosed source"
  return source
private def declared (source : Syntax.FunctionDecl) : IO LocalTypeInputs := do
  let parameters := source.value.signature.parameters.elements
  match accepted : declareRuntimeParameters? base owner parameters with
  | none => throw (IO.userError "original value-free source parameters did not declare")
  | some inputs =>
      have _ := declareRuntimeParameters?_sound accepted
      let rows := parameters.filterMap fun parameter => match parameter.value with
        | .typed none name annotation => (interpretTypeName? base annotation).map (name.value, ·)
        | _ => none
      assertTrue (decide (rows.length = parameters.length ∧ inputs.names.map Prod.fst = (rows.map Prod.fst).reverse ∧
        inputs.context.values = (rows.map Prod.snd).reverse ∧ inputs.ids =
          (List.range parameters.length).reverse.map (fun index => (⟨owner, index⟩ : Resolved.LocalId)))) "original parameter rows changed"
      return inputs
private def staticCheck (inputs : LocalTypeInputs) (body : Syntax.Block) (expected : Option (Core.Expr × Core.Ty)) : IO Unit := do
  have _ := elaborateTypedLetReturnBody?_eq_of_mutual_extends forward backward owner inputs body
  assertTrue (decide (elaborateTypedLetReturnBody? base owner inputs body = expected ∧
    elaborateTypedLetReturnBody? alternate owner inputs body = expected)) "mutual extension changed an exact optional result"
  match accepted : elaborateTypedLetReturnBody? base owner inputs body with
  | none => pure ()
  | some (core, type) =>
      have _ := (elaborateTypedLetReturnBody?_elaborates accepted).extend_types grows
      have _ := (elaborateTypedLetReturnBody?_sound accepted).extend_types grows
      have _ := elaborateTypedLetReturnBody?_some_of_extends grows accepted
      assertTrue (decide (elaborateTypedLetReturnBody? extended owner inputs body = some (core, type) ∧
        Core.infer? inputs.context.values core = some type)) "one-way extension changed successful Core or type"
private def actual (source : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) : IO LocalInputs := do
  let static ← declared source
  match accepted : bindRuntimeParameters? base owner source.value.signature.parameters.elements arguments with
  | none => throw (IO.userError "original actual arguments did not bind")
  | some inputs =>
      have _ := (bindRuntimeParameters?_sound accepted).erase_values.complete
      assertTrue (decide (inputs.environment.values = (arguments.map (·.value)).reverse ∧
        inputs.names = static.names ∧ inputs.context = static.context)) "actual arguments changed declaration positions or values"
      return inputs
private def expectedObservation (observed : Option (Core.Ty × Core.StatefulRunResult))
    (type : Core.Ty) (value : Core.Value) (store : Core.Store) (cost fuel : Nat) : Bool :=
  match observed with
  | some (actualType, .done result finalStore) => decide (actualType = type ∧ result = value ∧ finalStore = store ∧ cost ≤ fuel)
  | some (actualType, .outOfFuel checkpoint) => decide (actualType = type ∧ checkpoint.store = store ∧ fuel < cost)
  | _ => false
private def runChecked (inputs : LocalInputs) (body : Syntax.Block) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost bound : Nat) : IO Unit := do
  staticCheck inputs.toTypeInputs body (some (core, type))
  have _ := inputs.checkTypedLetReturnBody?_eq_of_mutual_extends forward backward owner body
  match checked : inputs.checkTypedLetReturnBody? base owner body with
  | none => throw (IO.userError "positive body did not check")
  | some _ =>
      have _ := LocalInputs.checkTypedLetReturnBody?_some_of_extends grows checked
      assertTrue (decide (inputs.checkTypedLetReturnBody? extended owner body = some (core, type) ∧
        typedLetReturnBodyFuelBound body = bound)) "checker extension or independent numerical bound changed"
  for store in stores do
    let run := fun types fuel => inputs.runTypedLetReturnBody? types owner fuel body store
    match core with
    | .letE initializer tail =>
        let checkpoint : Core.State := ⟨.eval initializer inputs.environment.values, [.letBody tail inputs.environment.values], store⟩
        assertTrue (decide (run base 1 = some (type, .outOfFuel checkpoint) ∧ run alternate 1 = run base 1 ∧ run extended 1 = run base 1))
          "dictionary change rewrote original values or the pending let frame"
    | _ => pure ()
    for fuel in List.range (bound + 3) do
      have sameResult := inputs.runTypedLetReturnBody?_eq_of_mutual_extends forward backward owner fuel body store
      assertTrue (decide (run base fuel = run alternate fuel ∧
        run base fuel = some (type, Core.runStateful fuel (.initial core inputs.environment.values store)))) "mutual extension changed full execution"
      assertTrue (expectedObservation (run base fuel) type value store cost fuel) "independent value, store or cost threshold changed"
      match original : run base fuel with
      | none => throw (IO.userError "whole accepted body returned none")
      | some (actualType, result) =>
          have extendedAt := LocalInputs.runTypedLetReturnBody?_some_of_extends grows original
          have alternateAt := sameResult.symm.trans original
          assertTrue (decide (run extended fuel = some (actualType, result))) "one-way extension did not retain the full successful pair"
          match resultAt : result with
          | .outOfFuel checkpoint =>
              have originalOut : run base fuel = some (actualType, .outOfFuel checkpoint) := by
                simpa only [resultAt] using original
              have alternateOut : run alternate fuel = some (actualType, .outOfFuel checkpoint) := by
                simpa only [resultAt] using alternateAt
              have extendedOut : run extended fuel = some (actualType, .outOfFuel checkpoint) := by
                simpa only [resultAt] using extendedAt
              for remaining in List.range (cost - fuel + 3) do
                have _ := LocalInputs.runTypedLetReturnBody?_resume originalOut remaining
                have _ := LocalInputs.runTypedLetReturnBody?_resume alternateOut remaining
                have _ := LocalInputs.runTypedLetReturnBody?_resume extendedOut remaining
                assertTrue (decide (run base (fuel + remaining) = some (type, Core.runStateful remaining checkpoint) ∧
                  run alternate (fuel + remaining) = run base (fuel + remaining) ∧ run extended (fuel + remaining) = run base (fuel + remaining)))
                  "type extension rebuilt a genuine checkpoint or changed its resumption"
              assertTrue (decide (Core.runStateful (cost - fuel) checkpoint = .done value store)) "genuine residual changed its expected value"
          | _ => pure ()
private def fixture (content : String) (arguments : List TypedRuntimeArgument) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost bound : Nat) : IO Unit := do
  let source ← parsed (Syntax.Parser.functionDecl .module) content
  let inputs ← actual source arguments
  assertTrue (decide (interpretRuntimeFunctionHeader? base source.value.signature = some type)) "body used a wrong header contrast"
  runChecked inputs source.value.body core type value cost bound
  for names in [base, alternate, extended] do
    assertTrue (decide ((compileRuntimeFunction? names owner source).map (fun compiled =>
      (compiled.core, compiled.returnType, compiled.inputs.names, compiled.inputs.context.values)) =
        some (core, type, inputs.names, inputs.context.values))) "entry dictionary extension changed exact Core or original parameter-only rows"
    for store in stores do
      for fuel in List.range (bound + 3) do
        assertTrue (decide (runRuntimeFunction? names owner source arguments fuel store =
          inputs.runTypedLetReturnBody? base owner fuel source.value.body store)) "entry dictionary extension changed complete body execution"

def frontendParsedTypedLetReturnBodyTypeExtensionTests : IO Unit := do
  assertTrue (decide (base ≠ alternate ∧ base.length ≠ alternate.length)) "different hidden rows or dictionary ordering became trivial"
  have _ (id : Core.DataTypeId) : ¬ ∃ value, Core.ValueHasType value (.namedData id) := by
    rintro ⟨value, typed⟩
    cases typed with
    | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
  for (annotation, type) in [("Opaque", Core.Ty.namedData ⟨91⟩), ("Pkg.Token", .namedData ⟨92⟩)] do
    for count in [0, 1, 2, 5, 12] do
      let indices := List.range count
      let declarations := String.join (indices.map fun index => s!"let z{index}: {annotation}=" ++ (if index = 0 then "x" else s!"z{index - 1}") ++ ";")
      let selected := if count = 0 then "x" else s!"z{count - 1}"
      let source ← parsed (Syntax.Parser.functionDecl .module) (s!"function nominal(x: {annotation},y: {annotation},c: Bool) returns ({annotation})" ++
        "{" ++ declarations ++ "if(c){if(c){return " ++ selected ++ ";}else{return y;}}else{return x;}}")
      let inputs ← declared source
      let terminal := Core.Expr.ifE (.var count) (.ifE (.var count) (.var (if count = 0 then 2 else 0)) (.var (count + 1))) (.var (count + 2))
      let core := indices.foldr (fun index tail => Core.Expr.letE (.var (if index = 0 then 2 else 0)) tail) terminal
      staticCheck inputs source.value.body (some (core, type))
      assertTrue (decide (typedLetReturnBodyFuelBound source.value.body = 3 * count + 7)) "nominal numeric bound required an inhabitant"
  for (x, r) in [(word 9, word 2), (Core.Word.zero, Core.Word.maximum), (word (2 ^ 255), word 7)] do
    let args : List TypedRuntimeArgument := [⟨.word, .word x, .word⟩, ⟨.word, .word r, .word⟩]
    fixture "function ordered(x: Word,r: Word) returns (Word){let y: Word=x;let z: Word=y - r;return z;}" args
      (.letE (.var 1) (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 0))) .word (.word (x.sub r)) 11 11
    fixture "function unused(x: Word,r: Word) returns (Word){let z: Word=x - r;return x;}" args
      (.letE (.binary .wordSub (.var 1) (.var 0)) (.var 2)) .word (.word x) 8 8
    for c in [false, true] do
      for d in [false, true] do
        fixture "function asymmetric(c: Bool,d: Bool,x: Word,r: Word) returns (Word){let y: Word=x;if(c){if(d){return ~y;}else{return y - r;}}else{return r;}}"
          ([⟨.bool, .bool c, .bool⟩, ⟨.bool, .bool d, .bool⟩] ++ args)
          (.letE (.var 1) (.ifE (.var 4) (.ifE (.var 3) (.unary .wordNot (.var 0)) (.binary .wordSub (.var 0) (.var 1))) (.var 1)))
          .word (.word (if c then if d then x.bitNot else x.sub r else r)) (if c then if d then 12 else 14 else 7) 14
  for (name, argument) in [("Cell", (⟨.cell .word, .cellRef .word 29, .cellRef⟩ : TypedRuntimeArgument)),
      ("Fn", ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩),
      ("Unit", ⟨.unit, .unit, .unit⟩), ("Bool", ⟨.bool, .bool false, .bool⟩)] do
    fixture (s!"function opaque(x: {name}) returns ({name})" ++ "{let y: " ++ name ++ "=x;let z: " ++ name ++ "=y;return z;}") [argument]
      (.letE (.var 0) (.letE (.var 0) (.var 0))) argument.type argument.value 7 7
  for body in ["{let z: Unknown=x;return z;}", "{let z: Bool=x;return z;}", "{let x: Word=x;return x;}",
      "{let z: Word=x;let z: Word=x;return z;}", "{let z=x;return z;}", "{let z: Word;return x;}",
      "{let z: Word=z;return x;}", "{let y: Word=z;let z: Word=x;return y;}", "{let z: Word=missing;return x;}",
      "{let z: Word=x();return x;}", "{let z: Word<Bool> = x;return x;}",
      "{let z: Word=x;if(c){if(c){return z;}else{return missing;}}else{return x;}}",
      "{let z: Word=x;if(c){return z;}else{return c;}}", "{let z: Word=x;if(x){return z;}else{return x;}}",
      "{let z: Word=x;if(c){return z;}}", "{let z: Word=x;if(c){let y: Word=z;return y;}else{return x;}}", "{}"] do
    let source ← parsed (Syntax.Parser.functionDecl .module) ("function rejected(x: Word,c: Bool) returns (Word)" ++ body)
    let inputs ← actual source [⟨.word, .word (word 9), .word⟩, ⟨.bool, .bool true, .bool⟩]
    staticCheck inputs.toTypeInputs source.value.body none
    have _ := inputs.checkTypedLetReturnBody?_eq_of_mutual_extends forward backward owner source.value.body
    for store in stores do
      for fuel in List.range (typedLetReturnBodyFuelBound source.value.body + 3) do
        have _ := inputs.runTypedLetReturnBody?_eq_of_mutual_extends forward backward owner fuel source.value.body store
        assertTrue ((inputs.runTypedLetReturnBody? base owner fuel source.value.body store).isNone &&
          (inputs.runTypedLetReturnBody? alternate owner fuel source.value.body store).isNone) "mutual dictionaries repaired whole rejection"
  let qualified ← parsed Syntax.Parser.typeExpr "Pkg /* exact components */ . Token"
  let .named name none := qualified.value | throw (IO.userError "qualified annotation changed shape")
  assertTrue (decide (qualifiedTypeNameKey name = ["Pkg", "Token"] ∧ interpretTypeName? base qualified = some (.namedData ⟨92⟩) ∧
    base.lookup? ["Pkg.Token"] = some .word ∧ alternate.lookup? ["Pkg", "Token"] = some (.namedData ⟨92⟩))) "qualified keys were flattened"
  let nominal ← parsed (Syntax.Parser.functionDecl .module) "function repair(x: Opaque) returns (Opaque){let z: Alias=x;return z;}"
  let nominalInputs ← declared nominal
  staticCheck nominalInputs nominal.value.body none
  assertTrue (decide (elaborateTypedLetReturnBody? extended owner nominalInputs nominal.value.body =
    some (.letE (.var 0) (.var 0), .namedData ⟨91⟩))) "new nominal meaning needed a fabricated actual value"
  let repaired ← parsed (Syntax.Parser.functionDecl .module) "function repair(x: Word) returns (Word){let z: WordAlias=x;return z;}"
  let fixed ← actual repaired [⟨.word, .word (word 9), .word⟩]
  staticCheck fixed.toTypeInputs repaired.value.body none
  assertTrue (decide (fixed.ids = [⟨owner, 0⟩] ∧ fixed.context.values = [.word] ∧ fixed.environment.values = [.word (word 9)] ∧
    fixed.checkTypedLetReturnBody? extended owner repaired.value.body = some (.letE (.var 0) (.var 0), .word) ∧
    typedLetReturnBodyFuelBound repaired.value.body = 4)) "repair changed fixed inputs or numerical cost"
  for store in stores do
    for fuel in List.range 7 do
      assertTrue ((fixed.runTypedLetReturnBody? base owner fuel repaired.value.body store).isNone &&
        expectedObservation (fixed.runTypedLetReturnBody? extended owner fuel repaired.value.body store) .word (.word (word 9)) store 4 fuel)
        "one-way extension incorrectly preserved none or changed repaired execution"
  let shadow : TypeNameTable := (["Word"], .bool) :: base
  have _ : ¬ TypeNameTable.Extends base shadow := by
    intro extension
    have impossible := (extension (show TypeNameTable.Lookup base ["Word"] .word from .head)).type_unique (show TypeNameTable.Lookup shadow ["Word"] .bool from .head)
    cases impossible
  have _ : ∀ row ∈ base, row ∈ shadow := fun _ member => List.mem_cons_of_mem _ member
  let shadowed ← parsed (Syntax.Parser.functionDecl .module) "function shadow(x: Word) returns (Word){let z: Word=x;return z;}"
  assertTrue (decide (fixed.checkTypedLetReturnBody? base owner shadowed.value.body = some (.letE (.var 0) (.var 0), .word) ∧
    fixed.checkTypedLetReturnBody? shadow owner shadowed.value.body = none ∧ fixed.context.values = [.word] ∧
    fixed.environment.values = [.word (word 9)] ∧ shadow.drop 1 = base)) "retaining dictionary rows was mistaken for first-match extension"
  let untouched ← parsed (Syntax.Parser.block .allow) "{return x;}"
  assertTrue (decide (fixed.checkTypedLetReturnBody? shadow owner untouched = some (.var 0, .word))) "changed dictionary silently redeclared the fixed input bundle"
  for store in stores do
    for fuel in List.range 7 do
      assertTrue ((fixed.runTypedLetReturnBody? shadow owner fuel shadowed.value.body store).isNone) "changed-head rejection was repaired by fuel"

end Tests
