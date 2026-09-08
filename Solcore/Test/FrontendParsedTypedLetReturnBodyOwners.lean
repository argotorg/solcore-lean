import Solcore.Syntax.Parser.Function
import Solcore.Frontend.TypedLetReturnBodyRunnerOwnerProperties
import Solcore.Frontend.TypedLetReturnBodyFuelBoundProperties
import Solcore.Frontend.TypedLetReturnBodyResumptionProperties
import Solcore.Frontend.RuntimeParameterDeclarationBindingProperties
import Solcore.Frontend.RuntimeFunctionCompilation
import Solcore.Frontend.RuntimeFunctionEntry

/-! Owner-only allocation changes actual IDs, not the parsed source, original
scope positions or full fixed-store checkpoints. Nominal cases remain value-free. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"PrefixOwners", by decide⟩], by decide⟩⟩, 17⟩
private def shift (id : Resolved.DeclarationId) : Resolved.DeclarationId :=
  { id with declarationIndex := id.declarationIndex + 11 }
private theorem shiftInjective : Function.Injective shift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := congrArg Resolved.DeclarationId.declarationIndex same
  change left.declarationIndex + 11 = right.declarationIndex + 11 at indices
  have original := Nat.add_right_cancel indices
  cases left; cases right; simp_all [shift]
private theorem shiftNotSurjective : ¬ Function.Surjective shift := by
  intro surjective
  obtain ⟨original, same⟩ := surjective { owner with declarationIndex := 0 }
  have indices := congrArg Resolved.DeclarationId.declarationIndex same
  change original.declarationIndex + 11 = 0 at indices
  omega
private def mapping := ownerLocalIdMap shift
private theorem mappingInjective : Function.Injective mapping := ownerLocalIdMap_injective shift shiftInjective
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩),
  (["Alias"], .namedData ⟨91⟩), (["Pkg", "Token"], .namedData ⟨92⟩),
  (["FnOpaque"], .function .word (.namedData ⟨91⟩)), (["Opaque"], .bool)]
private def stores : List Core.Store := [[.word (word 91), .cellRef .word 40],
  [.closure .bool .bool (.var 0) [], .bool true, .word Core.Word.maximum]]
private def parsed {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO α := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-prefix-owners.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  let .ok source next := parser (Syntax.Parser.State.initial file lexed) | throw (IO.userError s!"fixture did not parse: {content}")
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd) "incomplete or diagnosed source"
  return source
private def declared (source : Syntax.FunctionDecl) : IO LocalTypeInputs := do
  let parameters := source.value.signature.parameters.elements
  match accepted : declareRuntimeParameters? types owner parameters with
  | none => throw (IO.userError "value-free source parameters did not declare")
  | some inputs =>
      have _ := declareRuntimeParameters?_sound accepted
      let rows := parameters.filterMap fun parameter => match parameter.value with
        | .typed none name annotation => (interpretTypeName? types annotation).map (name.value, ·)
        | _ => none
      assertTrue (decide (rows.length = parameters.length ∧ inputs.names.map Prod.fst = (rows.map Prod.fst).reverse ∧
        inputs.context.values = (rows.map Prod.snd).reverse ∧ inputs.ids =
          (List.range parameters.length).reverse.map (fun index => (⟨owner, index⟩ : Resolved.LocalId)))) "declaration changed original source rows"
      return inputs

private def relabeled (inputs : LocalTypeInputs) (body : Syntax.Block) : IO LocalTypeInputs := do
  let mapped := inputs.mapIds mapping mappingInjective
  have _ := elaborateTypedLetReturnBody?_mapOwner shift shiftInjective types owner inputs body
  assertTrue (decide (mapped.ids = inputs.ids.map mapping ∧ mapped.ids.map (·.binderIndex) = inputs.ids.map (·.binderIndex) ∧
    mapped.names.map Prod.fst = inputs.names.map Prod.fst ∧ mapped.context.values = inputs.context.values ∧
    elaborateTypedLetReturnBody? types (shift owner) mapped body = elaborateTypedLetReturnBody? types owner inputs body))
    "owner relabeling changed names, index positions, type rows or complete optional checking"
  if !inputs.bindings.isEmpty then assertTrue (decide (mapped.ids ≠ inputs.ids)) "nontrivial owner shift left IDs unchanged"
  match checked : elaborateTypedLetReturnBody? types owner inputs body with
  | none => pure ()
  | some _ =>
      have _ := (elaborateTypedLetReturnBody?_elaborates checked).mapOwner shift shiftInjective
      have _ := (elaborateTypedLetReturnBody?_sound checked).mapOwner shift shiftInjective
      pure ()
  return mapped
private def inspect (inputs : LocalTypeInputs) (body : Syntax.Block) (core : Core.Expr)
    (type : Core.Ty) (nextIndex : Nat) : IO Unit := do
  match body, core with
  | ⟨blockSpan, ⟨_, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩, .letE initial tail =>
      let some boundType := interpretTypeName? types annotation | throw (IO.userError "lost annotation meaning")
      let mapped := inputs.mapIds mapping mappingInjective
      let extended := inputs.bindFresh owner name.value boundType
      let extendedMapped := mapped.bindFresh (shift owner) name.value boundType
      have _ := Resolved.freshLocalId_map_owner shift shiftInjective owner inputs.ids
      have _ := inputs.bindFresh_mapOwner owner shift shiftInjective name.value boundType
      assertTrue (decide (Resolved.freshLocalId owner inputs.ids = ⟨owner, nextIndex⟩ ∧
        Resolved.freshLocalId (shift owner) mapped.ids = ⟨shift owner, nextIndex⟩ ∧
        extendedMapped.ids = extended.ids.map mapping ∧ extendedMapped.context.values = extended.context.values ∧
        extendedMapped.names.map Prod.fst = extended.names.map Prod.fst ∧
        elaborateLocalExpression? inputs.names inputs.context initializer = some (initial, boundType) ∧
        elaborateLocalExpression? mapped.names mapped.context initializer = some (initial, boundType) ∧
        elaborateTypedLetReturnBody? types owner extended ⟨blockSpan, rest⟩ = some (tail, type) ∧
        elaborateTypedLetReturnBody? types (shift owner) extendedMapped ⟨blockSpan, rest⟩ = some (tail, type)))
        "fresh identity, original initializer scope or extended tail order changed"
      inspect extended ⟨blockSpan, rest⟩ tail type (nextIndex + 1)
  | _, _ =>
      assertTrue (decide (elaborateTerminalReturnTree? inputs.names inputs.context body = some (core, type)))
        "independent ordered Core did not end in the actual terminal tree"
termination_by body.value.length
private def checkedStatic (inputs : LocalTypeInputs) (body : Syntax.Block) (core : Core.Expr)
    (type : Core.Ty) (bound nextIndex : Nat) : IO Unit := do
  let mapped ← relabeled inputs body
  assertTrue (decide (elaborateTypedLetReturnBody? types owner inputs body = some (core, type) ∧
    elaborateTypedLetReturnBody? types (shift owner) mapped body = some (core, type) ∧
    Core.infer? inputs.context.values core = some type ∧ typedLetReturnBodyFuelBound body = bound))
    "independent Core, type or source-only bound changed"
  inspect inputs body core type nextIndex

private def runChecked (inputs : LocalInputs) (body : Syntax.Block) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost bound nextIndex : Nat) : IO Unit := do
  checkedStatic inputs.toTypeInputs body core type bound nextIndex
  let mapped := inputs.mapIds mapping mappingInjective
  have _ := inputs.checkTypedLetReturnBody?_mapOwner shift shiftInjective types owner body
  assertTrue (decide (mapped.ids = inputs.ids.map mapping ∧ mapped.environment.values = inputs.environment.values ∧
    mapped.context.values = inputs.context.values ∧ mapped.names.map Prod.fst = inputs.names.map Prod.fst ∧
    mapped.checkTypedLetReturnBody? types (shift owner) body = some (core, type))) "actual values or checked Core changed"
  for store in stores do
    let run := fun fuel => inputs.runTypedLetReturnBody? types owner fuel body store
    let shiftedRun := fun fuel => mapped.runTypedLetReturnBody? types (shift owner) fuel body store
    match core with
    | .letE initializer tail =>
        let expected : Core.State := ⟨.eval initializer inputs.environment.values, [.letBody tail inputs.environment.values], store⟩
        assertTrue (decide (run 1 = some (type, .outOfFuel expected) ∧ shiftedRun 1 = some (type, .outOfFuel expected)))
          "initial pending let frame did not retain the original actual values"
    | _ => pure ()
    for fuel in List.range (bound + 3) do
      have _ := inputs.runTypedLetReturnBody?_mapOwner shift shiftInjective types owner fuel body store
      assertTrue (decide (shiftedRun fuel = run fuel ∧
        run fuel = some (type, Core.runStateful fuel (.initial core inputs.environment.values store))))
        "owner covariance lost a complete same-fuel result"
      if cost ≤ fuel then
        assertTrue (decide (run fuel = some (type, .done value store))) "independent completion value or cost changed"
      else
        match original : run fuel, renamed : shiftedRun fuel with
        | some (originalType, .outOfFuel checkpoint), some (mappedType, .outOfFuel mappedCheckpoint) =>
            assertTrue (decide (originalType = type ∧ mappedType = type ∧ checkpoint = mappedCheckpoint ∧ checkpoint.store = store))
              "owner shift changed a genuine full checkpoint"
            for remaining in List.range (cost - fuel + 3) do
              have _ := LocalInputs.runTypedLetReturnBody?_resume original remaining
              have _ := LocalInputs.runTypedLetReturnBody?_resume renamed remaining
              assertTrue (decide (run (fuel + remaining) = some (type, Core.runStateful remaining checkpoint) ∧
                shiftedRun (fuel + remaining) = some (type, Core.runStateful remaining mappedCheckpoint) ∧
                Core.runStateful remaining checkpoint = Core.runStateful remaining mappedCheckpoint)) "genuine resumption rebuilt or changed a frame"
            assertTrue (decide (Core.runStateful (cost - fuel) checkpoint = .done value store)) "actual residual did not reach the independent expected value"
        | _, _ => throw (IO.userError "below-cost actual checkpoint disappeared")
private def actual (source : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) : IO LocalInputs := do
  let static ← declared source
  match accepted : bindRuntimeParameters? types owner source.value.signature.parameters.elements arguments with
  | none => throw (IO.userError "actual arguments did not bind")
  | some inputs =>
      have _ := (bindRuntimeParameters?_sound accepted).erase_values.complete
      assertTrue (decide (inputs.environment.values = (arguments.map (·.value)).reverse ∧
        inputs.names = static.names ∧ inputs.context = static.context)) "actual argument order disagreed with value-free declaration"
      return inputs
private def fixture (content : String) (arguments : List TypedRuntimeArgument) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost bound : Nat) : IO Unit := do
  let source ← parsed (Syntax.Parser.functionDecl .module) content
  let inputs ← actual source arguments
  assertTrue (decide (interpretRuntimeFunctionHeader? types source.value.signature = some type)) "body contrast used an invalid header"
  runChecked inputs source.value.body core type value cost bound arguments.length
  for (selectedOwner, expectedIds) in [(owner, inputs.ids), (shift owner, inputs.ids.map mapping)] do
    assertTrue (decide ((compileRuntimeFunction? types selectedOwner source).map (fun compiled =>
      (compiled.core, compiled.returnType, compiled.inputs.ids, compiled.inputs.context.values, compiled.inputs.names.map Prod.fst)) =
        some (core, type, expectedIds, inputs.context.values, inputs.names.map Prod.fst))) "entry owner change altered Core or parameter-only rows"
    for store in stores do
      for fuel in List.range (bound + 3) do
        assertTrue (decide (runRuntimeFunction? types selectedOwner source arguments fuel store =
          inputs.runTypedLetReturnBody? types owner fuel source.value.body store)) "entry owner change altered complete body execution"

def frontendParsedTypedLetReturnBodyOwnerTests : IO Unit := do
  have _ := shiftNotSurjective
  have _ (id : Core.DataTypeId) : ¬ ∃ value, Core.ValueHasType value (.namedData id) := by
    rintro ⟨value, typed⟩
    cases typed with
    | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
  for (annotation, type) in [("Opaque", Core.Ty.namedData ⟨91⟩), ("Pkg.Token", .namedData ⟨92⟩), ("FnOpaque", .function .word (.namedData ⟨91⟩))] do
    for count in [0, 1, 2, 5, 12] do
      let indices := List.range count
      let declarations := String.join (indices.map fun index => s!"let z{index}: {annotation}=" ++ (if index = 0 then "x" else s!"z{index - 1}") ++ ";")
      let selected := if count = 0 then "x" else s!"z{count - 1}"
      let source ← parsed (Syntax.Parser.functionDecl .module) (s!"function nominal(x: {annotation},y: {annotation},c: Bool) returns ({annotation})" ++
        "{" ++ declarations ++ "if(c){if(c){return " ++ selected ++ ";}else{return y;}}else{return x;}}")
      let inputs ← declared source
      let terminal := Core.Expr.ifE (.var count) (.ifE (.var count) (.var (if count = 0 then 2 else 0)) (.var (count + 1))) (.var (count + 2))
      let core := indices.foldr (fun index tail => Core.Expr.letE (.var (if index = 0 then 2 else 0)) tail) terminal
      checkedStatic inputs source.value.body core type (3 * count + 7) 3
      assertTrue (decide (interpretRuntimeFunctionHeader? types source.value.signature = some type)) "nominal header meaning changed"
      assertTrue (decide ((compileRuntimeFunction? types owner source).map (fun compiled =>
        (compiled.core, compiled.returnType, compiled.inputs.names, compiled.inputs.context.values)) =
          some (core, type, inputs.names, inputs.context.values))) "nominal compilation needed values or changed its original parameter rows"
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
  fixture "function emptyScope() returns (Word){let z: Word=7;return z;}" [] (.letE (.word (word 7)) (.var 0)) .word (.word (word 7)) 4 4
  let mixed : LocalInputs := ⟨[⟨"r", ⟨shift owner, 500⟩, .word, .word (word 2), .word⟩,
    ⟨"x", ⟨owner, 4⟩, .word, .word (word 9), .word⟩, ⟨"c", ⟨owner, 40⟩, .bool, .bool true, .bool⟩], by decide⟩
  let mixedBody ← parsed (Syntax.Parser.block .allow) "{let y: Word=x;let z: Word=y - r;return z;}"
  assertTrue (decide (mixed.environment.values = [.word (word 2), .word (word 9), .bool true])) "mixed-owner fixture lost its independent actual order"
  let repeated := mixed.ids ++ [⟨owner, 40⟩, ⟨shift owner, 900⟩]
  have _ := Resolved.freshLocalId_map_owner shift shiftInjective owner repeated
  assertTrue (decide (Resolved.freshLocalId owner repeated = ⟨owner, 41⟩ ∧
    Resolved.freshLocalId (shift owner) (repeated.map mapping) = ⟨shift owner, 41⟩)) "other owners, sparse indices or repeated raw IDs changed fresh allocation"
  runChecked mixed mixedBody (.letE (.var 1) (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 0))) .word (.word (word 7)) 11 11 41
  for body in ["{let z: Unknown=x;return z;}", "{let z: Bool=x;return z;}", "{let x: Word=r;return x;}",
      "{let z: Word=x;let z: Word=r;return z;}", "{let z=x;return z;}", "{let z: Word;return x;}",
      "{let z: Word=z;return x;}", "{let y: Word=z;let z: Word=x;return y;}",
      "{let z: Word=missing;return x;}", "{let z: Word=x();return x;}",
      "{let z: Word=x;if(c){if(c){return z;}else{return missing;}}else{return x;}}",
      "{let z: Word=x;if(c){return z;}else{return c;}}", "{let z: Word=x;if(x){return z;}else{return r;}}",
      "{let z: Word=x;if(c){return z;}}", "{let z: Word=x;if(c){let y: Word=z;return y;}else{return r;}}",
      "{let z: Word=x;return z;return x;}", "{}"] do
    let source ← parsed (Syntax.Parser.functionDecl .module) ("function rejected(x: Word,r: Word,c: Bool) returns (Word)" ++ body)
    let inputs ← actual source [⟨.word, .word (word 9), .word⟩, ⟨.word, .word (word 2), .word⟩, ⟨.bool, .bool true, .bool⟩]
    let _ ← relabeled inputs.toTypeInputs source.value.body
    let mapped := inputs.mapIds mapping mappingInjective
    have _ := inputs.checkTypedLetReturnBody?_mapOwner shift shiftInjective types owner source.value.body
    assertTrue ((inputs.checkTypedLetReturnBody? types owner source.value.body).isNone &&
      (mapped.checkTypedLetReturnBody? types (shift owner) source.value.body).isNone) "owner change repaired whole rejection"
    for store in stores do
      for fuel in List.range (typedLetReturnBodyFuelBound source.value.body + 3) do
        have _ := inputs.runTypedLetReturnBody?_mapOwner shift shiftInjective types owner fuel source.value.body store
        assertTrue ((inputs.runTypedLetReturnBody? types owner fuel source.value.body store).isNone &&
          (mapped.runTypedLetReturnBody? types (shift owner) fuel source.value.body store).isNone) "non-surjective owner relabeling or fuel repaired a rejected body"

end Tests
