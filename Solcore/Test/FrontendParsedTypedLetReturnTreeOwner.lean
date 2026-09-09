import Solcore.Syntax.Parser.Function
import Solcore.Frontend.TypedLetReturnTreeRunnerOwnerProperties
import Solcore.Frontend.TypedLetReturnTreeFuelBoundProperties
import Solcore.Frontend.TypedLetReturnTreeResumptionProperties
import Solcore.Frontend.TypedLetReturnTreeEmbeddingProperties
import Solcore.Frontend.RuntimeParameterDeclarationBindingProperties
import Solcore.Frontend.RuntimeFunctionEntry
import Solcore.Frontend.RuntimeFunctionCompilation

/-! Original parsed syntax and separately supplied Core build independent
provenance. Owner covariance retains actual values and full fixed-store states;
nominal entry compilation requires no inhabitants and keeps parameter-only rows. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TreeOwners", by decide⟩], by decide⟩⟩, 17⟩
private def shift (id : Resolved.DeclarationId) : Resolved.DeclarationId := { id with declarationIndex := id.declarationIndex + 11 }
private theorem shiftInjective : Function.Injective shift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := Nat.add_right_cancel (congrArg Resolved.DeclarationId.declarationIndex same)
  cases left; cases right; cases modules; cases indices; rfl
private theorem shiftNotSurjective : ¬ Function.Surjective shift := by
  intro onto
  obtain ⟨original, same⟩ := onto { owner with declarationIndex := 0 }
  have indices := congrArg Resolved.DeclarationId.declarationIndex same
  change original.declarationIndex + 11 = 0 at indices
  omega
private def mapping := ownerLocalIdMap shift
private theorem mappingInjective : Function.Injective mapping := ownerLocalIdMap_injective shift shiftInjective
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, .word (word n), .word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩),
  (["Pkg", "Token"], .namedData ⟨92⟩), (["FnOpaque"], .function .word (.namedData ⟨91⟩)), (["Opaque"], .bool)]
private def stores : List Core.Store := [[.word (word 91), .cellRef .word 40],
  [.closure .bool .bool (.var 0) [], .bool true, .word Core.Word.maximum]]
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-tree-owners.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError s!"function did not parse: {content}")
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd) "incomplete or diagnosed declaration"
  return source
private def declared (source : Syntax.FunctionDecl) : IO LocalTypeInputs := do
  let some inputs := declareRuntimeParameters? types owner source.value.signature.parameters.elements
    | throw (IO.userError "original value-free parameters rejected")
  return inputs
private def actual (source : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) : IO LocalInputs := do
  let static ← declared source
  match accepted : bindRuntimeParameters? types owner source.value.signature.parameters.elements arguments with
  | none => throw (IO.userError "actual typed arguments rejected")
  | some inputs =>
      have _ := (bindRuntimeParameters?_sound accepted).erase_values.complete
      assertTrue (decide (inputs.names = static.names ∧ inputs.context = static.context ∧
        inputs.environment.values = arguments.reverse.map (·.value))) "original parameter names/types or single argument reversal changed"
      return inputs

private structure Expression (inputs : LocalTypeInputs) (source : Syntax.Expr) (core : Core.Expr) (type : Core.Ty) where
  resolved : Resolved.Expr
  resolution : ResolvesLocalExpression inputs.names source resolved
  lowered : Resolved.Lowers inputs.ids resolved core
  typing : Resolved.HasType inputs.context resolved type
private def expression (inputs : LocalTypeInputs) (source : Syntax.Expr) (core : Core.Expr) (type : Core.Ty) :
    IO (Expression inputs source core type) := do
  match sourceAt : source, coreAt : core, typeAt : type with
  | ⟨_, .identifier name⟩, .var index, type =>
      match named : inputs.names.lookup? name.value with
      | none => throw (IO.userError "independent reference name missing")
      | some id =>
          if indexed : Resolved.LocalScope.index? inputs.ids id = some index then
            if typed : inputs.context.lookup? id = some type then
              return ⟨.var id, by rw [sourceAt]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
                by rw [coreAt]; exact .var (Resolved.LocalScope.index?_iff.mp indexed),
                by rw [typeAt]; exact .var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
            else throw (IO.userError "independent reference type differs")
          else throw (IO.userError "independent reference position differs")
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩, .binary .wordSub first second, .word =>
      let l ← expression inputs left first .word
      let r ← expression inputs right second .word
      return ⟨.binary .wordSub l.resolved r.resolved, by rw [sourceAt]; exact .subtract l.resolution r.resolution,
        by rw [coreAt]; exact .binary l.lowered r.lowered,
        by rw [typeAt]; exact .binary l.typing r.typing⟩
  | _, _, _ => throw (IO.userError "expression differs from independent fixture Core")
termination_by sizeOf source
private structure Evidence (inputs : LocalTypeInputs) (body : Syntax.Block) (core : Core.Expr) (type : Core.Ty) : Type where
  elaboration : TypedLetReturnTreeElaborates types owner inputs body core type
private def certify (inputs : LocalTypeInputs) (body : Syntax.Block) (core : Core.Expr) (type : Core.Ty)
    (nextIndex : Nat) : IO (Evidence inputs body core type) := do
  match sourceAt : body, coreAt : core, typeAt : type with
  | ⟨_, [⟨_, .returnStmt none⟩]⟩, .unit, .unit => return ⟨by rw [sourceAt, coreAt, typeAt]; exact .single .bare⟩
  | ⟨_, [⟨_, .returnStmt (some source)⟩]⟩, core, type =>
      let child ← expression inputs source core type
      return ⟨by rw [sourceAt, coreAt, typeAt]; exact .single (.expression child.resolution
        (by simpa only [LocalTypeInputs.context_ids] using child.lowered) child.typing)⟩
  | ⟨blockSpan, ⟨_, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩, .letE initial tail, type =>
      match meaning : interpretTypeName? types annotation with
      | none => throw (IO.userError "written annotation has no meaning")
      | some declaredType =>
          if unused : name.value ∉ inputs.names.map Prod.fst then
            let child ← expression inputs initializer initial declaredType
            let extended := inputs.bindFresh owner name.value declaredType
            let mapped := inputs.mapIds mapping mappingInjective
            have _ := inputs.bindFresh_mapOwner owner shift shiftInjective name.value declaredType
            assertTrue (decide (extended.ids = (⟨owner, nextIndex⟩ : Resolved.LocalId) :: inputs.ids ∧
              (mapped.bindFresh (shift owner) name.value declaredType).ids =
                (⟨shift owner, nextIndex⟩ : Resolved.LocalId) :: mapped.ids)) "fresh index used length or a sibling allocation"
            let childTail ← certify extended ⟨blockSpan, rest⟩ tail type (nextIndex + 1)
            return ⟨by
              rw [sourceAt, coreAt, typeAt]
              exact .binding (interpretTypeName?_sound meaning).structural unused
                child.resolution child.lowered child.typing childTail.elaboration⟩
          else throw (IO.userError "independent binding reused a name")
  | ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩, .letE initial tail, type =>
      let .identifier originalName := initializer.value | throw (IO.userError "inferred fixture expected original reference")
      let some inferredType := (inputs.names.lookup? originalName.value).bind inputs.context.lookup?
        | throw (IO.userError "original reference type missing")
      if unused : name.value ∉ inputs.names.map Prod.fst then
        let child ← expression inputs initializer initial inferredType
        let extended := inputs.bindFresh owner name.value inferredType
        assertTrue (blockSpan.contains letSpan && letSpan.contains name.span && letSpan.contains initializer.span &&
          decide (name.span.endByte ≤ initializer.span.startByte ∧ extended.context = (⟨owner, nextIndex⟩, inferredType) :: inputs.context) &&
          (elaborateTypedLetReturnBody? types owner inputs body).isNone) "inferred annotation/span/fresh type or old prefix changed"
        let childTail ← certify extended ⟨blockSpan, rest⟩ tail type (nextIndex + 1)
        return ⟨by rw [sourceAt, coreAt, typeAt]; exact .inferred unused child.resolution child.lowered child.typing childTail.elaboration⟩
      else throw (IO.userError "independent inference reused a name")
  | ⟨_, [⟨_, .ifThen condition left (some right)⟩]⟩, .ifE guard first second, type =>
      let child ← expression inputs condition guard .bool
      let l ← certify inputs left first type nextIndex
      let r ← certify inputs right second type nextIndex
      return ⟨by rw [sourceAt, coreAt, typeAt]; exact .conditional child.resolution child.lowered child.typing l.elaboration r.elaboration⟩
  | _, _, _ => throw (IO.userError "original tree differs from independent fixture Core")
termination_by sizeOf body
private def checkedStatic (inputs : LocalTypeInputs) (body : Syntax.Block) (core : Core.Expr) (type : Core.Ty)
    (nextIndex : Nat) : IO Unit := do
  let proof ← certify inputs body core type nextIndex
  have _ := proof.elaboration.mapOwner shift shiftInjective
  have _ := proof.elaboration.hasType.mapOwner shift shiftInjective
  have _ := elaborateTypedLetReturnTree?_mapOwner shift shiftInjective types owner inputs body
  let mapped := inputs.mapIds mapping mappingInjective
  assertTrue (decide (elaborateTypedLetReturnTree? types owner inputs body = some (core, type) ∧
    elaborateTypedLetReturnTree? types (shift owner) mapped body = some (core, type) ∧ Core.infer? inputs.context.values core = some type ∧
    mapped.names.map Prod.fst = inputs.names.map Prod.fst ∧ mapped.context.values = inputs.context.values ∧
    mapped.ids = inputs.ids.map mapping ∧ mapped.ids.map (·.binderIndex) = inputs.ids.map (·.binderIndex))) "static owner change altered exact source/Core/rows"
private def runChecked (inputs : LocalInputs) (body : Syntax.Block) (core : Core.Expr) (type : Core.Ty)
    (value : Core.Value) (cost bound nextIndex : Nat) : IO Unit := do
  checkedStatic inputs.toTypeInputs body core type nextIndex
  let mapped := inputs.mapIds mapping mappingInjective
  have _ := inputs.checkTypedLetReturnTree?_mapOwner shift shiftInjective types owner body
  assertTrue (decide (mapped.environment.values = inputs.environment.values ∧ mapped.ids ≠ inputs.ids ∧
    mapped.checkTypedLetReturnTree? types (shift owner) body = some (core, type) ∧ typedLetReturnTreeFuelBound body = bound)) "actual values or bound changed"
  for store in stores do
    let run := fun fuel => inputs.runTypedLetReturnTree? types owner fuel body store
    let renamed := fun fuel => mapped.runTypedLetReturnTree? types (shift owner) fuel body store
    for fuel in List.range (bound + 3) do
      have _ := inputs.runTypedLetReturnTree?_mapOwner shift shiftInjective types owner fuel body store
      assertTrue (decide (renamed fuel = run fuel ∧ run fuel = some (type, Core.runStateful fuel (.initial core inputs.environment.values store))))
        "full same-fuel owner result changed the independent Core or actual positional values"
      if cost ≤ fuel then assertTrue (decide (run fuel = some (type, .done value store))) "independent value/cost changed"
      else
        match original : run fuel, shifted : renamed fuel with
        | some (t, .outOfFuel state), some (u, .outOfFuel shiftedState) =>
            assertTrue (decide (t = type ∧ u = type ∧ state = shiftedState ∧ state.store = store)) "genuine checkpoint differed"
            for remaining in List.range (cost - fuel + 3) do
              have _ := LocalInputs.runTypedLetReturnTree?_resume original remaining
              have _ := LocalInputs.runTypedLetReturnTree?_resume shifted remaining
              assertTrue (decide (run (fuel + remaining) = some (type, Core.runStateful remaining state) ∧
                renamed (fuel + remaining) = some (type, Core.runStateful remaining shiftedState))) "resumption rebuilt values or frames"
            assertTrue (decide (Core.runStateful (cost - fuel) state = .done value store)) "actual residual lost expected value"
            if 0 < fuel then assertTrue (decide (run (cost - fuel) ≠ some (type, .done value store))) "restart became checkpoint resumption"
        | _, _ => throw (IO.userError "actual below-cost checkpoint missing")
private def alternating (depth level : Nat) (annotation : String) : String × Core.Expr :=
  match depth with
  | 0 => ("return " ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";", .var (if level = 0 then 2 else 0))
  | count + 1 =>
      let (tail, core) := alternating count (level + 1) annotation
      ("if(c){" ++ s!"let z{level}: {annotation}=" ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";" ++ tail ++
        "}else{" ++ s!"let z{level}: {annotation}=y;return z{level};" ++ "}",
        .ifE (.var level) (.letE (.var (if level = 0 then 2 else 0)) core) (.letE (.var (level + 1)) (.var 0)))
private def fixture (content : String) (arguments : List TypedRuntimeArgument) (core : Core.Expr)
    (expected : TypedRuntimeArgument) (cost bound : Nat) : IO Unit := do
  let source ← parsed content
  let inputs ← actual source arguments
  assertTrue (decide (interpretRuntimeFunctionHeader? types source.value.signature = some expected.type) &&
    (elaborateTypedLetReturnBody? types owner inputs.toTypeInputs source.value.body).isNone) "header or old prefix boundary changed"
  for chosenOwner in [owner, shift owner] do
    let names := if chosenOwner = owner then inputs.names else (inputs.mapIds mapping mappingInjective).names
    assertTrue (decide ((compileRuntimeFunction? types chosenOwner source).map (fun c => (c.core, c.returnType, c.inputs.names, c.inputs.context.values)) =
      some (core, expected.type, names, inputs.context.values)) && (prepareRuntimeFunction? types chosenOwner source arguments).any (fun p =>
        decide (p.core = core ∧ p.returnType = expected.type ∧ p.inputs.names = names ∧ p.inputs.context.values = inputs.context.values ∧
          p.inputs.environment.values = arguments.reverse.map (·.value)))) "owner changed exact compilation or actual parameter rows"
    for store in stores do
      for fuel in List.range (bound + 3) do
        assertTrue (decide (runRuntimeFunction? types chosenOwner source arguments fuel store =
          some (expected.type, Core.runStateful fuel (.initial core inputs.environment.values store)))) "owner changed the full entry result or checkpoint"
  runChecked inputs source.value.body core expected.type expected.value cost bound arguments.length

def frontendParsedTypedLetReturnTreeOwnerTests : IO Unit := do
  have _ := shiftNotSurjective
  have _ (id : Core.DataTypeId) : ¬ ∃ value, Core.ValueHasType value (.namedData id) := by
    rintro ⟨value, typed⟩
    cases typed with
    | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
  for (annotation, type) in [("Opaque", Core.Ty.namedData ⟨91⟩), ("Pkg.Token", .namedData ⟨92⟩), ("FnOpaque", .function .word (.namedData ⟨91⟩))] do
    for depth in [1, 2, 5, 12] do
      let (body, core) := alternating depth 0 annotation
      let source ← parsed (s!"function nominal(x: {annotation},y: {annotation},c: Bool) returns ({annotation})" ++ "{" ++ body ++ "}")
      let inputs ← declared source
      checkedStatic inputs source.value.body core type 3
      for chosenOwner in [owner, shift owner] do
        let names := if chosenOwner = owner then inputs.names else (inputs.mapIds mapping mappingInjective).names
        assertTrue (decide (interpretRuntimeFunctionHeader? types source.value.signature = some type ∧
          (compileRuntimeFunction? types chosenOwner source).map (fun c => (c.core, c.returnType, c.inputs.names, c.inputs.context.values)) =
            some (core, type, names, inputs.context.values))) "nominal owner compilation changed exact Core or demanded an inhabitant"
  let left : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩
  let right : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  for (annotation, x, y) in [("Word", wordArg 9, wordArg 2), ("Cell", ⟨.cell .word, .cellRef .word 17, .cellRef⟩, ⟨.cell .word, .cellRef .word 29, .cellRef⟩),
      ("Fn", left, right), ("Bool", boolArg false, boolArg true)] do
    for depth in [1, 2, 5] do
      let (body, core) := alternating depth 0 annotation
      for c in [false, true] do
        fixture (s!"function recursive(x: {annotation},y: {annotation},c: Bool) returns ({annotation})" ++ "{" ++ body ++ "}")
          [x, y, boolArg c] core (if c then x else y) (if c then 6 * depth + 1 else 7) (6 * depth + 1)
  for (x, y) in [(9, 2), (2, 9), (0, Core.Word.maximum.val)] do
    for c in [false, true] do
      for d in [false, true] do
        fixture "function ordered(c: Bool,d: Bool,x: Word,y: Word) returns (Word){if(c){let z: Word=x - y;if(d){let w: Word=z;return w;}else{let w: Word=y - z;return w;}}else{let z: Word=y - x;return y;}}"
          [boolArg c, boolArg d, wordArg x, wordArg y] (.ifE (.var 3)
            (.letE (.binary .wordSub (.var 1) (.var 0)) (.ifE (.var 3) (.letE (.var 0) (.var 0))
              (.letE (.binary .wordSub (.var 1) (.var 0)) (.var 0)))) (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 1)))
          ⟨.word, .word (if c then if d then (word x).sub (word y) else (word y).sub ((word x).sub (word y)) else word y), .word⟩
          (if c then if d then 17 else 21 else 11) 21
  for c in [false, true] do
    fixture "function siblings(x: Word,c: Bool){if(c){let z: Word=x;return;}else{let z: Bool=c;return;}}"
      [wordArg 9, boolArg c] (.ifE (.var 0) (.letE (.var 1) .unit) (.letE (.var 0) .unit)) ⟨.unit, .unit, .unit⟩ 7 7
  let source ← parsed "function sparse(x: Word,y: Word,c: Bool) returns (Word){if(c){let z: Word=x;return z;}else{let z: Word=y;return z;}}"
  let mixed : LocalInputs := ⟨[⟨"c", ⟨owner, 2⟩, .bool, .bool true, .bool⟩,
    ⟨"y", ⟨shift owner, 999⟩, .word, .word (word 2), .word⟩, ⟨"x", ⟨owner, 7⟩, .word, .word (word 9), .word⟩], by decide⟩
  let ordinary ← actual source [wordArg 9, wordArg 2, boolArg true]
  assertTrue (decide (mixed.names.map Prod.fst = ordinary.names.map Prod.fst ∧ mixed.context.values = ordinary.context.values ∧
    mixed.environment.values = ordinary.environment.values)) "sparse IDs changed original parsed argument positions"
  let expected := Core.Expr.ifE (.var 0) (.letE (.var 2) (.var 0)) (.letE (.var 1) (.var 0))
  runChecked mixed source.value.body expected .word (.word (word 9)) 7 7 8
  for store in stores do
    let env := mixed.environment.values
    let run := fun fuel => mixed.runTypedLetReturnTree? types owner fuel source.value.body store
    for (fuel, state) in [(1, (⟨.eval (.var 0) env, [.ifBranches (.letE (.var 2) (.var 0)) (.letE (.var 1) (.var 0)) env], store⟩ : Core.State)),
        (4, ⟨.eval (.var 2) env, [.letBody (.var 0) env], store⟩), (5, ⟨.ret (.word (word 9)), [.letBody (.var 0) env], store⟩),
        (6, ⟨.eval (.var 0) (.word (word 9) :: env), [], store⟩)] do
      assertTrue (decide (run fuel = some (.word, .outOfFuel state))) "independent if/initializer/captured-value/tail checkpoint changed"
  let rawIds := mixed.ids ++ [⟨owner, 7⟩]
  have _ := Resolved.freshLocalId_map_owner shift shiftInjective owner rawIds
  let indexShift := fun id : Resolved.LocalId => { id with binderIndex := id.binderIndex + 1 }
  have _ : Function.Injective indexShift := by
    intro left right same
    have owners := congrArg Resolved.LocalId.owner same
    have indices := Nat.add_right_cancel (congrArg Resolved.LocalId.binderIndex same)
    cases left; cases right; cases owners; cases indices; rfl
  assertTrue (decide (Resolved.freshLocalId owner rawIds = ⟨owner, 8⟩ ∧
    Resolved.freshLocalId (shift owner) (rawIds.map mapping) = ⟨shift owner, 8⟩ ∧
    Resolved.freshLocalId owner (([] : List Resolved.LocalId).map indexShift) ≠ indexShift (Resolved.freshLocalId owner []) ∧
    Resolved.freshLocalId owner (rawIds.map (ownerLocalIdMap (fun _ => owner))) ≠
      ownerLocalIdMap (fun _ => owner) (Resolved.freshLocalId owner rawIds))) "inadmissible allocator mapping was silently generalized"
  for c in [false, true] do
    fixture "function rejected(x: Word,y: Word,c: Bool) returns (Word){if(c){let z=x;return z;}else{return y;}}"
      [wordArg 9, wordArg 2, boolArg c] (.ifE (.var 0) (.letE (.var 2) (.var 0)) (.var 1)) (wordArg (if c then 9 else 2)) (if c then 7 else 4) 7
  for body in ["{if(c){let z: Word=x;return z;}else{let z: Unknown=y;return z;}}",
      "{if(c){let z: Word=x;return z;}else{let z: Bool=y;return y;}}", "{if(c){let x: Word=y;return x;}else{return y;}}",
      "{if(c){let z: Word=z;return x;}else{return y;}}", "{if(c){return x;}else{return z;}}",
      "{if(c){let z: Word;return x;}else{return y;}}",
      "{if(c){let z: Word=x;return z;}else{if(c){return y;}else{return missing;}}}",
      "{if(c){return x;}else{return c;}}", "{if(x){return x;}else{return y;}}", "{if(c){return x;}}", "{return x;return y;}", "{}"] do
    let source ← parsed ("function rejected(x: Word,y: Word,c: Bool) returns (Word)" ++ body)
    let inputs ← actual source [wordArg 9, wordArg 2, boolArg true]
    let mapped := inputs.mapIds mapping mappingInjective
    have _ := elaborateTypedLetReturnTree?_mapOwner shift shiftInjective types owner inputs.toTypeInputs source.value.body
    have _ := inputs.checkTypedLetReturnTree?_mapOwner shift shiftInjective types owner source.value.body
    assertTrue ((inputs.checkTypedLetReturnTree? types owner source.value.body).isNone &&
      (mapped.checkTypedLetReturnTree? types (shift owner) source.value.body).isNone) "owner map repaired whole rejection"
    for store in stores do
      for fuel in List.range (typedLetReturnTreeFuelBound source.value.body + 3) do
        have _ := inputs.runTypedLetReturnTree?_mapOwner shift shiftInjective types owner fuel source.value.body store
        assertTrue ((inputs.runTypedLetReturnTree? types owner fuel source.value.body store).isNone &&
          (mapped.runTypedLetReturnTree? types (shift owner) fuel source.value.body store).isNone) "owner/fuel repaired rejected source"

end Tests
