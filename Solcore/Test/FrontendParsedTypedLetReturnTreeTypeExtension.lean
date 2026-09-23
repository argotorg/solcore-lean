import Solcore.Syntax.Parser.Function
import Solcore.Frontend.TypedLetReturnTree
import Solcore.Frontend.RuntimeParameterDeclarations
import Solcore.Frontend.RuntimeFunction
/-! Independent original-syntax provenance meets semantic dictionary extension.
Inputs are bound once under the original table. Whole rejection is preserved only
mutually; a repaired unselected annotation need not change the raw selected path. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TreeTypes", by decide⟩], by decide⟩⟩, 17⟩
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, .word (word n), .word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def base : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩),
  (["Pkg", "Token"], .namedData ⟨92⟩), (["Pkg.Token"], .word), (["Word"], .bool)]
private def alternate : TypeNameTable := ((["Word"], .word) :: base) ++ [(["Opaque"], .word)]
private def extras : TypeNameTable := [(["WordAlias"], .word), (["Alias"], .namedData ⟨91⟩), (["Word"], .bool)]
private def extended := base ++ extras
private theorem sameLookup (key : List String) : base.lookup? key = alternate.lookup? key := by
  by_cases w : ["Word"] = key
  · subst key; rfl
  by_cases o : ["Opaque"] = key
  · subst key; rfl
  simp [base, alternate, TypeNameTable.lookup?, w, o]
private theorem fromLookup {old next : TypeNameTable}
    (same : ∀ key, old.lookup? key = next.lookup? key) : TypeNameTable.Extends old next := by
  intro key type found
  exact TypeNameTable.lookup?_iff.mp ((same key).symm.trans (TypeNameTable.lookup?_iff.mpr found))
private theorem forward : TypeNameTable.Extends base alternate := fromLookup sameLookup
private theorem backward : TypeNameTable.Extends alternate base := fromLookup (fun key => (sameLookup key).symm)
private theorem grows : TypeNameTable.Extends base extended := TypeNameTable.Extends.append_right base extras
private def stores : List Core.Store := [[.word (word 91), .cellRef .word 40], [.closure .bool .bool (.var 0) [], .bool true, .word Core.Word.maximum]]
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-tree-type-extension.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError s!"function did not parse: {content}")
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd) "incomplete or diagnosed source"
  return source
private def declared (source : Syntax.FunctionDecl) : IO LocalTypeInputs := do
  let some inputs := declareRuntimeParameters? base owner source.value.signature.parameters.elements
    | throw (IO.userError "original value-free parameters rejected")
  return inputs
private def actual (source : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) : IO LocalInputs := do
  let static ← declared source
  match accepted : bindRuntimeParameters? base owner source.value.signature.parameters.elements arguments with
  | none => throw (IO.userError "original actual arguments rejected")
  | some inputs =>
      have _ := (bindRuntimeParameters?_sound accepted).erase_values.complete
      assertTrue (decide (inputs.names = static.names ∧ inputs.context = static.context ∧
        inputs.environment.values = arguments.reverse.map (·.value))) "original rows or single argument reversal changed"
      return inputs
private structure Expression (inputs : LocalTypeInputs) (source : Syntax.Expr) (core : Core.Expr) (type : Core.Ty) where
  resolved : Resolved.Expr
  resolution : ResolvesLocalExpression inputs.names source resolved
  lowered : Resolved.Lowers inputs.ids resolved core
  typing : Resolved.HasType inputs.context resolved type
private def expression (inputs : LocalTypeInputs) (source : Syntax.Expr) (core : Core.Expr) (type : Core.Ty) : IO (Expression inputs source core type) := do
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
      let l ← expression inputs left first .word; let r ← expression inputs right second .word
      return ⟨.binary .wordSub l.resolved r.resolved, by rw [sourceAt]; exact .subtract l.resolution r.resolution,
        by rw [coreAt]; exact .binary l.lowered r.lowered,
        by rw [typeAt]; exact .binary l.typing r.typing⟩
  | _, _, _ => throw (IO.userError "expression differs from independent fixture Core")
termination_by sizeOf source
private structure Evidence (types : TypeNameTable) (inputs : LocalTypeInputs) (body : Syntax.Block) (core : Core.Expr) (type : Core.Ty) : Type where
  elaboration : TypedLetReturnTreeElaborates types owner inputs body core type
private def certify (types : TypeNameTable) (inputs : LocalTypeInputs) (body : Syntax.Block) (core : Core.Expr) (type : Core.Ty) : IO (Evidence types inputs body core type) := do
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
            let childTail ← certify types (inputs.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩ tail type
            return ⟨by
              rw [sourceAt, coreAt, typeAt]; exact .binding (interpretTypeName?_sound meaning).structural unused child.resolution child.lowered child.typing childTail.elaboration⟩
          else throw (IO.userError "independent binding reused a name")
  | ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩, .letE initial tail, type =>
      let .identifier originalName := initializer.value | throw (IO.userError "inferred fixture expected original reference")
      let some inferredType := (inputs.names.lookup? originalName.value).bind inputs.context.lookup? | throw (IO.userError "original reference type missing")
      if unused : name.value ∉ inputs.names.map Prod.fst then
        let child ← expression inputs initializer initial inferredType
        assertTrue (blockSpan.contains letSpan && letSpan.contains name.span && letSpan.contains initializer.span &&
          decide (name.span.endByte ≤ initializer.span.startByte) && (elaborateTypedLetReturnBody? types owner inputs body).isNone) "inferred annotation/spans or old prefix changed"
        let childTail ← certify types (inputs.bindFresh owner name.value inferredType) ⟨blockSpan, rest⟩ tail type
        return ⟨by rw [sourceAt, coreAt, typeAt]; exact .inferred unused child.resolution child.lowered child.typing childTail.elaboration⟩
      else throw (IO.userError "independent inference reused a name")
  | ⟨_, [⟨_, .ifThen condition left (some right)⟩]⟩, .ifE guard first second, type =>
      let child ← expression inputs condition guard .bool
      let l ← certify types inputs left first type; let r ← certify types inputs right second type
      return ⟨by rw [sourceAt, coreAt, typeAt]; exact .conditional child.resolution child.lowered child.typing l.elaboration r.elaboration⟩
  | _, _, _ => throw (IO.userError "original tree differs from independent Core")
termination_by sizeOf body
private def staticCheck (inputs : LocalTypeInputs) (body : Syntax.Block) (expected : Option (Core.Expr × Core.Ty)) : IO Unit := do
  have _ := elaborateTypedLetReturnTree?_eq_of_mutual_extends forward backward owner inputs body
  assertTrue (decide (elaborateTypedLetReturnTree? base owner inputs body = expected ∧
    elaborateTypedLetReturnTree? alternate owner inputs body = expected)) "mutual tables changed complete optional checking"
  if let some (core, type) := expected then
    let proof ← certify base inputs body core type
    have _ := proof.elaboration.extend_types grows
    have _ := proof.elaboration.hasType.extend_types grows
    have _ := elaborateTypedLetReturnTree?_some_of_extends grows proof.elaboration.complete
    assertTrue (decide (elaborateTypedLetReturnTree? extended owner inputs body = expected ∧
      Core.infer? inputs.context.values core = some type)) "one-way extension changed independent Core/type"
private def runChecked (inputs : LocalInputs) (body : Syntax.Block) (core : Core.Expr) (expected : TypedRuntimeArgument) (cost bound : Nat) : IO Unit := do
  staticCheck inputs.toTypeInputs body (some (core, expected.type))
  have _ := inputs.checkTypedLetReturnTree?_eq_of_mutual_extends forward backward owner body
  match checked : inputs.checkTypedLetReturnTree? base owner body with
  | none => throw (IO.userError "positive checker returned none")
  | some _ =>
      have _ := LocalInputs.checkTypedLetReturnTree?_some_of_extends grows checked
      assertTrue (decide (inputs.checkTypedLetReturnTree? extended owner body = some (core, expected.type) ∧
        typedLetReturnTreeFuelBound body = bound)) "successful checker or independent bound changed"
  for store in stores do
    let run := fun types fuel => inputs.runTypedLetReturnTree? types owner fuel body store
    for fuel in List.range (bound + 3) do
      have same := inputs.runTypedLetReturnTree?_eq_of_mutual_extends forward backward owner fuel body store
      assertTrue (decide (run base fuel = run alternate fuel ∧ run base fuel =
        some (expected.type, Core.runStateful fuel (.initial core inputs.environment.values store)))) "fixed-input full Core result changed"
      match original : run base fuel with
      | none => throw (IO.userError "accepted source lost a result")
      | some (type, result) =>
          have preserved := LocalInputs.runTypedLetReturnTree?_some_of_extends grows original
          assertTrue (decide (run extended fuel = some (type, result)) && match result with
            | .done value finalStore => decide (cost ≤ fuel ∧ value = expected.value ∧ finalStore = store)
            | .outOfFuel state => decide (fuel < cost ∧ state.store = store)
            | _ => false) "successful full pair or independent threshold/value changed"
          match resultAt : result with
          | .outOfFuel state =>
              have exhausted : run base fuel = some (type, .outOfFuel state) := by simpa only [resultAt] using original
              have nextOut : run extended fuel = some (type, .outOfFuel state) := by simpa only [resultAt] using preserved
              for remaining in List.range (cost - fuel + 3) do
                have _ := LocalInputs.runTypedLetReturnTree?_resume exhausted remaining
                have _ := LocalInputs.runTypedLetReturnTree?_resume nextOut remaining
                have _ := LocalInputs.runTypedLetReturnTree?_resume (same.symm.trans exhausted) remaining
                assertTrue (decide (run base (fuel + remaining) = some (type, Core.runStateful remaining state) ∧
                  run alternate (fuel + remaining) = run base (fuel + remaining) ∧ run extended (fuel + remaining) = run base (fuel + remaining))) "dictionary extension rebuilt a genuine checkpoint"
              let middle := (cost - fuel) / 2
              let .outOfFuel second := Core.runStateful middle state | throw (IO.userError "middle checkpoint disappeared")
              for last in [cost - fuel - middle - 1, cost - fuel - middle, cost - fuel - middle + 2] do
                for table in [base, alternate, extended] do
                  assertTrue (decide (run table (fuel + middle + last) = some (type, Core.runStateful last second))) "three chunks lost actual frames"
              assertTrue (decide (Core.runStateful (cost - fuel) state = .done expected.value store)) "exact residual lost expected value"
          | _ => pure ()
private def alternating (depth level : Nat) (annotation : String) : String × Core.Expr :=
  match depth with
  | 0 => ("return " ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";", .var (if level = 0 then 2 else 0))
  | count + 1 =>
      let (tail, core) := alternating count (level + 1) annotation
      ("if(c){" ++ s!"let z{level}: {annotation}=" ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";" ++ tail ++
        "}else{" ++ s!"let z{level}: {annotation}=y;return z{level};" ++ "}",
        .ifE (.var level) (.letE (.var (if level = 0 then 2 else 0)) core) (.letE (.var (level + 1)) (.var 0)))
private def fixture (content : String) (arguments : List TypedRuntimeArgument) (core : Core.Expr) (expected : TypedRuntimeArgument) (cost bound : Nat) : IO Unit := do
  let source ← parsed content; let inputs ← actual source arguments
  assertTrue (decide (interpretRuntimeFunctionHeader? base source.value.signature = some expected.type) &&
    (elaborateTypedLetReturnBody? base owner inputs.toTypeInputs source.value.body).isNone) "header or old prefix boundary changed"
  runChecked inputs source.value.body core expected cost bound
  for table in [base, alternate, extended] do
    assertTrue (decide ((compileRuntimeFunction? table owner source).map (fun c => (c.core, c.returnType, c.inputs.names, c.inputs.context.values)) =
      some (core, expected.type, inputs.names, inputs.context.values)) && (prepareRuntimeFunction? table owner source arguments).any (fun p =>
        decide (p.core = core ∧ p.returnType = expected.type ∧ p.inputs.names = inputs.names ∧ p.inputs.context.values = inputs.context.values ∧
          p.inputs.environment.values = arguments.reverse.map (·.value)))) "table changed exact entry or original actual rows"
    for store in stores do
      for fuel in List.range (bound + 3) do
        assertTrue (decide (runRuntimeFunction? table owner source arguments fuel store =
          some (expected.type, Core.runStateful fuel (.initial core inputs.environment.values store)))) "table changed full entry result or checkpoint"
private def rawReference (inputs : LocalInputs) (store : Core.Store) (source : Syntax.Expr) (value : Core.Value) : IO (PLift (LocalExpressionEvaluatesWithCost inputs.names inputs.environment store source value store 1)) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : inputs.names.lookup? name.value with
      | none => throw (IO.userError "raw name missing")
      | some id =>
          if found : inputs.environment.lookup? id = some value then
            return ⟨by rw [sourceAt]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
          else throw (IO.userError "raw actual value missing")
  | _ => throw (IO.userError "raw fixture expected identifier")

def frontendParsedTypedLetReturnTreeTypeExtensionTests : IO Unit := do
  assertTrue (decide (base ≠ alternate ∧ base.length ≠ alternate.length ∧ base.lookup? ["Pkg.Token"] = some .word ∧
    base.lookup? ["Pkg", "Token"] = some (.namedData ⟨92⟩))) "mutual tables or qualified-key contrast became trivial"
  have _ (id : Core.DataTypeId) : ¬ ∃ value, Core.ValueHasType value (.namedData id) := by
    rintro ⟨value, typed⟩
    cases typed with
    | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
  for (annotation, type) in [("Opaque", Core.Ty.namedData ⟨91⟩), ("Pkg /* separate */ . Token", .namedData ⟨92⟩)] do
    for depth in [1, 2, 5, 12] do
      let (body, core) := alternating depth 0 annotation
      let source ← parsed (s!"function nominal(x: {annotation},y: {annotation},c: Bool) returns ({annotation})" ++ "{" ++ body ++ "}")
      let inputs ← declared source
      staticCheck inputs source.value.body (some (core, type))
      assertTrue (decide (interpretRuntimeFunctionHeader? base source.value.signature = some type ∧
        (compileRuntimeFunction? extended owner source).map (fun c => (c.core, c.returnType, c.inputs.names, c.inputs.context.values)) =
          some (core, type, inputs.names, inputs.context.values))) "nominal extension changed exact Core or demanded an inhabitant"
  let left : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩
  let right : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  for (annotation, x, y) in [("Word", wordArg 9, wordArg 2), ("Cell", ⟨.cell .word, .cellRef .word 17, .cellRef⟩, ⟨.cell .word, .cellRef .word 29, .cellRef⟩),
      ("Fn", left, right)] do
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
    fixture "function rejected(x: Word,y: Word,c: Bool) returns (Word){if(c){let z=x;return z;}else{return y;}}"
      [wordArg 9, wordArg 2, boolArg c] (.ifE (.var 0) (.letE (.var 2) (.var 0)) (.var 1)) (wordArg (if c then 9 else 2)) (if c then 7 else 4) 7
  for body in ["{if(c){let z: Unknown=x;return z;}else{return y;}}", "{if(c){let z: Bool=x;return z;}else{return y;}}",
      "{if(c){let x: Word=y;return x;}else{return y;}}", "{if(c){let z: Word=z;return x;}else{return y;}}",
      "{if(c){let z: Word;return x;}else{return y;}}",
      "{if(c){return x;}else{let a: Word=y;if(c){return a;}else{return missing;}}}",
      "{if(c){return x;}else{return c;}}", "{if(x){return x;}else{return y;}}", "{if(c){return x;}}", "{return x;return y;}", "{}"] do
    let source ← parsed ("function rejected(x: Word,y: Word,c: Bool) returns (Word)" ++ body); let inputs ← actual source [wordArg 9, wordArg 2, boolArg true]
    staticCheck inputs.toTypeInputs source.value.body none
    have _ := inputs.checkTypedLetReturnTree?_eq_of_mutual_extends forward backward owner source.value.body
    for store in stores do
      for fuel in List.range (typedLetReturnTreeFuelBound source.value.body + 3) do
        have _ := inputs.runTypedLetReturnTree?_eq_of_mutual_extends forward backward owner fuel source.value.body store
        assertTrue ((inputs.runTypedLetReturnTree? base owner fuel source.value.body store).isNone &&
          (inputs.runTypedLetReturnTree? alternate owner fuel source.value.body store).isNone) "mutual tables repaired whole rejection"
  let repair ← parsed "function repair(x: Word,c: Bool) returns (Word){if(c){return x;}else{let z: WordAlias=x;return z;}}"
  let fixed ← actual repair [wordArg 9, boolArg true]
  let repairedCore := Core.Expr.ifE (.var 0) (.var 1) (.letE (.var 1) (.var 0))
  staticCheck fixed.toTypeInputs repair.value.body none
  let proof ← certify extended fixed.toTypeInputs repair.value.body repairedCore .word
  have _ := proof.elaboration.complete
  assertTrue (decide (fixed.checkTypedLetReturnTree? extended owner repair.value.body = some (repairedCore, .word) ∧
    fixed.ids = [⟨owner, 1⟩, ⟨owner, 0⟩])) "repair changed original fixed inputs"
  for store in stores do
    match sourceAt : repair.value.body with
    | ⟨_, [⟨_, .ifThen condition ⟨_, [⟨_, .returnStmt (some returned)⟩]⟩ (some _)⟩]⟩ =>
        let guard ← rawReference fixed store condition (.bool true); let result ← rawReference fixed store returned (.word (word 9))
        have raw : TypedLetReturnTreeEvaluatesWithCost owner fixed.names fixed.environment store repair.value.body (.word (word 9)) store 4 := by
          rw [sourceAt]; exact .ifTrue guard.down (.single (.expression result.down))
        have _ := raw.erase
        pure ()
    | _ => throw (IO.userError "unknown-unselected repair source shape changed")
    for fuel in List.range 10 do
      assertTrue ((fixed.runTypedLetReturnTree? base owner fuel repair.value.body store).isNone &&
        decide (fixed.runTypedLetReturnTree? extended owner fuel repair.value.body store =
          some (.word, Core.runStateful fuel (.initial repairedCore fixed.environment.values store)))) "one-way extension wrongly preserved none or changed raw selected value"
      if 4 ≤ fuel then assertTrue (decide (fixed.runTypedLetReturnTree? extended owner fuel repair.value.body store =
        some (.word, .done (.word (word 9)) store))) "unselected repair changed the independent four-step selected path"
  let nominal ← parsed "function repaired(x: Opaque,c: Bool) returns (Opaque){if(c){return x;}else{let z: Alias=x;return z;}}"; let nominalInputs ← declared nominal
  staticCheck nominalInputs nominal.value.body none
  let nominalProof ← certify extended nominalInputs nominal.value.body repairedCore (.namedData ⟨91⟩)
  have _ := nominalProof.elaboration.complete
  assertTrue (decide (elaborateTypedLetReturnTree? extended owner nominalInputs nominal.value.body =
    some (repairedCore, .namedData ⟨91⟩))) "unknown unselected nominal repair demanded an actual inhabitant"
  let shadow : TypeNameTable := (["Word"], .bool) :: base
  have _ : ¬ TypeNameTable.Extends base shadow := by
    intro extension
    have impossible := (extension (show TypeNameTable.Lookup base ["Word"] .word from .head)).type_unique
      (show TypeNameTable.Lookup shadow ["Word"] .bool from .head)
    cases impossible
  have _ : ∀ row ∈ base, row ∈ shadow := fun _ member => List.mem_cons_of_mem _ member
  let source ← parsed "function shadow(x: Word,c: Bool) returns (Word){if(c){let z: Word=x;return z;}else{return x;}}"
  assertTrue ((fixed.checkTypedLetReturnTree? base owner source.value.body).isSome &&
    (fixed.checkTypedLetReturnTree? shadow owner source.value.body).isNone && decide (shadow.drop 1 = base ∧
      fixed.context.values = [.bool, .word] ∧ fixed.environment.values = [.bool true, .word (word 9)])) "row inclusion or rebinding was mistaken for semantic extension"
  let unchanged ← parsed "function unchanged(x: Word,c: Bool) returns (Word){return x;}"
  assertTrue (decide (fixed.checkTypedLetReturnTree? shadow owner unchanged.value.body = some (.var 1, .word))) "dictionary change silently rebound fixed parameters"
end Tests
