import Solcore.Syntax.Parser.Term
import Solcore.Frontend.TypedLetReturnTree
import Solcore.Frontend.LocalName
import Solcore.Resolved.Renaming

/-! Composed lookup agrees on every spelling, independently of IDs and layouts.
Original parsed blocks have separate value/cost certificates on both sides. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"RawLookup", by decide⟩], by decide⟩⟩, index⟩
private def id (o i : Nat) : Resolved.LocalId := ⟨owner o, i⟩
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def w (n : Nat) : Core.Value := .word (word n)
private def stores : List Core.Store := [[], [.cellRef .word 40, .bool true, w 91]]
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool)]
private def leftTable : LocalNameTable := [("c", id 17 2), ("d", id 71 999), ("r", id 17 5), ("l", id 17 7)]
private def rightTable : LocalNameTable := [("ghost", id 3 77), ("l", id 3 2), ("c", id 3 1),
  ("l", id 71 80), ("r", id 3 4), ("d", id 71 0)]
private def leftEnv (l r : Core.Value) (c d : Bool) : Resolved.Environment :=
  [(id 17 8, w 99), (id 17 5, r), (id 71 999, .bool d), (id 17 2, .bool c), (id 17 7, l), (id 17 7, .bool true)]
private def rightEnv (l r : Core.Value) (c d : Bool) : Resolved.Environment :=
  [(id 71 0, .bool d), (id 3 4, r), (id 3 1, .bool c), (id 3 2, l), (id 3 78, w 88), (id 3 2, .bool false), (id 71 117, .unit)]
private theorem sameLookup (l r : Core.Value) (c d : Bool) : ∀ name,
    (leftTable.lookup? name).bind (leftEnv l r c d).lookup? = (rightTable.lookup? name).bind (rightEnv l r c d).lookup? := by
  intro name
  by_cases hc : "c" = name
  · subst name; simp [leftTable, rightTable, leftEnv, rightEnv, LocalNameTable.lookup?, Resolved.LocalScope.lookup?, id, owner]
  by_cases hd : "d" = name
  · subst name; simp [leftTable, rightTable, leftEnv, rightEnv, LocalNameTable.lookup?, Resolved.LocalScope.lookup?, id, owner]
  by_cases hr : "r" = name
  · subst name; simp [leftTable, rightTable, leftEnv, rightEnv, LocalNameTable.lookup?, Resolved.LocalScope.lookup?, id, owner]
  by_cases hl : "l" = name
  · subst name; simp [leftTable, rightTable, leftEnv, rightEnv, LocalNameTable.lookup?, Resolved.LocalScope.lookup?, id, owner]
  by_cases hg : "ghost" = name
  · subst name; simp [leftTable, rightTable, leftEnv, rightEnv, LocalNameTable.lookup?, Resolved.LocalScope.lookup?, id, owner]
  simp [leftTable, rightTable, LocalNameTable.lookup?, hc, hd, hr, hl, hg]
private def parsed (content : String) : IO Syntax.Block := do
  let file : Syntax.SourceFile := { id := ⟨.main, "raw-lookup.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  let .ok body next := Syntax.Parser.block .allow (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError s!"block did not parse: {content}")
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd) "incomplete original block"
  assertTrue (decide (body.span.source = file.id ∧ body.span.startByte = 0 ∧ body.span.endByte = content.utf8ByteSize))
    "original block span changed"
  return body
private structure Expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost table env store source value store cost
private def reference (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table env store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "certificate name missing")
      | some id =>
          match found : env.lookup? id with
          | none => throw (IO.userError "certificate actual value missing")
          | some value => return ⟨value, 1, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | _ => throw (IO.userError "certificate expected original reference")
private def expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table env store source) := do
  match sourceAt : source with
  | ⟨_, .identifier _⟩ => reference table env store source
  | ⟨_, .unary ⟨_, .bitNot⟩ operand⟩ =>
      let child ← reference table env store operand
      match atValue : child.value with
      | .word value => return ⟨.word value.bitNot, child.cost + 2, by rw [sourceAt]; exact .bitNot (atValue ▸ child.costed)⟩
      | _ => throw (IO.userError "certificate expected Word")
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let first ← reference table env store left
      let second ← reference table env store right
      match atLeft : first.value, atRight : second.value with
      | .word l, .word r => return ⟨.word (l.sub r), first.cost + second.cost + 3, by
          rw [sourceAt]; exact .subtract (atLeft ▸ first.costed) (atRight ▸ second.costed)⟩
      | _, _ => throw (IO.userError "certificate subtraction expected Words")
  | _ => throw (IO.userError "expression outside independent certificate script")
private structure Certificate (currentOwner : Resolved.DeclarationId) (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (body : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TypedLetReturnTreeEvaluatesWithCost currentOwner table env store body value store cost
private def certify (currentOwner : Resolved.DeclarationId) (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (body : Syntax.Block) (choices : List Bool) : IO (Certificate currentOwner table env store body) := do
  match atBody : body with
  | ⟨span, ⟨_, .letDecl name annotation (some initializer)⟩ :: rest⟩ =>
      let child ← expression table env store initializer
      let id := Resolved.freshLocalId currentOwner (table.map Prod.snd)
      let tail ← certify currentOwner ((name.value, id) :: table) ((id, child.value) :: env) store ⟨span, rest⟩ choices
      return ⟨tail.value, child.cost + tail.cost + 2, by
        rw [atBody]
        cases annotation with
        | none => exact .inferred child.costed tail.costed
        | some _ => exact .binding child.costed tail.costed⟩
  | ⟨_, [⟨_, .ifThen condition left (some right)⟩]⟩ =>
      let choice :: rest := choices | throw (IO.userError "independent branch script missing")
      let guard ← reference table env store condition
      if agrees : guard.value = .bool choice then
        match atChoice : choice with
        | true =>
            let child ← certify currentOwner table env store left rest
            return ⟨child.value, guard.cost + child.cost + 2, by
              rw [atBody]
              exact .ifTrue (by simpa only [agrees, atChoice] using guard.costed) child.costed⟩
        | false =>
            let child ← certify currentOwner table env store right rest
            return ⟨child.value, guard.cost + child.cost + 2, by
              rw [atBody]
              exact .ifFalse (by simpa only [agrees, atChoice] using guard.costed) child.costed⟩
      else throw (IO.userError "independent branch script disagrees with actual guard")
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ =>
      assertTrue choices.isEmpty "script continued past bare return"
      return ⟨.unit, 1, by rw [atBody]; exact .single .bare⟩
  | ⟨_, [⟨_, .returnStmt (some operand)⟩]⟩ =>
      assertTrue choices.isEmpty "script continued past return"
      let child ← expression table env store operand
      return ⟨child.value, child.cost, by rw [atBody]; exact .single (.expression child.costed)⟩
  | _ => throw (IO.userError "body outside independent certificate script")
termination_by sizeOf body
private def raw (lo ro : Resolved.DeclarationId) (lt rt : LocalNameTable) (le re : Resolved.Environment)
    (agrees : ∀ name, (lt.lookup? name).bind le.lookup? = (rt.lookup? name).bind re.lookup?)
    (body : Syntax.Block) (expected : Option (Core.Value × Nat)) (choices : List Bool := []) : IO Unit := do
  have same := evaluateTypedLetReturnTreeWithCost?_congr_lookup lo ro lt rt le re agrees body
  have _ := same.symm
  assertTrue (decide (evaluateTypedLetReturnTreeWithCost? lo lt le body = expected ∧
    evaluateTypedLetReturnTreeWithCost? ro rt re body = expected)) "independent result/cost differed"
  match body.value with
  | [⟨_, .returnStmt (some expression)⟩] =>
      have sameExpression := evaluateLocalExpressionWithCost?_congr_lookup lt rt le re agrees expression
      have _ := sameExpression.symm
      assertTrue (decide (evaluateLocalExpressionWithCost? lt le expression = expected ∧
        evaluateLocalExpressionWithCost? rt re expression = expected)) "expression lookup law changed cost"
  | _ => pure ()
  for store in stores do
    match expected with
    | none =>
        match left : evaluateTypedLetReturnTreeWithCost? lo lt le body,
            right : evaluateTypedLetReturnTreeWithCost? ro rt re body with
        | none, none =>
            have _ := (evaluateTypedLetReturnTreeWithCost?_eq_none_iff store).mp left
            have _ := (evaluateTypedLetReturnTreeWithCost?_eq_none_iff store).mp right
            pure ()
        | _, _ => throw (IO.userError "genuine raw absence disappeared")
    | some (value, cost) =>
        let left ← certify lo lt le store body choices
        let right ← certify ro rt re store body choices
        assertTrue (decide (left.value = value ∧ right.value = value ∧ left.cost = cost ∧ right.cost = cost))
          "independent raw certificates disagreed"
        have _ := (typedLetReturnTreeEvaluatesWithCost_congr_lookup_iff (leftOwner := lo) (rightOwner := ro) agrees).mp left.costed
        have _ := (typedLetReturnTreeEvaluatesWithCost_congr_lookup_iff (leftOwner := lo) (rightOwner := ro) agrees).mpr right.costed
        have _ := (typedLetReturnTreeEvaluates_congr_lookup_iff (leftOwner := lo) (rightOwner := ro) agrees).mp left.costed.erase
        have _ := (typedLetReturnTreeEvaluates_congr_lookup_iff (leftOwner := lo) (rightOwner := ro) agrees).mpr right.costed.erase
        have _ : ¬ TypedLetReturnTreeEvaluatesWithCost ro rt re store body value (.unit :: store) cost := by
          intro impossible
          have lengths := congrArg List.length impossible.store_eq
          simp only [List.length_cons] at lengths
          omega
        pure ()
private def sample (content : String) (l r : Core.Value) (c d : Bool)
    (expected : Option (Core.Value × Nat)) (choices : List Bool := []) : IO Unit := do
  raw (owner 17) (owner 3) leftTable rightTable (leftEnv l r c d) (rightEnv l r c d)
    (sameLookup l r c d) (← parsed content) expected choices
private def spine (remaining level : Nat) : String :=
  match remaining with
  | 0 => "return " ++ (if level = 0 then "l" else s!"z{level - 1}") ++ ";"
  | count + 1 => "if(c){" ++ s!"let z{level}: Word=" ++
      (if level = 0 then "l" else s!"z{level - 1}") ++ ";" ++ spine count (level + 1) ++
      "}else{" ++ s!"let z{level}: Word=r;return z{level};" ++ "}"
private def checkedLeft : LocalInputs := ⟨[⟨"x", id 17 0, .word, w 9, .word⟩,
  ⟨"y", id 17 1, .word, w 2, .word⟩], by change [id 17 0, id 17 1].Nodup; decide⟩
private def checkedRight : LocalInputs := ⟨[⟨"y", id 3 0, .word, w 2, .word⟩,
  ⟨"x", id 3 10, .word, w 9, .word⟩, ⟨"x", id 3 20, .word, w 99, .word⟩], by
    change [id 3 0, id 3 10, id 3 20].Nodup; decide⟩
private def checked : IO Unit := do
  let body ← parsed "{let z: Word=x;return z;}"
  have same : ∀ name, (checkedLeft.names.lookup? name).bind checkedLeft.environment.lookup? =
      (checkedRight.names.lookup? name).bind checkedRight.environment.lookup? := by
    intro name
    by_cases hx : "x" = name
    · subst name; rfl
    by_cases hy : "y" = name
    · subst name; rfl
    simp [checkedLeft, checkedRight, LocalInputs.names, LocalInputs.environment, LocalNameTable.lookup?, hx, hy]
  raw (owner 17) (owner 3) checkedLeft.names checkedRight.names checkedLeft.environment checkedRight.environment same body (some (w 9, 4))
  for (actual, currentOwner, core) in [(checkedLeft, owner 17, Core.Expr.letE (.var 0) (.var 0)),
      (checkedRight, owner 3, Core.Expr.letE (.var 1) (.var 0))] do
    assertTrue (decide (actual.checkTypedLetReturnTree? types currentOwner body = some (core, .word))) "independent exact Core disappeared"
    match accepted : actual.checkTypedLetReturnTree? types currentOwner body,
        evaluated : evaluateTypedLetReturnTreeWithCost? currentOwner actual.toTypeInputs.names actual.environment body with
    | some _, some _ =>
        have aligned : actual.environment.ids = actual.toTypeInputs.context.ids := by
          simpa only [LocalInputs.toTypeInputs_context] using actual.sameIds
        for store in stores do
          have _ := evaluateTypedLetReturnTreeWithCost?_checked_toStepsWithContinuation (store := store) evaluated accepted aligned []
          for fuel in List.range 7 do
            assertTrue (decide (actual.runTypedLetReturnTree? types currentOwner fuel body store =
              some (.word, Core.runStateful fuel (.initial core actual.environment.values store)))) "own actual Core result changed"
          assertTrue (decide (actual.runTypedLetReturnTree? types currentOwner 2 body store =
            some (.word, .outOfFuel ⟨.ret (w 9), [.letBody (.var 0) actual.environment.values], store⟩))) "independent captured environment changed"
    | _, _ => throw (IO.userError "separate checked premises missing")
  for store in stores do
    assertTrue (decide (checkedLeft.runTypedLetReturnTree? types (owner 17) 2 body store ≠
      checkedRight.runTypedLetReturnTree? types (owner 3) 2 body store)) "equal raw results were mistaken for equal checkpoints"

def frontendParsedRawLookupTests : IO Unit := do
  sample "{let z=l;return z;}" (w 9) (w 2) true false (some (w 9, 4))
  for depth in [0, 1, 2, 5, 12] do
    for c in [false, true] do
      sample ("{" ++ spine depth 0 ++ "}") (w 9) (w 2) c false
        (some (w (if depth = 0 || c then 9 else 2), if depth = 0 then 1 else if c then 6 * depth + 1 else 7))
        (if depth = 0 then [] else if c then List.replicate depth true else [false])
  for (l, r) in [(9, 2), (2, 9), (0, Core.wordModulus - 1), (2 ^ 255, 7)] do
    for c in [false, true] do
      for d in [false, true] do
        sample "{if(c){let z: Word=l - r;if(d){let q: Word=z;return ~q;}else{let q: Word=r - z;return q;}}else{let z: Word=r - l;return r;}}"
          (w l) (w r) c d (some (if c then if d then w (Core.wordModulus - 1 - (l + Core.wordModulus - r) % Core.wordModulus)
            else w (r + Core.wordModulus - (l + Core.wordModulus - r) % Core.wordModulus) else w r,
            if c then if d then 19 else 21 else 11)) (if c then [true, d] else [false])
  for (content, value, cost, choices) in [("{return;}", Core.Value.unit, 1, []), ("{return l - r;}", w 7, 5, []),
      ("{return ~l;}", w (Core.wordModulus - 10), 3, []), ("{let unused: Word=l - r;return r;}", w 2, 8, []),
      ("{let z: Unknown=l;return z;}", w 9, 4, []), ("{let z: Bool=l;return z;}", w 9, 4, []), ("{let l: Word=l - r;return l;}", w 7, 8, []),
      ("{if(c){return l;}else{let z: Unknown=ghost;return z;}}", w 9, 4, [true])] do
    sample content (w 9) (w 2) true false (some (value, cost)) choices
  for content in ["{}", "{return ghost;}", "{return missing;}", "{let z: Word;return l;}",
      "{let z: Word=l;}", "{return l;return r;}", "{if(c){return l;}}", "{if(c){return l;}else{return r;}return l;}",
      "{let unused: Word=ghost;return r;}", "{let unused: Word=~c;return r;}", "{return f(l);}",
      "{if(l){return l;}else{return r;}}"] do sample content (w 9) (w 2) true false none
  for value in [Core.Value.unit, .cellRef .word 999, .closure .word .word (.var 1) [w 7],
      .closure .word .bool (.var 80) [], .constructed ⟨⟨91⟩, 4⟩ (.pair .unit (w 7))] do
    sample "{let z: Word=l;if(c){return z;}else{return r;}}" value (w 2) true false (some (value, 7)) [true]
  let static : LocalTypeInputs := ⟨[⟨"c", id 17 2, .bool⟩, ⟨"d", id 71 999, .bool⟩,
    ⟨"r", id 17 5, .word⟩, ⟨"l", id 17 7, .word⟩], by
      change [id 17 2, id 71 999, id 17 5, id 17 7].Nodup; decide⟩
  assertTrue (decide (static.names = leftTable)) "whole-check contrast replaced raw names"
  for content in ["{let z: Unknown=l;return z;}", "{let z: Bool=l;return z;}", "{let l: Word=l - r;return l;}",
      "{if(c){return l;}else{let z: Unknown=ghost;return z;}}"] do
    assertTrue ((elaborateTypedLetReturnTree? types (owner 17) static (← parsed content)).isNone)
      "raw selected success was mistaken for whole annotation/freshness/branch acceptance"
  assertTrue (decide (leftTable.lookup? "ghost" = none ∧ rightTable.lookup? "ghost" = some (id 3 77) ∧
    Resolved.freshLocalId (owner 17) (leftTable.map Prod.snd) = id 17 8 ∧
    Resolved.freshLocalId (owner 3) (rightTable.map Prod.snd) = id 3 78 ∧
    (leftEnv (w 9) (w 2) true false).lookup? (id 17 8) = some (w 99) ∧
    (rightEnv (w 9) (w 2) true false).lookup? (id 3 78) = some (w 88))) "absence, unbound names and independent fresh collisions changed"
  checked
  let source ← parsed "{let z: Unknown=x;return z;}"
  let indexShift := fun binder : Resolved.LocalId => { binder with binderIndex := binder.binderIndex + 10 }
  let table : LocalNameTable := [("x", id 71 0)]
  let env : Resolved.Environment := [(id 71 0, w 9)]
  let mappedTable := LocalNameTable.mapIds indexShift table
  let mappedEnv := Resolved.LocalScope.mapIds indexShift env
  have same : ∀ name, (table.lookup? name).bind env.lookup? = (mappedTable.lookup? name).bind mappedEnv.lookup? := by
    intro name
    by_cases hx : "x" = name
    · subst name; rfl
    simp [table, mappedTable, LocalNameTable.mapIds, LocalNameTable.lookup?, hx]
  raw (owner 17) (owner 17) table mappedTable env mappedEnv same source (some (w 9, 4))
  assertTrue (decide (Resolved.freshLocalId (owner 17) (mappedTable.map Prod.snd) ≠
    indexShift (Resolved.freshLocalId (owner 17) (table.map Prod.snd)))) "index-changing map unexpectedly commuted with allocation"
  let changed : Resolved.Environment := (id 71 0, w 2) :: env
  assertTrue (decide ((table.lookup? "x").bind env.lookup? ≠ (table.lookup? "x").bind changed.lookup? ∧
    evaluateTypedLetReturnTreeWithCost? (owner 17) table changed source = some (w 2, 4))) "changed visible first match had no witness"

end Tests
