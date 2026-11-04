import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.TypedLetReturnTree

/-!
# Typed let tree raw owner tests

Raw owners of typed let return trees.
-/

section
-- leanmerge: from Solcore.Test.FrontendParsedTypedLetReturnTreeRawOwner
/-! Original complete blocks and independent raw certificates on arbitrary caller
rows. Owner collapse changes lookup; allocator noncommutation alone says less. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"RawTreeOwners", by decide⟩], by decide⟩⟩, 17⟩
private def other : Resolved.DeclarationId := { owner with declarationIndex := 71 }
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
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def w (n : Nat) : Core.Value := .word (word n)
private def stores : List Core.Store := [[], [.cellRef .word 40, .bool true, w 91]]
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool)]
private def inputs (l r : Nat) (c d : Bool) : LocalInputs := ⟨[
  ⟨"c", ⟨owner, 2⟩, .bool, .bool c, .bool⟩, ⟨"d", ⟨other, 999⟩, .bool, .bool d, .bool⟩,
  ⟨"r", ⟨owner, 5⟩, .word, w r, .word⟩, ⟨"l", ⟨owner, 7⟩, .word, w l, .word⟩], by
    change ([⟨owner, 2⟩, ⟨other, 999⟩, ⟨owner, 5⟩, ⟨owner, 7⟩] : List Resolved.LocalId).Nodup
    decide⟩
private def parsed (content : String) : IO Syntax.Block := do
  let file : Syntax.SourceFile := { id := ⟨.main, "raw-tree-owners.sol"⟩, content }
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
private def raw (table : LocalNameTable) (env : Resolved.Environment) (body : Syntax.Block)
    (expected : Option (Core.Value × Nat)) (choices : List Bool := []) : IO Unit := do
  let mappedTable := LocalNameTable.mapIds mapping table
  let mappedEnv := Resolved.LocalScope.mapIds mapping env
  have same := evaluateTypedLetReturnTreeWithCost?_mapOwner shift shiftInjective owner table env body
  have _ := same.symm
  assertTrue (decide (evaluateTypedLetReturnTreeWithCost? owner table env body = expected ∧
    evaluateTypedLetReturnTreeWithCost? (shift owner) mappedTable mappedEnv body = expected ∧
    mappedEnv.values = env.values ∧ mappedTable.map Prod.fst = table.map Prod.fst))
    "independent raw value/cost or unchanged rows disagreed"
  for store in stores do
    match expected with
    | none =>
        match original : evaluateTypedLetReturnTreeWithCost? owner table env body,
            mapped : evaluateTypedLetReturnTreeWithCost? (shift owner) mappedTable mappedEnv body with
        | none, none =>
            have _ := (evaluateTypedLetReturnTreeWithCost?_eq_none_iff store).mp original
            have _ := (evaluateTypedLetReturnTreeWithCost?_eq_none_iff store).mp mapped
            pure ()
        | _, _ => throw (IO.userError "raw absence changed under owner relabeling")
    | some (value, cost) =>
        let original ← certify owner table env store body choices
        let mapped ← certify (shift owner) mappedTable mappedEnv store body choices
        assertTrue (decide (original.value = value ∧ mapped.value = value ∧ original.cost = cost ∧ mapped.cost = cost))
          "independent original-AST certificates disagreed"
        have mappedForward := (typedLetReturnTreeEvaluatesWithCost_mapOwner_iff shift shiftInjective).mpr original.costed
        have _ := (typedLetReturnTreeEvaluatesWithCost_mapOwner_iff shift shiftInjective
          (owner := owner) (table := table) (environment := env)).mp mapped.costed
        have _ := (typedLetReturnTreeEvaluates_mapOwner_iff shift shiftInjective).mpr original.costed.erase
        have _ := (typedLetReturnTreeEvaluates_mapOwner_iff shift shiftInjective
          (owner := owner) (table := table) (environment := env)).mp mapped.costed.erase
        have _ := mappedForward.store_eq
        have _ : ¬ TypedLetReturnTreeEvaluatesWithCost (shift owner) mappedTable mappedEnv
            store body value (.unit :: store) cost := by
          intro impossible
          have lengths := congrArg List.length impossible.store_eq
          simp only [List.length_cons] at lengths
          omega
        pure ()
private def spine (remaining level : Nat) : String :=
  match remaining with
  | 0 => "return " ++ (if level = 0 then "l" else s!"z{level - 1}") ++ ";"
  | count + 1 => "if(c){" ++ s!"let z{level}: Word=" ++
      (if level = 0 then "l" else s!"z{level - 1}") ++ ";" ++ spine count (level + 1) ++
      "}else{" ++ s!"let z{level}: Word=r;return z{level};" ++ "}"
private def checked (actual : LocalInputs) (body : Syntax.Block) : IO Unit := do
  let renamed := actual.mapIds mapping (ownerLocalIdMap_injective shift shiftInjective)
  let core : Core.Expr := .letE (.var 3) (.var 0)
  assertTrue (decide (actual.checkTypedLetReturnTree? types owner body = some (core, .word) ∧
    renamed.checkTypedLetReturnTree? types (shift owner) body = some (core, .word)))
    "separate whole acceptance changed exact Core"
  match accepted : actual.checkTypedLetReturnTree? types owner body,
      evaluated : evaluateTypedLetReturnTreeWithCost? owner actual.toTypeInputs.names actual.environment body with
  | some _, some _ =>
      have aligned : actual.environment.ids = actual.toTypeInputs.context.ids := by
        simpa only [LocalInputs.toTypeInputs_context] using actual.sameIds
      for store in stores do
        have _ := evaluateTypedLetReturnTreeWithCost?_checked_toStepsWithContinuation
          (store := store) evaluated accepted aligned [.letBody (.var 0) [w 99]]
        for fuel in List.range 7 do
          have _ := actual.runTypedLetReturnTree?_mapOwner shift shiftInjective types owner fuel body store
          assertTrue (decide (actual.runTypedLetReturnTree? types owner fuel body store =
            some (.word, Core.runStateful fuel (.initial core actual.environment.values store)) ∧
            renamed.runTypedLetReturnTree? types (shift owner) fuel body store =
              actual.runTypedLetReturnTree? types owner fuel body store)) "fixed-store full checkpoint changed"
        assertTrue (decide (actual.runTypedLetReturnTree? types owner 2 body store =
          some (.word, .outOfFuel ⟨.ret (w 9), [.letBody (.var 0) actual.environment.values], store⟩)))
          "old-scope initializer checkpoint changed"
  | _, _ => throw (IO.userError "separate checked premises missing")

def frontendParsedTypedLetReturnTreeRawOwnerTests : IO Unit := do
  have _ := shiftNotSurjective
  for depth in [0, 1, 2, 5, 12] do
    let body ← parsed ("{" ++ spine depth 0 ++ "}")
    for c in [false, true] do
      let actual := inputs 9 2 c false
      raw actual.names actual.environment body
        (some (w (if depth = 0 || c then 9 else 2), if depth = 0 then 1 else if c then 6 * depth + 1 else 7))
        (if depth = 0 then [] else if c then List.replicate depth true else [false])
  let asymmetric ← parsed "{if(c){let z: Word=l - r;if(d){let q: Word=z;return ~q;}else{let q: Word=r - z;return q;}}else{let z: Word=r - l;return r;}}"
  for (l, r) in [(9, 2), (2, 9), (0, Core.wordModulus - 1), (2 ^ 255, 7)] do
    for c in [false, true] do
      for d in [false, true] do
        let actual := inputs l r c d
        raw actual.names actual.environment asymmetric
          (some (if c then if d then w (Core.wordModulus - 1 - (l + Core.wordModulus - r) % Core.wordModulus)
            else w (r + Core.wordModulus - (l + Core.wordModulus - r) % Core.wordModulus) else w r,
            if c then if d then 19 else 21 else 11)) (if c then [true, d] else [false])
  let actual := inputs 9 2 true false
  let inferred ← parsed "{let z=l;return z;}"
  raw actual.names actual.environment inferred (some (w 9, 4))
  checked actual inferred
  for (content, value, cost, choices) in [("{return;}", Core.Value.unit, 1, []),
      ("{let unused: Word=l - r;return r;}", w 2, 8, []),
      ("{let z: Unknown=l;return z;}", w 9, 4, []), ("{let z: Bool=l;return z;}", w 9, 4, []),
      ("{let l: Word=l - r;return l;}", w 7, 8, []),
      ("{if(c){let z: Word=l;return z;}else{let z: Unknown=missing;return z;}}", w 9, 7, [true]),
      ("{if(c){return l;}else{return c;}}", w 9, 4, [true])] do
    let body ← parsed content
    raw actual.names actual.environment body (some (value, cost)) choices
    if content != "{return;}" && content != "{let unused: Word=l - r;return r;}" then
      assertTrue ((actual.checkTypedLetReturnTree? types owner body).isNone) "raw success became whole acceptance"
  for content in ["{}", "{let z: Word;return l;}", "{let z: Word=l;}",
      "{return l;return r;}", "{if(c){return l;}}", "{if(c){return l;}else{return r;}return l;}",
      "{let unused: Word=missing;return r;}", "{let unused: Word=~c;return r;}", "{let z: Word=z;return l;}", "{return f(l);}",
      "{if(l){return l;}else{return r;}}"] do raw actual.names actual.environment (← parsed content) none
  let body ← parsed "{let z: Word=l;return z;}"
  checked actual body
  let fresh : Resolved.LocalId := ⟨owner, 8⟩
  let collision : Resolved.Environment := (fresh, w 99) :: actual.environment
  assertTrue (decide (Resolved.freshLocalId owner (actual.names.map Prod.snd) = fresh ∧
    Resolved.freshLocalId owner collision.ids = ⟨owner, 9⟩ ∧ collision.ids ≠ actual.context.ids ∧
    Core.runStateful 4 (.initial (.letE (.var 3) (.var 0)) collision.values []) = .done (w 2) []))
    "name-table allocation and unaligned positional Core execution were conflated"
  raw actual.names collision body (some (w 9, 4))
  let id : Resolved.LocalId := ⟨other, 999⟩
  raw (("l", id) :: actual.names) ((id, w 4) :: (id, w 9) :: collision) body (some (w 4, 4))
  raw actual.names [] body none
  for value in [Core.Value.unit, .cellRef .word 999, .closure .word .word (.var 1) [w 7],
      .closure .word .word (.var 80) [], .bool false, .constructed ⟨⟨91⟩, 4⟩ (.pair .unit (w 7))] do
    raw actual.names (actual.environment.map fun row => (row.1, value)) body (some (value, 4))
  let returned ← parsed "{return x;}"
  let a : Resolved.LocalId := ⟨owner, 0⟩
  let b : Resolved.LocalId := ⟨other, 0⟩
  let table : LocalNameTable := [("x", b)]
  let environment : Resolved.Environment := [(a, w 2), (b, w 9)]
  let collapse := ownerLocalIdMap (fun _ => owner)
  assertTrue (decide (a ≠ b ∧ collapse a = collapse b ∧
    evaluateTypedLetReturnTreeWithCost? owner table environment returned = some (w 9, 1) ∧
    evaluateTypedLetReturnTreeWithCost? owner (LocalNameTable.mapIds collapse table)
      (Resolved.LocalScope.mapIds collapse environment) returned = some (w 2, 1))) "owner collapse failed to expose changed first-match value"
  let indexShift := fun id : Resolved.LocalId => { id with binderIndex := id.binderIndex + 1 }
  let source ← parsed "{let z: Unknown=x;return z;}"
  let env : Resolved.Environment := [(b, w 9)]
  assertTrue (decide (Resolved.freshLocalId owner ((LocalNameTable.mapIds indexShift table).map Prod.snd) ≠
    indexShift (Resolved.freshLocalId owner (table.map Prod.snd)) ∧
    evaluateTypedLetReturnTreeWithCost? owner table env source = some (w 9, 4) ∧
    evaluateTypedLetReturnTreeWithCost? owner (LocalNameTable.mapIds indexShift table)
      (Resolved.LocalScope.mapIds indexShift env) source = some (w 9, 4)))
    "allocator noncommutation was wrongly presented as raw result inequality"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendTypedLetReturnTreeRawOwnerProperties
/-! Raw rows need not be aligned, unique or typed. Owner transport preserves
first matches and actual values; the final checked path has its own premises. -/
set_option autoImplicit false
namespace Tests.FrontendTypedLetReturnTreeRawOwner
open Solcore Solcore.Frontend

private def owner (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"RawOwners", by decide⟩], by decide⟩⟩, index⟩
private def id (declaration index : Nat) : Resolved.LocalId := ⟨owner declaration, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "raw-owners.sol"⟩, 226, 8⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation (name : String := "Payload") : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def returned (name : String) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (ref name))⟩]⟩
private def binding (name : String) (value : Syntax.Expr) (tail : Syntax.Block) (typeName : String := "Payload") : Syntax.Block :=
  ⟨span, ⟨span, .letDecl ⟨span, name⟩ (some (annotation typeName)) (some value)⟩ :: tail.value⟩
private def branch (condition : Syntax.Expr) (yes no : Syntax.Block) : Syntax.Block := ⟨span, [⟨span, .ifThen condition yes (some no)⟩]⟩
private def zero : Syntax.Expr := ⟨span, .literal ⟨span, .decimal "0"⟩⟩
private def guard : Syntax.Expr := ⟨span, .binary zero ⟨span, .equal⟩ zero⟩
private theorem zeroMeaning : WordLiteralDenotes ⟨span, .decimal "0"⟩ Core.Word.zero :=
  .decimal (by decide) (.cons (.decimal (digit := 0) (by decide) (by decide)) .nil)
private def tree : List String → String → Syntax.Block
  | [], previous => returned previous
  | name :: rest, previous => binding name (ref previous) (branch guard (tree rest name) (returned name))
private def names : LocalNameTable := [("seed", id 0 7), ("seed", id 1 199), ("alias", id 0 7), ("old", id 0 2)]
private def values (value hidden : Core.Value) : Resolved.Environment :=
  [(id 0 8, hidden), (id 1 199, .bool false), (id 0 7, value), (id 0 7, .bool true), (id 0 2, .unit)]
private def mappedNames (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (table : LocalNameTable) := table.mapIds (ownerLocalIdMap mapping)
private def mappedValues (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (env : Resolved.Environment) := env.mapIds (ownerLocalIdMap mapping)
private def shift (declaration : Resolved.DeclarationId) : Resolved.DeclarationId := { declaration with declarationIndex := declaration.declarationIndex + 5 }
private theorem shiftInjective : Function.Injective shift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := Nat.add_right_cancel (congrArg Resolved.DeclarationId.declarationIndex same)
  cases left; cases right; cases modules; cases indices; rfl
private theorem counted (locals : List String) (previous : String) (table : LocalNameTable) (env : Resolved.Environment)
    (value : Core.Value) (store : Core.Store) (head : LocalExpressionEvaluatesWithCost table env store (ref previous) value store 1) :
    TypedLetReturnTreeEvaluatesWithCost (owner 0) table env store (tree locals previous) value store (10 * locals.length + 1) := by
  induction locals generalizing previous table env with
  | nil => exact .single (.expression head)
  | cons name rest ih =>
    have count : 1 + (5 + (10 * rest.length + 1) + 2) + 2 = 10 * (name :: rest).length + 1 := by simp; omega
    simpa only [count, tree, binding, branch, guard, zero] using TypedLetReturnTreeEvaluatesWithCost.binding
      (name := ⟨span, name⟩) (annotation := annotation) head
      (.ifTrue (.equal (.wordLiteral zeroMeaning) (.wordLiteral zeroMeaning)) (ih name _ _ (.identifier .head .head)))
private theorem raw (locals : List String) (value hidden : Core.Value) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost (owner 0) names (values value hidden) store (tree locals "seed") value store (10 * locals.length + 1) :=
  counted locals "seed" names (values value hidden) value store (.identifier .head (.tail (by decide) (.tail (by decide) .head)))
private theorem output (locals : List String) (value hidden : Core.Value) :
    evaluateTypedLetReturnTreeWithCost? (owner 0) names (values value hidden) (tree locals "seed") = some (value, 10 * locals.length + 1) :=
  evaluateTypedLetReturnTreeWithCost?_complete (raw locals value hidden [])

theorem arbitrary_raw_depth_and_duplicate_unaligned_rows_keep_values_costs_and_stores
    (locals : List String) (value hidden : Core.Value) (store : Core.Store)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) :
    evaluateTypedLetReturnTreeWithCost? (mapping (owner 0)) (mappedNames mapping names) (mappedValues mapping (values value hidden))
      (tree locals "seed") = some (value, 10 * locals.length + 1) ∧
    TypedLetReturnTreeEvaluatesWithCost (mapping (owner 0)) (mappedNames mapping names) (mappedValues mapping (values value hidden))
      store (tree locals "seed") value store (10 * locals.length + 1) ∧
    TypedLetReturnTreeEvaluates (mapping (owner 0)) (mappedNames mapping names) (mappedValues mapping (values value hidden))
      store (tree locals "seed") value store ∧
    evaluateTypedLetReturnTreeWithCost? (owner 0) names (values value hidden) (tree locals "seed") = some (value, 10 * locals.length + 1) := by
  have same := evaluateTypedLetReturnTreeWithCost?_mapOwner mapping injective (owner 0) names (values value hidden) (tree locals "seed")
  have mappedResult := same.trans (output locals value hidden)
  exact ⟨mappedResult,
    (typedLetReturnTreeEvaluatesWithCost_mapOwner_iff mapping injective).mpr (raw locals value hidden store),
    (typedLetReturnTreeEvaluates_mapOwner_iff mapping injective).mpr (raw locals value hidden store).erase,
    same.symm.trans mappedResult⟩

theorem reflection_retains_exact_final_store_value_and_cost
    (locals : List String) (value hidden result : Core.Value) (store final : Core.Store) (cost : Nat) :
    (TypedLetReturnTreeEvaluatesWithCost (owner 5) (mappedNames shift names) (mappedValues shift (values value hidden))
      store (tree locals "seed") result final cost ↔ result = value ∧ final = store ∧ cost = 10 * locals.length + 1) ∧
    (TypedLetReturnTreeEvaluates (owner 5) (mappedNames shift names) (mappedValues shift (values value hidden))
      store (tree locals "seed") result final ↔ result = value ∧ final = store) := by
  constructor
  · constructor
    · intro path
      exact ((typedLetReturnTreeEvaluatesWithCost_mapOwner_iff shift shiftInjective (owner := owner 0)
        (table := names) (environment := values value hidden)).mp path).deterministic (raw locals value hidden store)
    · rintro ⟨sameValue, sameStore, sameCost⟩; subst result; subst final; subst cost
      exact (typedLetReturnTreeEvaluatesWithCost_mapOwner_iff shift shiftInjective).mpr (raw locals value hidden store)
  · constructor
    · intro path
      exact ((typedLetReturnTreeEvaluates_mapOwner_iff shift shiftInjective (owner := owner 0)
        (table := names) (environment := values value hidden)).mp path).deterministic (raw locals value hidden store).erase
    · rintro ⟨sameValue, sameStore⟩; subst result; subst final
      exact (typedLetReturnTreeEvaluates_mapOwner_iff shift shiftInjective).mpr (raw locals value hidden store).erase

theorem a_nonsurjective_owner_map_changes_only_owners_not_indices_or_row_order (value hidden : Core.Value) :
    ¬ Function.Surjective shift ∧
    mappedNames shift names = [("seed", id 5 7), ("seed", id 6 199), ("alias", id 5 7), ("old", id 5 2)] ∧
    (mappedValues shift (values value hidden)).values = [hidden, .bool false, value, .bool true, .unit] ∧
    (mappedValues shift (values value hidden)).ids ≠ (mappedNames shift names).map Prod.snd ∧
    ¬ ((mappedNames shift names).map Prod.snd).Nodup := by
  refine ⟨?_, rfl, rfl, ?_, ?_⟩
  · intro onto
    obtain ⟨preimage, same⟩ := onto (owner 0)
    have impossible := congrArg Resolved.DeclarationId.declarationIndex same
    change preimage.declarationIndex + 5 = 0 at impossible
    omega
  · intro same; cases same
  · decide

theorem fresh_name_table_allocation_can_collide_with_an_extra_environment_row
    (value hidden : Core.Value) (store : Core.Store) :
    Resolved.freshLocalId (owner 0) (names.map Prod.snd) = id 0 8 ∧
    Resolved.freshLocalId (owner 5) ((mappedNames shift names).map Prod.snd) = id 5 8 ∧
    (mappedValues shift (values value hidden)).lookup? (id 5 8) = some hidden ∧
    evaluateTypedLetReturnTreeWithCost? (owner 5) (mappedNames shift names) (mappedValues shift (values value hidden))
      (binding "seed" (ref "seed") (returned "seed")) = some (value, 4) ∧
    TypedLetReturnTreeEvaluatesWithCost (owner 5) (mappedNames shift names) (mappedValues shift (values value hidden))
      store (binding "seed" (ref "seed") (returned "seed")) value store 4 := by
  have original : TypedLetReturnTreeEvaluatesWithCost (owner 0) names (values value hidden) store
      (binding "seed" (ref "seed") (returned "seed")) value store 4 := by
    apply TypedLetReturnTreeEvaluatesWithCost.binding (initializerCost := 1) (tailCost := 1)
    · exact .identifier .head (.tail (by decide) (.tail (by decide) .head))
    · exact .single (.expression (.identifier .head .head))
  exact ⟨rfl, rfl, rfl,
    (evaluateTypedLetReturnTreeWithCost?_mapOwner shift shiftInjective (owner 0) names _ _).trans
      (evaluateTypedLetReturnTreeWithCost?_complete original),
    (typedLetReturnTreeEvaluatesWithCost_mapOwner_iff shift shiftInjective).mpr original⟩

private def clean (type : Core.Ty) : LocalTypeInputs := ⟨[⟨"seed", id 0 7, type⟩], by change [id 0 7].Nodup; decide⟩
private def cleanValues (value : Core.Value) : Resolved.Environment := [(id 0 7, value)]
private def unknown := binding "fresh" (ref "seed") (returned "fresh") "Unknown"
private def skipped := branch guard (returned "seed") unknown
theorem raw_selected_success_does_not_establish_the_unselected_annotation_contract
    (value : Core.Value) (type : Core.Ty) (store : Core.Store) :
    evaluateTypedLetReturnTreeWithCost? (owner 5) (mappedNames shift (clean type).names)
      (mappedValues shift (cleanValues value)) skipped = some (value, 8) ∧
    elaborateTypedLetReturnTree? [(["Payload"], type)] (owner 5)
      ((clean type).mapIds (ownerLocalIdMap shift) (ownerLocalIdMap_injective shift shiftInjective)) skipped = none := by
  have original : TypedLetReturnTreeEvaluatesWithCost (owner 0) (clean type).names (cleanValues value) store skipped value store 8 := by
    apply TypedLetReturnTreeEvaluatesWithCost.ifTrue (conditionCost := 5) (branchCost := 1)
    · exact .equal (.wordLiteral zeroMeaning) (.wordLiteral zeroMeaning)
    · exact .single (.expression (.identifier .head .head))
  refine ⟨(evaluateTypedLetReturnTreeWithCost?_mapOwner shift shiftInjective (owner 0) _ _ _).trans
    (evaluateTypedLetReturnTreeWithCost?_complete original),
    (elaborateTypedLetReturnTree?_mapOwner shift shiftInjective _ (owner 0) (clean type) skipped).trans ?_⟩
  apply elaborateTypedLetReturnTree?_eq_none_iff.mpr
  rintro ⟨_, typing⟩
  cases typing with
  | single child => cases child
  | conditional _ _ other =>
    cases other with
    | single child => cases child
    | binding meaning _ _ _ =>
      have impossible := meaning.complete
      simp only [annotation, interpretStructuralType?_named_eq_typeName] at impossible
      change none = some _ at impossible
      cases impossible

theorem missing_selected_initializers_remain_absent_in_both_raw_relations (store : Core.Store) :
    evaluateTypedLetReturnTreeWithCost? (owner 5) (mappedNames shift names) [] unknown = none ∧
    ¬ (∃ result cost, TypedLetReturnTreeEvaluatesWithCost (owner 5) (mappedNames shift names) [] store unknown result store cost) ∧
    ¬ (∃ result, TypedLetReturnTreeEvaluates (owner 5) (mappedNames shift names) [] store unknown result store) := by
  have absent : ¬ ∃ result cost, TypedLetReturnTreeEvaluatesWithCost (owner 0) names [] store unknown result store cost := by
    rintro ⟨_, _, path⟩
    cases path with
    | single child => cases child
    | binding initializer _ => cases initializer with | identifier _ found => cases found
  refine ⟨(evaluateTypedLetReturnTreeWithCost?_mapOwner shift shiftInjective (owner 0) names [] unknown).trans
    ((evaluateTypedLetReturnTreeWithCost?_eq_none_iff store).mpr absent), ?_, ?_⟩
  · rintro ⟨result, cost, path⟩
    exact absent ⟨result, cost, (typedLetReturnTreeEvaluatesWithCost_mapOwner_iff shift shiftInjective).mp path⟩
  · rintro ⟨result, path⟩
    obtain ⟨cost, costed⟩ := ((typedLetReturnTreeEvaluates_mapOwner_iff shift shiftInjective
      (owner := owner 0) (table := names) (environment := [])).mp path).exists_cost
    exact absent ⟨result, cost, costed⟩

theorem opaque_values_are_not_retyped_or_invoked_by_owner_transport
    (locals : List String) (location : Core.Location) (hidden : Core.Value) :
    evaluateTypedLetReturnTreeWithCost? (owner 5) (mappedNames shift names)
      (mappedValues shift (values (.cellRef .word location) hidden)) (tree locals "seed") = some (.cellRef .word location, 10 * locals.length + 1) ∧
    evaluateTypedLetReturnTreeWithCost? (owner 5) (mappedNames shift names)
      (mappedValues shift (values (.closure .word .bool (.var 999) [.unit]) hidden)) (tree locals "seed") =
      some (.closure .word .bool (.var 999) [.unit], 10 * locals.length + 1) :=
  ⟨(arbitrary_raw_depth_and_duplicate_unaligned_rows_keep_values_costs_and_stores locals _ hidden [] shift shiftInjective).1,
    (arbitrary_raw_depth_and_duplicate_unaligned_rows_keep_values_costs_and_stores locals _ hidden [] shift shiftInjective).1⟩

private def collapse (_ : Resolved.DeclarationId) := owner 0
private def collisionNames : LocalNameTable := [("seed", id 1 0)]
private def collisionValues : Resolved.Environment := [(id 0 0, .bool false), (id 1 0, .bool true)]
private def collisionBody := binding "z" (ref "seed") (returned "z")
theorem a_noninjective_owner_collapse_changes_the_actual_first_match :
    ¬ Function.Injective collapse ∧
    evaluateTypedLetReturnTreeWithCost? (owner 0) collisionNames collisionValues collisionBody = some (.bool true, 4) ∧
    evaluateTypedLetReturnTreeWithCost? (owner 0) (mappedNames collapse collisionNames) (mappedValues collapse collisionValues) collisionBody = some (.bool false, 4) ∧
    evaluateTypedLetReturnTreeWithCost? (owner 0) collisionNames collisionValues collisionBody ≠
      evaluateTypedLetReturnTreeWithCost? (owner 0) (mappedNames collapse collisionNames) (mappedValues collapse collisionValues) collisionBody := by
  have original : TypedLetReturnTreeEvaluatesWithCost (owner 0) collisionNames collisionValues [] collisionBody (.bool true) [] 4 := by
    apply TypedLetReturnTreeEvaluatesWithCost.binding (initializerCost := 1) (tailCost := 1)
    · exact .identifier .head (.tail (by decide) .head)
    · exact .single (.expression (.identifier .head .head))
  have collapsed : TypedLetReturnTreeEvaluatesWithCost (owner 0) (mappedNames collapse collisionNames) (mappedValues collapse collisionValues) [] collisionBody (.bool false) [] 4 := by
    apply TypedLetReturnTreeEvaluatesWithCost.binding (initializerCost := 1) (tailCost := 1)
    · exact .identifier .head .head
    · exact .single (.expression (.identifier .head .head))
  have before := evaluateTypedLetReturnTreeWithCost?_complete original
  have after := evaluateTypedLetReturnTreeWithCost?_complete collapsed
  refine ⟨?_, before, after, ?_⟩
  · intro injective
    have impossible := injective (a₁ := owner 0) (a₂ := owner 1) rfl
    cases impossible
  · rw [before, after]; intro impossible; cases impossible

private def indexShift (binder : Resolved.LocalId) : Resolved.LocalId := { binder with binderIndex := binder.binderIndex + 10 }
theorem arbitrary_index_shifts_fail_allocator_commutation_without_claiming_changed_raw_results :
    Function.Injective indexShift ∧
    Resolved.freshLocalId (owner 0) ([].map indexShift) = id 0 0 ∧
    indexShift (Resolved.freshLocalId (owner 0) []) = id 0 10 ∧
    Resolved.freshLocalId (owner 0) ([].map indexShift) ≠ indexShift (Resolved.freshLocalId (owner 0) []) := by
  refine ⟨?_, rfl, rfl, by decide⟩
  intro left right same
  have owners := congrArg Resolved.LocalId.owner same
  have indices := Nat.add_right_cancel (congrArg Resolved.LocalId.binderIndex same)
  cases left; cases right; cases owners; cases indices; rfl

theorem a_checked_core_path_uses_separate_whole_provenance_and_aligned_ids
    (type : Core.Ty) (value : Core.Value) (store : Core.Store) (continuation : List Core.Frame) :
    Core.Steps 4 ⟨.eval (.letE (.var 0) (.var 0)) [value], continuation, store⟩ ⟨.ret value, continuation, store⟩ := by
  have elaboration : TypedLetReturnTreeElaborates [(["Payload"], type)] (owner 0) (clean type)
      (binding "x" (ref "seed") (returned "x")) (.letE (.var 0) (.var 0)) type :=
    .binding (.named .head) (by change "x" ∉ ["seed"]; decide) (.identifier .head) (.var .head) (.var .head)
      (.single (.expression (.identifier .head) (.var .head) (.var .head)))
  have original : TypedLetReturnTreeEvaluatesWithCost (owner 0) (clean type).names (cleanValues value) store
      (binding "x" (ref "seed") (returned "x")) value store 4 := by
    apply TypedLetReturnTreeEvaluatesWithCost.binding (initializerCost := 1) (tailCost := 1)
    · exact .identifier .head .head
    · exact .single (.expression (.identifier .head .head))
  have evaluated := (evaluateTypedLetReturnTreeWithCost?_mapOwner shift shiftInjective (owner 0) _ _ _).trans
    (evaluateTypedLetReturnTreeWithCost?_complete original)
  exact evaluateTypedLetReturnTreeWithCost?_checked_toStepsWithContinuation evaluated
    (elaboration.mapOwner shift shiftInjective).complete rfl continuation

end Tests.FrontendTypedLetReturnTreeRawOwner
end
