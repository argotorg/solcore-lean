import Solcore.Frontend.ClosedSourceEvaluationProperties

/-! Heterogeneous original tuples and all nine body rules have independent
closed derivations. Lookup witnesses, not evaluator callbacks, supply actual
values. These symbolic spans make no parser, typing or canonical-scope claim. -/
set_option autoImplicit false
namespace Tests.FrontendClosedSourceBody
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def ref (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span,.identifier name⟩
private def groups : List Syntax.SourceSpan → Syntax.Expr → Syntax.Expr
  | [],source => source
  | span::rest,source => ⟨span,.group (groups rest source)⟩
private theorem groupPath {o names captured store source actual}
    (path : E o names captured store source actual store) (spans : List Syntax.SourceSpan) :
    E o names captured store (groups spans source) actual store := by
  induction spans with | nil => exact path | cons _ _ ih => exact .group ih
private structure Leaf where
  name : Syntax.Identifier
  span : Syntax.SourceSpan
  groups : List Syntax.SourceSpan
  id : Resolved.LocalId
  actual : RuntimeValue
private def leafSource (leaf : Leaf) : Syntax.Expr := groups leaf.groups (ref leaf.span leaf.name)
private def Admits (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue) (leaf : Leaf) : Prop :=
  LocalNameTable.Lookup names leaf.name.value leaf.id ∧ Resolved.LocalScope.Lookup captured leaf.id leaf.actual
private theorem leafPath (o : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (leaf : Leaf)
    (valid : Admits names captured leaf) : E o names captured store (leafSource leaf) leaf.actual store :=
  groupPath (.reference valid.1 valid.2) leaf.groups
private def tuple (span delimiter : Syntax.SourceSpan) (first second : Syntax.Expr) (rest : List Syntax.Expr) : Syntax.Expr :=
  ⟨span,.tuple ⟨delimiter,first::second::rest⟩⟩
private def packed (first second : RuntimeValue) : List RuntimeValue → RuntimeValue
  | [] => .pair first second
  | third::rest => .pair first (packed second third rest)
private theorem tuplePath (o : Resolved.DeclarationId) (span delimiter : Syntax.SourceSpan)
    (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (first second : Leaf) (rest : List Leaf)
    (valid : ∀ leaf ∈ first::second::rest, Admits names captured leaf) :
    E o names captured store (tuple span delimiter (leafSource first) (leafSource second) (rest.map leafSource))
      (packed first.actual second.actual (rest.map Leaf.actual)) store := by
  induction rest generalizing first second with
  | nil => exact .pair (leafPath _ _ _ _ _ (valid _ (by simp))) (leafPath _ _ _ _ _ (valid _ (by simp)))
  | cons third rest ih =>
      exact .many (leafPath _ _ _ _ _ (valid _ (by simp)))
        (ih second third (fun leaf member => valid leaf (List.mem_cons_of_mem _ member)))
private theorem freshNe {o : Resolved.DeclarationId} {names : LocalNameTable}
    {name : String} {id : Resolved.LocalId} (named : LocalNameTable.Lookup names name id) :
    Resolved.freshLocalId o (names.map Prod.snd) ≠ id := by
  intro same
  have member : id ∈ names.map Prod.snd := List.mem_map_of_mem named.mem
  exact Resolved.freshLocalId_not_mem o _ (same ▸ member)
private structure Rows (name condition : Syntax.Identifier) (leaves : List Leaf)
    (actual : RuntimeValue) (side : Bool) where
  names : LocalNameTable
  captured : Resolved.LocalScope RuntimeValue
  id : Resolved.LocalId
  conditionId : Resolved.LocalId
  named : LocalNameTable.Lookup names name.value id
  found : Resolved.LocalScope.Lookup captured id actual
  conditionNamed : LocalNameTable.Lookup names condition.value conditionId
  conditionFound : Resolved.LocalScope.Lookup captured conditionId (.bool side)
  retained : ∀ leaf ∈ leaves, Admits names captured leaf
private def rebound {name condition leaves actual side} (o : Resolved.DeclarationId)
    (different : name.value≠condition.value) (unshadowed : ∀ leaf ∈ leaves, name.value≠leaf.name.value)
    (rows : Rows name condition leaves actual side) : Rows name condition leaves actual side where
  names := (name.value,Resolved.freshLocalId o (rows.names.map Prod.snd))::rows.names
  captured := (Resolved.freshLocalId o (rows.names.map Prod.snd),actual)::rows.captured
  id := Resolved.freshLocalId o (rows.names.map Prod.snd)
  conditionId := rows.conditionId
  named := .head
  found := .head
  conditionNamed := .tail different rows.conditionNamed
  conditionFound := .tail (freshNe rows.conditionNamed) rows.conditionFound
  retained := fun leaf member => ⟨.tail (unshadowed leaf member) (rows.retained leaf member).1,
    .tail (freshNe (rows.retained leaf member).1) (rows.retained leaf member).2⟩
private def returned (span : Syntax.SourceSpan) (source : Syntax.Expr) : Syntax.Block :=
  ⟨span,[⟨span,.returnStmt (some source)⟩]⟩
private def bare (span : Syntax.SourceSpan) : Syntax.Block := ⟨span,[⟨span,.returnStmt none⟩]⟩
private def zero (span : Syntax.SourceSpan) : Syntax.Expr := ⟨span,.literal ⟨span,.decimal "0"⟩⟩
private theorem zeroMeaning (span : Syntax.SourceSpan) : WordLiteralDenotes ⟨span,.decimal "0"⟩ .zero :=
  .decimal (by decide) (.cons (.decimal (digit:=0) (by decide) rfl) .nil)
private def matched (span : Syntax.SourceSpan) (source : Syntax.Expr)
    (cases : List Syntax.MatchCase) (defaultBody : Option Syntax.Block) : Syntax.Block :=
  ⟨span,[⟨span,.matchWith ⟨span,⟨source,[]⟩⟩ ⟨span,⟨cases,defaultBody⟩⟩⟩]⟩
private def literalCase (span : Syntax.SourceSpan) (body : Syntax.Block) : Syntax.MatchCase :=
  ⟨span,⟨⟨span,.literal ⟨span,.decimal "0"⟩⟩,body⟩⟩
private def terminal (span delimiter : Syntax.SourceSpan) (name condition : Syntax.Identifier)
    (second : Leaf) (rest : List Leaf) (unused : List Syntax.MatchCase) (defaultBody : Option Syntax.Block) : Syntax.Block :=
  let result := returned span (tuple span delimiter (ref span name) (leafSource second) (rest.map leafSource))
  ⟨span,[⟨span,.ifThen (ref span condition)
    (matched span (zero span) (literalCase span result::unused) defaultBody)
    (some (matched span ⟨span,.tuple ⟨delimiter,[]⟩⟩ [] (some (bare span))))⟩]⟩
private def body (span delimiter : Syntax.SourceSpan) (name condition : Syntax.Identifier)
    (annotation : Syntax.TypeExpr) (second : Leaf) (rest : List Leaf)
    (unused : List Syntax.MatchCase) (defaultBody : Option Syntax.Block) : Nat → Syntax.Block
  | 0 => terminal span delimiter name condition second rest unused defaultBody
  | n+1 => ⟨span,[⟨name.span,.letDecl name (some annotation) (some (ref span name))⟩,
      ⟨name.span,.letDecl name none (some (ref span name))⟩,
      ⟨span,.expression (ref span name) true⟩,
      ⟨span,.block (body span delimiter name condition annotation second rest unused defaultBody n).value⟩]⟩
private theorem bodyPath (o : Resolved.DeclarationId) (span delimiter : Syntax.SourceSpan)
    (name condition : Syntax.Identifier) (annotation : Syntax.TypeExpr) (second : Leaf) (rest : List Leaf)
    (unused : List Syntax.MatchCase) (defaultBody : Option Syntax.Block) (n : Nat)
    (actual : RuntimeValue) (side : Bool) (store : List RuntimeValue)
    (different : name.value≠condition.value)
    (unshadowed : ∀ leaf ∈ second::rest, name.value≠leaf.name.value)
    (rows : Rows name condition (second::rest) actual side) :
    B o rows.names rows.captured store (body span delimiter name condition annotation second rest unused defaultBody n)
      (if side then packed actual second.actual (rest.map Leaf.actual) else .unit) store := by
  induction n generalizing rows with
  | zero =>
      cases side
      · exact .ifFalse (.reference rows.conditionNamed rows.conditionFound) (.wordMatch .unit .fallback .bare)
      · apply ClosedSourceBodyEvaluates.ifTrue (.reference rows.conditionNamed rows.conditionFound)
        apply ClosedSourceBodyEvaluates.wordMatch (.wordLiteral (zeroMeaning span))
          (.hit (.literal ⟨_,rfl,zeroMeaning span⟩))
        apply ClosedSourceBodyEvaluates.expression
        exact tuplePath o span delimiter rows.names rows.captured store
          ⟨name,span,[],rows.id,actual⟩ second rest (by
            intro leaf member
            rcases List.mem_cons.mp member with rfl | member
            · exact ⟨rows.named,rows.found⟩
            · exact rows.retained leaf member)
  | succ n ih =>
      let first := rebound o different unshadowed rows
      let secondRows := rebound o different unshadowed first
      have tail := ih secondRows
      apply ClosedSourceBodyEvaluates.binding (.reference rows.named rows.found)
      apply ClosedSourceBodyEvaluates.inferred (.reference .head .head)
      apply ClosedSourceBodyEvaluates.discard (.reference .head .head)
      cases n <;> exact .block tail

theorem heterogeneous_grouped_tuple_retains_each_actual_component
    (o : Resolved.DeclarationId) (span delimiter : Syntax.SourceSpan) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (first second : Leaf) (rest : List Leaf)
    (valid : ∀ leaf ∈ first::second::rest, Admits names captured leaf) :
    E o names captured store (tuple span delimiter (leafSource first) (leafSource second) (rest.map leafSource))
      (packed first.actual second.actual (rest.map Leaf.actual)) store := tuplePath _ _ _ _ _ _ _ _ _ valid

theorem arbitrary_shadow_depth_keeps_retained_values_and_selects_the_original_body
    (o : Resolved.DeclarationId) (span delimiter : Syntax.SourceSpan) (name condition : Syntax.Identifier)
    (annotation : Syntax.TypeExpr) (second : Leaf) (rest : List Leaf)
    (unused : List Syntax.MatchCase) (defaultBody : Option Syntax.Block) (n : Nat)
    (actual : RuntimeValue) (side : Bool) (store : List RuntimeValue)
    (different : name.value≠condition.value) (unshadowed : ∀ leaf ∈ second::rest, name.value≠leaf.name.value)
    (rows : Rows name condition (second::rest) actual side) :
    B o rows.names rows.captured store (body span delimiter name condition annotation second rest unused defaultBody n)
      (if side then packed actual second.actual (rest.map Leaf.actual) else .unit) store :=
  bodyPath _ _ _ _ _ _ _ _ _ _ _ _ _ _ different unshadowed rows

theorem exact_original_body_compatibility_recovers_the_literal_result_and_store
    (o : Resolved.DeclarationId) (span delimiter : Syntax.SourceSpan) (name condition : Syntax.Identifier)
    (annotation : Syntax.TypeExpr) (second : Leaf) (rest : List Leaf)
    (unused : List Syntax.MatchCase) (defaultBody : Option Syntax.Block) (n : Nat)
    (actual result : RuntimeValue) (side : Bool) (store final : List RuntimeValue)
    (different : name.value≠condition.value) (unshadowed : ∀ leaf ∈ second::rest, name.value≠leaf.name.value)
    (rows : Rows name condition (second::rest) actual side) :
    SourceComputationBodyEvaluates E o rows.names rows.captured store
      (body span delimiter name condition annotation second rest unused defaultBody n) result final ↔
      result=(if side then packed actual second.actual (rest.map Leaf.actual) else .unit) ∧ final=store := by
  have independent := bodyPath o span delimiter name condition annotation second rest unused defaultBody
    n actual side store different unshadowed rows
  constructor
  · intro evaluated
    exact (closedSourceBodyEvaluates_iff.mpr evaluated).deterministic independent
  · rintro ⟨rfl,rfl⟩
    exact closedSourceBodyEvaluates_iff.mp independent

theorem arbitrary_groups_around_original_empty_tuple_return_unit
    (o : Resolved.DeclarationId) (span delimiter : Syntax.SourceSpan) (spans : List Syntax.SourceSpan)
    (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) :
    E o names captured store (groups spans ⟨span,.tuple ⟨delimiter,[]⟩⟩) .unit store := groupPath .unit spans

theorem leading_wildcard_returns_the_exact_mixed_capture
    (o : Resolved.DeclarationId) (span marker : Syntax.SourceSpan) (name : Syntax.Identifier)
    (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (id : Resolved.LocalId) (actual : RuntimeValue) (unused : List Syntax.MatchCase) (defaultBody : Option Syntax.Block)
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id actual) :
    B o names captured store (matched span (ref span name)
      (⟨span,⟨⟨span,.group ⟨span,.wildcard marker⟩⟩,returned span (ref span name)⟩⟩::unused) defaultBody) actual store :=
  .wordMatch (.reference named found) (.wildcard (.group (.wildcard rfl))) (.expression (.reference named found))

private def missedCases (span marker : Syntax.SourceSpan) (selected : Syntax.Block)
    (unused : List Syntax.MatchCase) : List (Syntax.SourceSpan × Syntax.Block) → List Syntax.MatchCase
  | [] => ⟨span,⟨⟨span,.group ⟨span,.wildcard marker⟩⟩,selected⟩⟩::unused
  | first::rest => literalCase first.1 first.2::missedCases span marker selected unused rest
private theorem missPath (span marker : Syntax.SourceSpan) (selected : Syntax.Block)
    (unused : List Syntax.MatchCase) (defaultBody : Option Syntax.Block) (word : Core.Word)
    (different : word≠.zero) (misses : List (Syntax.SourceSpan × Syntax.Block)) :
    RuntimeWordMatchChooses (.word word) (missedCases span marker selected unused misses)
      defaultBody selected misses.length := by
  induction misses with
  | nil => exact .wildcard (.group (.wildcard rfl))
  | cons first rest ih => exact .miss (.literal ⟨_,rfl,zeroMeaning first.1⟩) different ih

theorem arbitrary_missed_original_bodies_are_skipped_before_the_grouped_wildcard
    (o : Resolved.DeclarationId) (span marker : Syntax.SourceSpan) (name : Syntax.Identifier)
    (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (id : Resolved.LocalId) (word : Core.Word) (different : word≠.zero)
    (misses : List (Syntax.SourceSpan × Syntax.Block)) (unused : List Syntax.MatchCase)
    (defaultBody : Option Syntax.Block) (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id (.word word)) :
    let selected := returned span (ref span name)
    let cases := missedCases span marker selected unused misses
    RuntimeWordMatchChooses (.word word) cases defaultBody selected misses.length ∧
      B o names captured store (matched span (ref span name) cases defaultBody) (.word word) store := by
  have choice := missPath span marker (returned span (ref span name)) unused defaultBody word different misses
  exact ⟨choice,.wordMatch (.reference named found) choice (.expression (.reference named found))⟩

end Tests.FrontendClosedSourceBody
