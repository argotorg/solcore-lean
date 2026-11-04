import Solcore.Frontend.ClosedSource
import Solcore.Frontend.LocalReference
import Solcore.Resolved.LocalScope
import Solcore.Frontend.SourceLambdaEvaluation
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.LocalExpressionEvaluator
import Solcore.Frontend.LocalExpression
import Solcore.Frontend.WordLiteral
import Solcore.Core.UnaryPrimitives

/-!
# Closed source body tests

Closed source derivations of bodies and calls: runners, conditionals, closures, depth boundaries, core
images, stores and unary forms.
-/

section
-- leanmerge: from Solcore.Test.FrontendClosedSourceBodyProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendClosedSourceBodyRunnerProperties
/-! Heterogeneous original tuples and all nine body rules have independent
closed derivations. Lookup witnesses, not evaluator callbacks, supply actual
values. These symbolic spans make no parser, typing or canonical-scope claim. -/
set_option autoImplicit false
namespace Tests.FrontendClosedSourceBodyRunner
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

private theorem groupRun (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (spans : List Syntax.SourceSpan) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (id : Resolved.LocalId) (actual : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id actual)
    (budget : Nat) (large : spans.length+1≤budget) :
    evaluateClosedSourceExpression? budget o names captured store (groups spans (ref span name)) = some (actual,store) := by
  induction spans generalizing budget with
  | nil =>
      cases budget with
      | zero => simp at large
      | succ n => simp [groups,ref,evaluateClosedSourceExpression?,
          LocalNameTable.lookup?_iff.mpr named,Resolved.LocalScope.lookup?_iff.mpr found]
  | cons s rest ih =>
      cases budget with
      | zero => simp at large
      | succ n => simpa only [groups,evaluateClosedSourceExpression?] using
          (ih n (by simp only [List.length_cons] at large; omega))
private def depth (first second : Leaf) : List Leaf → Nat
  | [] => 1+max (first.groups.length+1) (second.groups.length+1)
  | third::rest => 1+max (first.groups.length+1) (depth second third rest)
private theorem tupleRun (o : Resolved.DeclarationId) (span delimiter : Syntax.SourceSpan)
    (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (first second : Leaf) (rest : List Leaf) (valid : ∀ leaf ∈ first::second::rest, Admits names captured leaf)
    (budget : Nat) (large : depth first second rest≤budget) :
    evaluateClosedSourceExpression? budget o names captured store
      (tuple span delimiter (leafSource first) (leafSource second) (rest.map leafSource)) =
      some (packed first.actual second.actual (rest.map Leaf.actual),store) := by
  induction rest generalizing first second budget with
  | nil =>
      cases budget with
      | zero => simp [depth] at large
      | succ n =>
          have left := groupRun o first.span first.name first.groups names captured store first.id first.actual
            (valid _ (by simp)).1 (valid _ (by simp)).2 n (by simp only [depth] at large; omega)
          have right := groupRun o second.span second.name second.groups names captured store second.id second.actual
            (valid _ (by simp)).1 (valid _ (by simp)).2 n (by simp only [depth] at large; omega)
          simp only [tuple,leafSource,List.map_nil,packed,evaluateClosedSourceExpression?,left,right,
            bind,Option.bind_some,pure]
  | cons third rest ih =>
      cases budget with
      | zero => simp [depth] at large
      | succ n =>
          have left := groupRun o first.span first.name first.groups names captured store first.id first.actual
            (valid _ (by simp)).1 (valid _ (by simp)).2 n (by simp only [depth] at large; omega)
          have right := ih second third (fun leaf member => valid leaf (List.mem_cons_of_mem _ member)) n
            (by simp only [depth] at large; omega)
          simp only [tuple,leafSource] at right
          simp only [tuple,leafSource,List.map_cons,packed,evaluateClosedSourceExpression?,left,right,
            bind,Option.bind_some,pure]

theorem heterogeneous_original_tuple_computes_at_its_structural_depth
    (o : Resolved.DeclarationId) (span delimiter : Syntax.SourceSpan) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (first second : Leaf) (rest : List Leaf) (valid : ∀ leaf ∈ first::second::rest, Admits names captured leaf)
    (budget : Nat) (large : depth first second rest≤budget) :
    let source := tuple span delimiter (leafSource first) (leafSource second) (rest.map leafSource)
    let result := packed first.actual second.actual (rest.map Leaf.actual)
    evaluateClosedSourceExpression? budget o names captured store source = some (result,store) ∧
      E o names captured store source result store := by
  have computed := tupleRun o span delimiter names captured store first second rest valid budget large
  exact ⟨computed,evaluateClosedSourceExpression?_sound computed⟩

theorem independent_heterogeneous_tuple_is_found_at_every_sufficiently_large_budget
    (o : Resolved.DeclarationId) (span delimiter : Syntax.SourceSpan) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (first second : Leaf) (rest : List Leaf) (valid : ∀ leaf ∈ first::second::rest, Admits names captured leaf) :
    ∃ required, ∀ budget, required≤budget →
      evaluateClosedSourceExpression? budget o names captured store
        (tuple span delimiter (leafSource first) (leafSource second) (rest.map leafSource)) =
        some (packed first.actual second.actual (rest.map Leaf.actual),store) :=
  evaluateClosedSourceExpression?_eventually_complete (tuplePath _ _ _ _ _ _ _ _ _ valid)

theorem all_nine_original_body_rules_and_arbitrary_shadows_are_eventually_found
    (o : Resolved.DeclarationId) (span delimiter : Syntax.SourceSpan) (name condition : Syntax.Identifier)
    (annotation : Syntax.TypeExpr) (second : Leaf) (rest : List Leaf)
    (unused : List Syntax.MatchCase) (defaultBody : Option Syntax.Block) (n : Nat)
    (actual : RuntimeValue) (side : Bool) (store : List RuntimeValue)
    (different : name.value≠condition.value) (unshadowed : ∀ leaf ∈ second::rest, name.value≠leaf.name.value)
    (rows : Rows name condition (second::rest) actual side) :
    let source := body span delimiter name condition annotation second rest unused defaultBody n
    let result := if side then packed actual second.actual (rest.map Leaf.actual) else .unit
    B o rows.names rows.captured store source result store ∧
      ∃ required, ∀ budget, required≤budget →
        evaluateClosedSourceBody? budget o rows.names rows.captured store source = some (result,store) := by
  have independent := bodyPath o span delimiter name condition annotation second rest unused defaultBody
    n actual side store different unshadowed rows
  exact ⟨independent,evaluateClosedSourceBody?_eventually_complete independent⟩

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

theorem arbitrary_comparison_count_is_not_the_body_depth_budget
    (o : Resolved.DeclarationId) (span marker : Syntax.SourceSpan) (name : Syntax.Identifier)
    (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (id : Resolved.LocalId) (word : Core.Word) (different : word≠.zero)
    (misses : List (Syntax.SourceSpan × Syntax.Block)) (unused : List Syntax.MatchCase)
    (defaultBody : Option Syntax.Block) (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id (.word word)) :
    let selected := returned span (ref span name)
    let cases := missedCases span marker selected unused misses
    let source := matched span (ref span name) cases defaultBody
    chooseRuntimeWordMatch? (.word word) cases defaultBody = some (selected,misses.length) ∧
      evaluateClosedSourceBody? 2 o names captured store source = none ∧
      evaluateClosedSourceBody? 3 o names captured store source = some (.word word,store) ∧
      B o names captured store source (.word word) store := by
  have original := missPath span marker (returned span (ref span name)) unused defaultBody word different misses
  have selection := chooseRuntimeWordMatch?_iff.mpr original
  simp only [returned,ref] at selection
  have computed : evaluateClosedSourceBody? 3 o names captured store
      (matched span (ref span name) (missedCases span marker (returned span (ref span name)) unused misses) defaultBody) =
      some (.word word,store) := by
    simp only [matched,evaluateClosedSourceBody?,ref,evaluateClosedSourceExpression?,
      LocalNameTable.lookup?_iff.mpr named,Resolved.LocalScope.lookup?_iff.mpr found,
      bind,Option.bind_some,pure,selection,returned]
  refine ⟨selection,?_,computed,evaluateClosedSourceBody?_sound computed⟩
  simp only [matched,evaluateClosedSourceBody?,ref,evaluateClosedSourceExpression?,
    LocalNameTable.lookup?_iff.mpr named,Resolved.LocalScope.lookup?_iff.mpr found,
    bind,Option.bind_some,pure,selection,returned]

end Tests.FrontendClosedSourceBodyRunner
end

section
-- leanmerge: from Solcore.Test.FrontendClosedSourceBoundaryProperties
/- Boundary consumers for the callback-free syntax fragment.
Successful store invariance is not termination or a fault classifier. -/
set_option autoImplicit false
open Solcore Solcore.Frontend

namespace Tests.ClosedSourceBoundaries

theorem expression_success_keeps_the_actual_store
    {owner names captured initialStore source value finalStore}
    (evaluated : ClosedSourceExpressionEvaluates owner names captured initialStore source value finalStore) :
    finalStore = initialStore := by
  induction evaluated using ClosedSourceExpressionEvaluates.rec
    (motive_2 := fun _ _ _ initialStore _ _ finalStore _ => finalStore = initialStore) with
  | reference _ _ => rfl
  | unit => rfl
  | wordLiteral _ => rfl
  | group _ ih => exact ih
  | pair _ _ leftIH rightIH => exact rightIH.trans leftIH
  | many _ _ headIH tailIH => exact tailIH.trans headIH
  | creation _ => rfl
  | call _ _ _ _ calleeIH argumentIH bodyIH =>
      exact bodyIH.trans (argumentIH.trans calleeIH)
  | conditionalTrue _ _ conditionIH branchIH => exact branchIH.trans conditionIH
  | conditionalFalse _ _ conditionIH branchIH => exact branchIH.trans conditionIH
  | logicalNot _ ih => exact ih
  | bitNot _ ih => exact ih
  | andTrue _ _ leftIH rightIH => exact rightIH.trans leftIH
  | andFalse _ leftIH => exact leftIH
  | orTrue _ leftIH => exact leftIH
  | orFalse _ _ leftIH rightIH => exact rightIH.trans leftIH
  | strictWordBinary _ _ _ leftIH rightIH => exact rightIH.trans leftIH
  | bare => rfl
  | expression _ ih => exact ih
  | block _ ih => exact ih
  | binding _ _ initializerIH tailIH => exact tailIH.trans initializerIH
  | inferred _ _ initializerIH tailIH => exact tailIH.trans initializerIH
  | discard _ _ expressionIH tailIH => exact tailIH.trans expressionIH
  | ifTrue _ _ conditionIH branchIH => exact branchIH.trans conditionIH
  | ifFalse _ _ conditionIH branchIH => exact branchIH.trans conditionIH
  | wordMatch _ _ _ scrutineeIH branchIH => exact branchIH.trans scrutineeIH

theorem body_success_keeps_the_actual_store
    {owner names captured initialStore source value finalStore}
    (evaluated : ClosedSourceBodyEvaluates owner names captured initialStore source value finalStore) :
    finalStore = initialStore := by
  have original := closedSourceBodyEvaluates_iff.mp evaluated
  clear evaluated
  induction original with
  | bare => rfl
  | expression child => exact expression_success_keeps_the_actual_store child
  | block _ ih => exact ih
  | binding child _ ih => exact ih.trans (expression_success_keeps_the_actual_store child)
  | inferred child _ ih => exact ih.trans (expression_success_keeps_the_actual_store child)
  | discard child _ ih => exact ih.trans (expression_success_keeps_the_actual_store child)
  | ifTrue child _ ih => exact ih.trans (expression_success_keeps_the_actual_store child)
  | ifFalse child _ ih => exact ih.trans (expression_success_keeps_the_actual_store child)
  | wordMatch child _ _ ih => exact ih.trans (expression_success_keeps_the_actual_store child)

theorem manual_singleton_tuple_has_no_success
    {owner names captured initialStore span tupleSpan child value finalStore} :
    ¬ ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .tuple ⟨tupleSpan, [child]⟩⟩ value finalStore := by
  intro evaluated
  cases evaluated with
  | creation shape => cases shape

theorem a_non_source_callee_has_no_unary_call
    {owner names captured initialStore callee calleeValue calleeStore}
    (calleeEvaluation : ClosedSourceExpressionEvaluates owner names captured initialStore
      callee calleeValue calleeStore)
    (notSource : ∀ source savedOwner savedNames savedCaptured,
      calleeValue ≠ RuntimeValue.sourceClosure source savedOwner savedNames savedCaptured)
    {span argumentsSpan argument value finalStore} :
    ¬ ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ value finalStore := by
  intro evaluated
  obtain ⟨_, _, _, _, _, _, _, _, _, _, otherCallee, _, _⟩ :=
    SourceLambdaEvaluates.call_iff.mp (closedSourceExpressionEvaluates_call_iff.mp evaluated)
  exact notSource _ _ _ _ (calleeEvaluation.deterministic otherCallee).1

theorem arbitrary_core_closures_are_inert_call_targets
    {owner names captured initialStore referenceSpan name id parameterType resultType code captures}
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id
      (RuntimeValue.coreClosure parameterType resultType code captures))
    {span argumentsSpan argument value finalStore} :
    ¬ ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .call ⟨referenceSpan, .identifier name⟩ ⟨argumentsSpan, [argument]⟩⟩ value finalStore :=
  a_non_source_callee_has_no_unary_call (.reference named found)
    (by intro source savedOwner savedNames savedCaptured impossible; cases impossible)

theorem arbitrary_host_functions_are_inert_call_targets
    {owner names captured initialStore referenceSpan name id host}
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id (RuntimeValue.hostFunction host))
    {span argumentsSpan argument value finalStore} :
    ¬ ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .call ⟨referenceSpan, .identifier name⟩ ⟨argumentsSpan, [argument]⟩⟩ value finalStore :=
  a_non_source_callee_has_no_unary_call (.reference named found)
    (by intro source savedOwner savedNames savedCaptured impossible; cases impossible)

theorem creation_with_empty_body_does_not_execute_it
    {owner names captured store source name bodySpan}
    (shape : SourceUnaryLambdaShape source name ⟨bodySpan, []⟩)
    {span argumentsSpan argument value finalStore} :
    ClosedSourceExpressionEvaluates owner names captured store source
        (.sourceClosure source owner names captured) store ∧
      ¬ ClosedSourceExpressionEvaluates owner names captured store
        ⟨span, .call source ⟨argumentsSpan, [argument]⟩⟩ value finalStore := by
  constructor
  · exact .creation shape
  · intro evaluated
    obtain ⟨_, _, _, _, _, _, _, _, _, otherShape, otherCallee, _, otherBody⟩ :=
      SourceLambdaEvaluates.call_iff.mp (closedSourceExpressionEvaluates_call_iff.mp evaluated)
    obtain ⟨sameCallee, sameStore⟩ :=
      ClosedSourceExpressionEvaluates.deterministic (.creation shape) otherCallee
    cases sameCallee
    cases sameStore
    have sameShape := Prod.mk.inj (Option.some.inj
      ((sourceUnaryLambdaShape?_iff.mpr shape).symm.trans
        (sourceUnaryLambdaShape?_iff.mpr otherShape)))
    obtain ⟨rfl, rfl⟩ := sameShape
    cases otherBody

theorem zero_and_multiple_arguments_have_no_success
    {owner names captured store span argumentsSpan callee first second rest value finalStore} :
    (¬ ClosedSourceExpressionEvaluates owner names captured store
      ⟨span, .call callee ⟨argumentsSpan, []⟩⟩ value finalStore) ∧
    (¬ ClosedSourceExpressionEvaluates owner names captured store
      ⟨span, .call callee ⟨argumentsSpan, first :: second :: rest⟩⟩ value finalStore) := by
  constructor
  · intro evaluated
    cases evaluated with
    | creation shape => cases shape
  · intro evaluated
    cases evaluated with
    | creation shape => cases shape

end Tests.ClosedSourceBoundaries
end

section
-- leanmerge: from Solcore.Test.FrontendClosedSourceCallProperties
/-! Original symbolic call towers are evaluated by closed constructors, not by
assumed callbacks. Every capture, annotation and raw store remains literal.
These are successful derivations, not execution-cost or termination bounds. -/
set_option autoImplicit false
namespace Tests.FrontendClosedSourceCall
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates
private def ref (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span,.identifier name⟩
private def returned (span : Syntax.SourceSpan) (value : Syntax.Expr) : Syntax.Block :=
  ⟨span,[⟨span,.returnStmt (some value)⟩]⟩
private def lambda (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (body : Syntax.Block) : Syntax.Expr :=
  ⟨span,.lambda span ⟨name.span,[⟨name.span,match annotation with
    | none => .inferred name | some type => .typed none name type⟩]⟩ returns body⟩
private theorem shape (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (body : Syntax.Block) :
    SourceUnaryLambdaShape (lambda span name annotation returns body) name body := by
  cases annotation <;> first | exact .inferred | exact .typed
private def app (span : Syntax.SourceSpan) (callee argument : Syntax.Expr) : Syntax.Expr :=
  ⟨span,.call callee ⟨span,[argument]⟩⟩
private def tower (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) : Nat → Syntax.Expr
  | 0 => ref span name
  | n+1 => app span (lambda span name annotation returns
      (returned span (tower span name annotation returns n))) (ref span name)
private theorem towerPath (o : Resolved.DeclarationId) (span : Syntax.SourceSpan)
    (name : Syntax.Identifier) (annotation returns : Option Syntax.TypeExpr) (n : Nat)
    (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (id : Resolved.LocalId) (actual : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id actual) :
    E o names captured store (tower span name annotation returns n) actual store := by
  induction n generalizing names captured id with
  | zero => exact .reference named found
  | succ n ih =>
      exact .call (shape _ _ _ _ _) (.creation (shape _ _ _ _ _))
        (.reference named found) (.expression (ih _ _ _ .head .head))
private def source (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (n : Nat) : Syntax.Expr :=
  lambda span name annotation returns (returned span (tower span name annotation returns n))
private def call (span : Syntax.SourceSpan) : Syntax.Expr :=
  app span (ref span ⟨span,"f"⟩) (ref span ⟨span,"argument"⟩)
private def callerNames (f x : Resolved.LocalId) (tail : LocalNameTable) : LocalNameTable :=
  ("f",f)::("argument",x)::tail
private def callerValues (f x : Resolved.LocalId) (closure actual : RuntimeValue)
    (tail : Resolved.LocalScope RuntimeValue) : Resolved.LocalScope RuntimeValue :=
  (f,closure)::(x,actual)::tail
private theorem invoke (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (n : Nat) (caller saved : Resolved.DeclarationId)
    (names callerTail : LocalNameTable) (captured callerSuffix : Resolved.LocalScope RuntimeValue)
    (f x : Resolved.LocalId) (different : f≠x) (actual : RuntimeValue) (store : List RuntimeValue) :
    E caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure (source span name annotation returns n) saved names captured) actual callerSuffix)
      store (call span) actual store :=
  .call (shape _ _ _ _ _) (.reference .head .head)
    (.reference (.tail (by change "f" ≠ "argument"; decide) .head) (.tail different .head))
    (.expression (towerPath _ _ _ _ _ _ _ _ _ _ _ .head .head))
private theorem freshNe {o : Resolved.DeclarationId} {names : LocalNameTable}
    {name : String} {id : Resolved.LocalId} (named : LocalNameTable.Lookup names name id) :
    Resolved.freshLocalId o (names.map Prod.snd) ≠ id := by
  intro same
  have member : id ∈ names.map Prod.snd := List.mem_map_of_mem named.mem
  exact Resolved.freshLocalId_not_mem o _ (same ▸ member)

theorem arbitrary_original_call_depth_returns_the_actual_value
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (n : Nat) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (id : Resolved.LocalId) (actual : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id actual) :
    E o names captured store (tower span name annotation returns n) actual store :=
  towerPath _ _ _ _ _ _ _ _ _ _ _ named found

theorem each_nested_callee_captures_every_current_row
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (n : Nat) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) :
    E o names captured store (source span name annotation returns n)
      (.sourceClosure (source span name annotation returns n) o names captured) store :=
  .creation (shape _ _ _ _ _)

theorem saved_owner_calls_shadow_old_names_and_capture_only_collisions
    (span : Syntax.SourceSpan) (name : Syntax.Identifier) (annotation returns : Option Syntax.TypeExpr)
    (n : Nat) (caller saved : Resolved.DeclarationId) (names callerTail : LocalNameTable)
    (captured callerSuffix : Resolved.LocalScope RuntimeValue) (oldId f x : Resolved.LocalId)
    (different : f≠x) (old collision actual : RuntimeValue) (store : List RuntimeValue) :
    let savedNames := (name.value,oldId)::names
    let rows := (Resolved.freshLocalId saved (savedNames.map Prod.snd),collision)::(oldId,old)::captured
    E caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure (source span name annotation returns n) saved savedNames rows)
        actual callerSuffix) store (call span) actual store :=
  invoke _ _ _ _ _ _ _ _ _ _ _ _ _ different _ _

theorem original_open_call_has_the_same_exact_endpoint_without_child_laws
    (span : Syntax.SourceSpan) (name : Syntax.Identifier) (annotation returns : Option Syntax.TypeExpr)
    (n : Nat) (caller saved : Resolved.DeclarationId) (names callerTail : LocalNameTable)
    (captured callerSuffix : Resolved.LocalScope RuntimeValue) (f x : Resolved.LocalId)
    (different : f≠x) (actual result : RuntimeValue) (store final : List RuntimeValue) :
    SourceLambdaEvaluates E (SourceComputationBodyEvaluates E) caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure (source span name annotation returns n) saved names captured) actual callerSuffix)
      store (call span) result final ↔ result=actual ∧ final=store := by
  have independent := invoke span name annotation returns n caller saved names callerTail
    captured callerSuffix f x different actual store
  constructor
  · intro evaluated
    exact (closedSourceExpressionEvaluates_call_iff.mpr evaluated).deterministic independent
  · rintro ⟨rfl,rfl⟩
    exact closedSourceExpressionEvaluates_call_iff.mp independent

theorem tower_result_and_store_are_unconditionally_unique
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (n : Nat) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store final : List RuntimeValue)
    (id : Resolved.LocalId) (actual result : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id actual)
    (other : E o names captured store (tower span name annotation returns n) result final) :
    result=actual ∧ final=store :=
  other.deterministic (towerPath _ _ _ _ _ _ _ _ _ _ _ named found)

theorem a_returned_source_closure_uses_its_own_saved_capture
    (span : Syntax.SourceSpan) (parameter selected : Syntax.Identifier)
    (notParameter : parameter.value≠selected.value) (annotation returns : Option Syntax.TypeExpr)
    (n : Nat) (caller saved : Resolved.DeclarationId) (savedNames callerTail : LocalNameTable)
    (savedValues callerSuffix : Resolved.LocalScope RuntimeValue) (f x selectedId : Resolved.LocalId)
    (different : f≠x) (argument result : RuntimeValue) (store : List RuntimeValue)
    (named : LocalNameTable.Lookup savedNames selected.value selectedId)
    (found : Resolved.LocalScope.Lookup savedValues selectedId result) :
    let original := lambda span parameter annotation returns (returned span (ref span selected))
    E caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure original saved savedNames savedValues) argument callerSuffix) store
      (app span (tower span ⟨span,"f"⟩ annotation returns n) (ref span ⟨span,"argument"⟩)) result store := by
  apply ClosedSourceExpressionEvaluates.call (shape _ _ _ _ _)
  · exact towerPath _ _ _ _ _ _ _ _ _ _ _ .head .head
  · exact .reference (.tail (by change "f" ≠ "argument"; decide) .head) (.tail different .head)
  · exact .expression (.reference (.tail notParameter named) (.tail (freshNe named) found))

end Tests.FrontendClosedSourceCall
end

section
-- leanmerge: from Solcore.Test.FrontendClosedSourceCallRunnerProperties
/-! Original symbolic call towers are evaluated by closed constructors, not by
assumed callbacks. Every capture, annotation and raw store remains literal.
The thresholds measure search depth, not execution cost or general termination. -/
set_option autoImplicit false
namespace Tests.FrontendClosedSourceCallRunner
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates
private def ref (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span,.identifier name⟩
private def returned (span : Syntax.SourceSpan) (value : Syntax.Expr) : Syntax.Block :=
  ⟨span,[⟨span,.returnStmt (some value)⟩]⟩
private def lambda (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (body : Syntax.Block) : Syntax.Expr :=
  ⟨span,.lambda span ⟨name.span,[⟨name.span,match annotation with
    | none => .inferred name | some type => .typed none name type⟩]⟩ returns body⟩
private theorem shape (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (body : Syntax.Block) :
    SourceUnaryLambdaShape (lambda span name annotation returns body) name body := by
  cases annotation <;> first | exact .inferred | exact .typed
private def app (span : Syntax.SourceSpan) (callee argument : Syntax.Expr) : Syntax.Expr :=
  ⟨span,.call callee ⟨span,[argument]⟩⟩
private def tower (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) : Nat → Syntax.Expr
  | 0 => ref span name
  | n+1 => app span (lambda span name annotation returns
      (returned span (tower span name annotation returns n))) (ref span name)
private theorem towerPath (o : Resolved.DeclarationId) (span : Syntax.SourceSpan)
    (name : Syntax.Identifier) (annotation returns : Option Syntax.TypeExpr) (n : Nat)
    (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (id : Resolved.LocalId) (actual : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id actual) :
    E o names captured store (tower span name annotation returns n) actual store := by
  induction n generalizing names captured id with
  | zero => exact .reference named found
  | succ n ih =>
      exact .call (shape _ _ _ _ _) (.creation (shape _ _ _ _ _))
        (.reference named found) (.expression (ih _ _ _ .head .head))
private def source (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (n : Nat) : Syntax.Expr :=
  lambda span name annotation returns (returned span (tower span name annotation returns n))
private def call (span : Syntax.SourceSpan) : Syntax.Expr :=
  app span (ref span ⟨span,"f"⟩) (ref span ⟨span,"argument"⟩)
private def callerNames (f x : Resolved.LocalId) (tail : LocalNameTable) : LocalNameTable :=
  ("f",f)::("argument",x)::tail
private def callerValues (f x : Resolved.LocalId) (closure actual : RuntimeValue)
    (tail : Resolved.LocalScope RuntimeValue) : Resolved.LocalScope RuntimeValue :=
  (f,closure)::(x,actual)::tail
private theorem invoke (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (n : Nat) (caller saved : Resolved.DeclarationId)
    (names callerTail : LocalNameTable) (captured callerSuffix : Resolved.LocalScope RuntimeValue)
    (f x : Resolved.LocalId) (different : f≠x) (actual : RuntimeValue) (store : List RuntimeValue) :
    E caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure (source span name annotation returns n) saved names captured) actual callerSuffix)
      store (call span) actual store :=
  .call (shape _ _ _ _ _) (.reference .head .head)
    (.reference (.tail (by change "f" ≠ "argument"; decide) .head) (.tail different .head))
    (.expression (towerPath _ _ _ _ _ _ _ _ _ _ _ .head .head))
private theorem freshNe {o : Resolved.DeclarationId} {names : LocalNameTable}
    {name : String} {id : Resolved.LocalId} (named : LocalNameTable.Lookup names name id) :
    Resolved.freshLocalId o (names.map Prod.snd) ≠ id := by
  intro same
  have member : id ∈ names.map Prod.snd := List.mem_map_of_mem named.mem
  exact Resolved.freshLocalId_not_mem o _ (same ▸ member)

private theorem towerRun (o : Resolved.DeclarationId) (span : Syntax.SourceSpan)
    (name : Syntax.Identifier) (annotation returns : Option Syntax.TypeExpr) (n budget : Nat)
    (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (id : Resolved.LocalId) (actual : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id actual) :
    evaluateClosedSourceExpression? budget o names captured store (tower span name annotation returns n) =
      if 2*n+1≤budget then some (actual,store) else none := by
  induction n generalizing budget names captured id with
  | zero =>
      cases budget <;> simp [tower,ref,evaluateClosedSourceExpression?,
        LocalNameTable.lookup?_iff.mpr named,Resolved.LocalScope.lookup?_iff.mpr found]
  | succ n ih =>
      cases budget with
      | zero => simp [evaluateClosedSourceExpression?]
      | succ budget =>
          cases budget with
          | zero => simp [tower,app,evaluateClosedSourceExpression?]
          | succ k =>
              let fresh := Resolved.freshLocalId o (names.map Prod.snd)
              have inner := ih k ((name.value,fresh)::names) ((fresh,actual)::captured) fresh .head .head
              cases annotation <;>
                simpa [tower,app,lambda,returned,evaluateClosedSourceExpression?,evaluateClosedSourceBody?,
                  sourceUnaryLambdaShape?,ref,LocalNameTable.lookup?_iff.mpr named,
                  Resolved.LocalScope.lookup?_iff.mpr found,
                  show (2*(n+1)+1≤k+2) ↔ (2*n+1≤k) by omega] using inner

private theorem invokeRun (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (n budget : Nat) (caller saved : Resolved.DeclarationId)
    (names callerTail : LocalNameTable) (captured callerSuffix : Resolved.LocalScope RuntimeValue)
    (f x : Resolved.LocalId) (different : f≠x) (actual : RuntimeValue) (store : List RuntimeValue) :
    evaluateClosedSourceExpression? budget caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure (source span name annotation returns n) saved names captured) actual callerSuffix)
      store (call span) = if 2*n+3≤budget then some (actual,store) else none := by
  cases budget with
  | zero => simp [evaluateClosedSourceExpression?]
  | succ budget =>
      cases budget with
      | zero => simp [call,app,evaluateClosedSourceExpression?]
      | succ budget =>
          cases budget with
          | zero =>
              cases annotation <;> simp [call,app,ref,source,lambda,returned,evaluateClosedSourceExpression?,
                evaluateClosedSourceBody?,callerNames,callerValues,LocalNameTable.lookup?,Resolved.LocalScope.lookup?,
                different,sourceUnaryLambdaShape?]
          | succ k =>
              let fresh := Resolved.freshLocalId saved (names.map Prod.snd)
              have inner := towerRun saved span name annotation returns n (k+1)
                ((name.value,fresh)::names) ((fresh,actual)::captured) store fresh actual .head .head
              cases annotation <;>
                simpa [call,app,ref,source,lambda,returned,evaluateClosedSourceExpression?,evaluateClosedSourceBody?,
                  callerNames,callerValues,LocalNameTable.lookup?,Resolved.LocalScope.lookup?,different,
                  sourceUnaryLambdaShape?,show (2*n+3≤k+3) ↔ (2*n+1≤k+1) by omega] using inner

theorem arbitrary_tower_has_exact_depth_threshold
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (n budget : Nat) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (id : Resolved.LocalId) (actual : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id actual) :
    evaluateClosedSourceExpression? budget o names captured store (tower span name annotation returns n) =
      if 2*n+1≤budget then some (actual,store) else none := towerRun _ _ _ _ _ _ _ _ _ _ _ _ named found

theorem independent_original_tower_is_eventually_found
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (n : Nat) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (id : Resolved.LocalId) (actual : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id actual) :
    E o names captured store (tower span name annotation returns n) actual store ∧
      ∃ required, ∀ budget, required≤budget →
        evaluateClosedSourceExpression? budget o names captured store (tower span name annotation returns n) = some (actual,store) := by
  have independent := towerPath o span name annotation returns n names captured store id actual named found
  exact ⟨independent,evaluateClosedSourceExpression?_eventually_complete independent⟩

theorem direct_computation_at_the_threshold_supplies_soundness
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation returns : Option Syntax.TypeExpr) (n : Nat) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (id : Resolved.LocalId) (actual : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id actual) :
    E o names captured store (tower span name annotation returns n) actual store := by
  have computed := towerRun o span name annotation returns n (2*n+1) names captured store id actual named found
  exact evaluateClosedSourceExpression?_sound (by simpa only [Nat.le_refl,↓reduceIte] using computed)

theorem saved_owner_and_capture_only_collision_keep_the_exact_call_threshold
    (span : Syntax.SourceSpan) (name : Syntax.Identifier) (annotation returns : Option Syntax.TypeExpr)
    (n budget : Nat) (caller saved : Resolved.DeclarationId) (names callerTail : LocalNameTable)
    (captured callerSuffix : Resolved.LocalScope RuntimeValue) (oldId f x : Resolved.LocalId)
    (different : f≠x) (old collision actual : RuntimeValue) (store : List RuntimeValue) :
    let savedNames := (name.value,oldId)::names
    let rows := (Resolved.freshLocalId saved (savedNames.map Prod.snd),collision)::(oldId,old)::captured
    E caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure (source span name annotation returns n) saved savedNames rows) actual callerSuffix)
      store (call span) actual store ∧
    evaluateClosedSourceExpression? budget caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure (source span name annotation returns n) saved savedNames rows) actual callerSuffix)
      store (call span) = if 2*n+3≤budget then some (actual,store) else none :=
  ⟨invoke _ _ _ _ _ _ _ _ _ _ _ _ _ different _ _,
    invokeRun _ _ _ _ _ _ _ _ _ _ _ _ _ _ different _ _⟩

theorem a_returned_higher_order_closure_eventually_uses_its_saved_capture
    (span : Syntax.SourceSpan) (parameter selected : Syntax.Identifier)
    (notParameter : parameter.value≠selected.value) (annotation returns : Option Syntax.TypeExpr)
    (n : Nat) (caller saved : Resolved.DeclarationId) (savedNames callerTail : LocalNameTable)
    (savedValues callerSuffix : Resolved.LocalScope RuntimeValue) (f x selectedId : Resolved.LocalId)
    (different : f≠x) (argument result : RuntimeValue) (store : List RuntimeValue)
    (named : LocalNameTable.Lookup savedNames selected.value selectedId)
    (found : Resolved.LocalScope.Lookup savedValues selectedId result) :
    let original := lambda span parameter annotation returns (returned span (ref span selected))
    let ns := callerNames f x callerTail
    let es := callerValues f x (.sourceClosure original saved savedNames savedValues) argument callerSuffix
    let expression := app span (tower span ⟨span,"f"⟩ annotation returns n) (ref span ⟨span,"argument"⟩)
    E caller ns es store expression result store ∧ ∃ required, ∀ budget, required≤budget →
      evaluateClosedSourceExpression? budget caller ns es store expression = some (result,store) := by
  dsimp only
  have independent : E caller (callerNames f x callerTail)
      (callerValues f x (.sourceClosure (lambda span parameter annotation returns (returned span (ref span selected)))
        saved savedNames savedValues) argument callerSuffix) store
      (app span (tower span ⟨span,"f"⟩ annotation returns n) (ref span ⟨span,"argument"⟩)) result store := by
    apply ClosedSourceExpressionEvaluates.call (shape _ _ _ _ _)
    · exact towerPath _ _ _ _ _ _ _ _ _ _ _ .head .head
    · exact .reference (.tail (by change "f" ≠ "argument"; decide) .head) (.tail different .head)
    · exact .expression (.reference (.tail notParameter named) (.tail (freshNe named) found))
  exact ⟨independent,evaluateClosedSourceExpression?_eventually_complete independent⟩

end Tests.FrontendClosedSourceCallRunner
end

section
-- leanmerge: from Solcore.Test.FrontendClosedSourceConditionalBoundaryProperties
/- Original conditional boundaries consume independent judgments and direct
computations separately. No typing, failure classification or cost claim. -/
set_option autoImplicit false
open Solcore Solcore.Frontend

namespace Tests.ClosedSourceConditionalBoundaries

/-- A previously evaluated actual Bool fixes the original selected child and store. -/
theorem fixed_guard_selects_exact_original_branch
    {owner names captured initialStore middleStore finalStore condition choice}
    (guard : ClosedSourceExpressionEvaluates owner names captured initialStore
      condition (.bool choice) middleStore)
    {span question colon thenBranch elseBranch value} :
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .conditional condition question thenBranch colon elseBranch⟩ value finalStore ↔
    ClosedSourceExpressionEvaluates owner names captured middleStore
      (if choice then thenBranch else elseBranch) value finalStore := by
  constructor
  · intro evaluated
    obtain ⟨other, otherStore, otherGuard, selected⟩ :=
      closedSourceExpressionEvaluates_conditional_iff.mp evaluated
    obtain ⟨same, rfl⟩ := guard.deterministic otherGuard
    cases same
    exact selected
  · intro selected
    exact closedSourceExpressionEvaluates_conditional_iff.mpr
      ⟨choice, middleStore, guard, selected⟩

/-- Original marker spans and unselected syntax need no evaluation premise. -/
theorem changing_only_unselected_branch_preserves_endpoint
    {owner names captured initialStore middleStore finalStore condition choice}
    (guard : ClosedSourceExpressionEvaluates owner names captured initialStore
      condition (.bool choice) middleStore)
    {span question colon selected ignored replacement value} :
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .conditional condition question
        (if choice then selected else ignored) colon (if choice then ignored else selected)⟩
      value finalStore ↔
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .conditional condition question
        (if choice then selected else replacement) colon (if choice then replacement else selected)⟩
      value finalStore := by
  rw [fixed_guard_selects_exact_original_branch guard,
    fixed_guard_selects_exact_original_branch guard]
  cases choice <;> rfl

/-- An actual non-Bool guard cannot be reinterpreted from source spelling. -/
theorem actual_non_boolean_guard_has_no_derivation
    {owner names captured initialStore middleStore condition actual}
    (guard : ClosedSourceExpressionEvaluates owner names captured initialStore
      condition actual middleStore)
    (notBool : ∀ choice, actual ≠ RuntimeValue.bool choice)
    {span question colon thenBranch elseBranch value finalStore} :
    ¬ ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .conditional condition question thenBranch colon elseBranch⟩ value finalStore := by
  intro evaluated
  obtain ⟨choice, _, otherGuard, _⟩ :=
    closedSourceExpressionEvaluates_conditional_iff.mp evaluated
  exact notBool choice (guard.deterministic otherGuard).1

/-- All-depth absence for a known non-Bool is not a general None classifier. -/
theorem actual_non_boolean_guard_has_no_success_at_any_depth
    {owner names captured initialStore middleStore condition actual}
    (guard : ClosedSourceExpressionEvaluates owner names captured initialStore
      condition actual middleStore)
    (notBool : ∀ choice, actual ≠ RuntimeValue.bool choice)
    (budget : Nat) (span question colon : Syntax.SourceSpan)
    (thenBranch elseBranch : Syntax.Expr) :
    evaluateClosedSourceExpression? budget owner names captured initialStore
      ⟨span, .conditional condition question thenBranch colon elseBranch⟩ = none := by
  cases computed : evaluateClosedSourceExpression? budget owner names captured initialStore
    ⟨span, .conditional condition question thenBranch colon elseBranch⟩ with
  | none => rfl
  | some endpoint =>
      rcases endpoint with ⟨value, finalStore⟩
      exact False.elim (actual_non_boolean_guard_has_no_derivation guard notBool
        (evaluateClosedSourceExpression?_sound computed))

/-- Direct depth computations are paired with an independent original derivation. -/
theorem direct_unit_choice_has_exact_depth_two
    {owner names captured store id choice} {name : Syntax.Identifier}
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id (RuntimeValue.bool choice))
    (span question colon guardSpan unitSpan tupleSpan : Syntax.SourceSpan)
    (ignored : Syntax.Expr) :
    let unitSource : Syntax.Expr := ⟨unitSpan, .tuple ⟨tupleSpan, []⟩⟩
    let source : Syntax.Expr := ⟨span, .conditional ⟨guardSpan, .identifier name⟩ question
      (if choice then unitSource else ignored) colon (if choice then ignored else unitSource)⟩
    ClosedSourceExpressionEvaluates owner names captured store source .unit store ∧
      evaluateClosedSourceExpression? 0 owner names captured store source = none ∧
      evaluateClosedSourceExpression? 1 owner names captured store source = none ∧
      evaluateClosedSourceExpression? 2 owner names captured store source = some (.unit, store) := by
  dsimp only
  have guard : ClosedSourceExpressionEvaluates owner names captured store
      ⟨guardSpan, .identifier name⟩ (.bool choice) store := .reference named found
  constructor
  · apply (fixed_guard_selects_exact_original_branch guard).mpr
    cases choice <;> exact .unit
  · cases choice <;>
      simp only [evaluateClosedSourceExpression?_conditional,
        evaluateClosedSourceExpression?, LocalNameTable.lookup?_iff.mpr named,
        Resolved.LocalScope.lookup?_iff.mpr found, bind, Option.bind_some,
        Option.bind_none, pure, Bool.false_eq_true, ↓reduceIte, and_self]

/-- Selecting creation preserves the original source and all actual captured rows. -/
theorem selected_source_creation_keeps_every_saved_field
    {owner names captured initialStore middleStore condition choice}
    (guard : ClosedSourceExpressionEvaluates owner names captured initialStore
      condition (.bool choice) middleStore)
    {source name body} (shape : SourceUnaryLambdaShape source name body)
    (span question colon : Syntax.SourceSpan) (ignored : Syntax.Expr) :
    let conditional : Syntax.Expr := ⟨span, .conditional condition question
      (if choice then source else ignored) colon (if choice then ignored else source)⟩
    ClosedSourceExpressionEvaluates owner names captured initialStore conditional
        (.sourceClosure source owner names captured) middleStore ∧
      ∃ required, ∀ budget, required ≤ budget →
        evaluateClosedSourceExpression? budget owner names captured initialStore conditional =
          some (.sourceClosure source owner names captured, middleStore) := by
  dsimp only
  have selected : ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .conditional condition question (if choice then source else ignored) colon
        (if choice then ignored else source)⟩
      (.sourceClosure source owner names captured) middleStore := by
    apply (fixed_guard_selects_exact_original_branch guard).mpr
    cases choice <;> exact .creation shape
  exact ⟨selected, evaluateClosedSourceExpression?_eventually_complete selected⟩

end Tests.ClosedSourceConditionalBoundaries
end

section
-- leanmerge: from Solcore.Test.FrontendClosedSourceConditionalClosureProperties
/- A conditional initializer saves every lexical row before a later payload let.
Independent caller and saved lookups drive nested argument and body conditionals. -/
set_option autoImplicit false
namespace Tests.ClosedSourceConditionalClosure
open Solcore Solcore.Frontend

private structure Ranges where
  span : Nat → Syntax.SourceSpan
  outer : Nat → Syntax.SourceSpan
  question : Nat → Syntax.SourceSpan
  colon : Nat → Syntax.SourceSpan
  guard : Nat → Syntax.SourceSpan
  annotation : Syntax.TypeExpr

private structure Lexical where
  owner : Resolved.DeclarationId
  names : LocalNameTable
  captured : Resolved.LocalScope RuntimeValue
  gate : Syntax.Identifier
  payload : Syntax.Identifier
  parameter : Syntax.Identifier
  gateId : Resolved.LocalId
  payloadId : Resolved.LocalId
  choice : Bool
  kept : RuntimeValue
  gateNamed : LocalNameTable.Lookup names gate.value gateId
  gateFound : Resolved.LocalScope.Lookup captured gateId (.bool choice)
  payloadNamed : LocalNameTable.Lookup names payload.value payloadId
  payloadFound : Resolved.LocalScope.Lookup captured payloadId kept
  parameterGate : parameter.value ≠ gate.value
  parameterPayload : parameter.value ≠ payload.value

private def ref (r : Ranges) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨r.span 0, .identifier name⟩
private def unit (r : Ranges) : Syntax.Expr := ⟨r.span 1, .tuple ⟨r.span 2, []⟩⟩
private def nest (r : Ranges) (gate : Syntax.Identifier) :
    Nat → Syntax.Expr → Syntax.Expr → Syntax.Expr
  | 0, left, _ => left
  | n + 1, left, right =>
      ⟨r.outer n, .conditional ⟨r.guard n, .identifier gate⟩ (r.question n)
        (nest r gate n left right) (r.colon n) (nest r gate n right left)⟩
private def picked (choice : Bool) : Nat → RuntimeValue → RuntimeValue → RuntimeValue
  | 0, left, _ => left
  | n + 1, left, right =>
      if choice then picked choice n left right else picked choice n right left

private theorem nest_original (r : Ranges) (owner : Resolved.DeclarationId)
    (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (gate : Syntax.Identifier) (id : Resolved.LocalId)
    (choice : Bool) (named : LocalNameTable.Lookup names gate.value id)
    (found : Resolved.LocalScope.Lookup captured id (.bool choice))
    (n : Nat) (left right : Syntax.Expr) (lv rv : RuntimeValue)
    (le : ClosedSourceExpressionEvaluates owner names captured store left lv store)
    (re : ClosedSourceExpressionEvaluates owner names captured store right rv store) :
    ClosedSourceExpressionEvaluates owner names captured store
      (nest r gate n left right) (picked choice n lv rv) store := by
  induction n generalizing left right lv rv with
  | zero => exact le
  | succ n ih =>
      cases choice
      · exact .conditionalFalse (.reference named found) (ih right left rv lv re le)
      · exact .conditionalTrue (.reference named found) (ih left right lv rv le re)

private def body (r : Ranges) (l : Lexical) (n : Nat) (typed : Bool) : Syntax.Block :=
  ⟨r.span 3, [⟨r.span 4, .returnStmt (some (nest r l.gate n
    (if typed then ref r l.parameter else ref r l.payload)
    (if typed then ref r l.payload else ref r l.parameter)))⟩]⟩
private def source (r : Ranges) (l : Lexical) (n : Nat) (typed : Bool) : Syntax.Expr :=
  ⟨r.span 5, .lambda (r.span 6) ⟨r.span 7, [⟨r.span 8,
    if typed then .typed none l.parameter r.annotation else .inferred l.parameter⟩]⟩
    none (body r l n typed)⟩
private theorem shape (r : Ranges) (l : Lexical) (n : Nat) (typed : Bool) :
    SourceUnaryLambdaShape (source r l n typed) l.parameter (body r l n typed) := by
  cases typed
  · exact .inferred
  · exact .typed

private theorem fresh_ne {names : LocalNameTable} {name : String} {id : Resolved.LocalId}
    (owner : Resolved.DeclarationId) (named : LocalNameTable.Lookup names name id) :
    Resolved.freshLocalId owner (names.map Prod.snd) ≠ id := by
  intro same
  apply Resolved.freshLocalId_not_mem owner (names.map Prod.snd)
  rw [same]
  exact List.mem_map.mpr ⟨(name, id), named.mem, rfl⟩

private theorem saved_body (r : Ranges) (l : Lexical) (n : Nat) (typed : Bool)
    (argument : RuntimeValue) (store : List RuntimeValue) :
    ClosedSourceBodyEvaluates l.owner
      ((l.parameter.value, Resolved.freshLocalId l.owner (l.names.map Prod.snd)) :: l.names)
      ((Resolved.freshLocalId l.owner (l.names.map Prod.snd), argument) :: l.captured)
      store (body r l n typed)
      (picked l.choice n (if typed then argument else l.kept)
        (if typed then l.kept else argument)) store := by
  apply ClosedSourceBodyEvaluates.expression
  apply nest_original r l.owner _ _ store l.gate l.gateId l.choice
    (.tail l.parameterGate l.gateNamed) (.tail (fresh_ne l.owner l.gateNamed) l.gateFound)
  · cases typed
    · exact .reference (.tail l.parameterPayload l.payloadNamed)
        (.tail (fresh_ne l.owner l.payloadNamed) l.payloadFound)
    · exact .reference .head .head
  · cases typed
    · exact .reference .head .head
    · exact .reference (.tail l.parameterPayload l.payloadNamed)
        (.tail (fresh_ne l.owner l.payloadNamed) l.payloadFound)

private def closure (r : Ranges) (saved : Lexical) (n : Nat) (creation : Bool) : RuntimeValue :=
  .sourceClosure (source r saved n (!creation)) saved.owner saved.names saved.captured
private def producer (r : Ranges) (saved : Lexical) (n : Nat)
    (choose f : Syntax.Identifier) : Syntax.Block :=
  ⟨r.span 9, [⟨r.span 10, .letDecl f none (some
      ⟨r.span 11, .conditional (ref r choose) (r.span 12)
        (source r saved n false) (r.span 13) (source r saved n true)⟩)⟩,
    ⟨r.span 14, .letDecl saved.payload (some r.annotation) (some (unit r))⟩,
    ⟨r.span 15, .returnStmt (some (ref r f))⟩]⟩

variable (r : Ranges) (saved caller : Lexical) (n m : Nat) (store : List RuntimeValue)
  (creation : Bool) (choose f : Syntax.Identifier) (chooseId fId : Resolved.LocalId)
  (chooseNamed : LocalNameTable.Lookup saved.names choose.value chooseId)
  (chooseFound : Resolved.LocalScope.Lookup saved.captured chooseId (.bool creation))
  (different : saved.payload.value ≠ f.value)

include chooseNamed chooseFound different in
theorem original_pre_shadow_closure_is_returned :
    ClosedSourceBodyEvaluates saved.owner saved.names saved.captured store
      (producer r saved n choose f) (closure r saved n creation) store := by
  apply ClosedSourceBodyEvaluates.inferred (boundValue := closure r saved n creation)
    (middleStore := store)
  · cases creation
    · exact .conditionalFalse (.reference chooseNamed chooseFound) (.creation (shape r saved n true))
    · exact .conditionalTrue (.reference chooseNamed chooseFound) (.creation (shape r saved n false))
  · apply ClosedSourceBodyEvaluates.binding ClosedSourceExpressionEvaluates.unit
    apply ClosedSourceBodyEvaluates.expression
    apply ClosedSourceExpressionEvaluates.reference (.tail different .head)
    exact .tail (Resolved.freshLocalId_cons_fresh_ne saved.owner (saved.names.map Prod.snd)) .head

private def argument (r : Ranges) (caller : Lexical) (m : Nat) : Syntax.Expr :=
  nest r caller.gate m (ref r caller.payload) (unit r)
private def argumentValue (caller : Lexical) (m : Nat) : RuntimeValue :=
  picked caller.choice m caller.kept .unit
private def invocation (r : Ranges) (caller : Lexical) (n m : Nat)
    (f : Syntax.Identifier) : Syntax.Expr :=
  ⟨r.span 16, .call ⟨r.span 17, .conditional (ref r caller.gate) (r.span 18)
    (ref r f) (r.span 19) (source r caller n true)⟩
    ⟨r.span 20, [argument r caller m]⟩⟩
private def result (saved caller : Lexical) (n m : Nat) (creation : Bool) : RuntimeValue :=
  if caller.choice then
    picked saved.choice n (if !creation then argumentValue caller m else saved.kept)
      (if !creation then saved.kept else argumentValue caller m)
  else picked caller.choice n (argumentValue caller m) caller.kept

variable (fNamed : LocalNameTable.Lookup caller.names f.value fId)
  (fFound : Resolved.LocalScope.Lookup caller.captured fId (closure r saved n creation))

include fNamed fFound in
private theorem invocation_original :
    ClosedSourceExpressionEvaluates caller.owner caller.names caller.captured store
      (invocation r caller n m f) (result saved caller n m creation) store := by
  have arg := nest_original r caller.owner caller.names caller.captured store
    caller.gate caller.gateId caller.choice caller.gateNamed caller.gateFound m
    (ref r caller.payload) (unit r) caller.kept .unit
    (.reference caller.payloadNamed caller.payloadFound) .unit
  cases h : caller.choice
  · simp only [result, h, Bool.false_eq_true, ↓reduceIte]
    exact .call (shape r caller n true)
      (.conditionalFalse (.reference caller.gateNamed (h ▸ caller.gateFound))
        (.creation (shape r caller n true))) arg
      (by simpa only [argumentValue, h, ↓reduceIte] using
        saved_body r caller n true (argumentValue caller m) store)
  · simp only [result, h, ↓reduceIte]
    exact .call (shape r saved n (!creation))
      (.conditionalTrue (.reference caller.gateNamed (h ▸ caller.gateFound))
        (.reference fNamed fFound)) arg (saved_body r saved n (!creation) _ store)

include chooseNamed chooseFound different fNamed fFound in
theorem returned_closure_composes_with_different_caller :
    ClosedSourceBodyEvaluates saved.owner saved.names saved.captured store
        (producer r saved n choose f) (closure r saved n creation) store ∧
      ClosedSourceExpressionEvaluates caller.owner caller.names caller.captured store
        (invocation r caller n m f) (result saved caller n m creation) store := by
  exact ⟨original_pre_shadow_closure_is_returned r saved n store creation choose f chooseId
    chooseNamed chooseFound different,
    invocation_original r saved caller n m store creation f fId fNamed fFound⟩

include fNamed fFound in
theorem original_caller_composition_has_open_body_compatibility :
    SourceLambdaEvaluates ClosedSourceExpressionEvaluates
      (SourceComputationBodyEvaluates ClosedSourceExpressionEvaluates)
      caller.owner caller.names caller.captured store
      (invocation r caller n m f) (result saved caller n m creation) store := by
  exact closedSourceExpressionEvaluates_call_iff.mp
    (invocation_original r saved caller n m store creation f fId fNamed fFound)

include chooseNamed chooseFound different fNamed fFound in
theorem independent_derivations_are_found_at_all_larger_budgets :
    ∃ required, ∀ budget, required ≤ budget →
      evaluateClosedSourceBody? budget saved.owner saved.names saved.captured store
          (producer r saved n choose f) = some (closure r saved n creation, store) ∧
        evaluateClosedSourceExpression? budget caller.owner caller.names caller.captured store
          (invocation r caller n m f) = some (result saved caller n m creation, store) := by
  have witnesses := returned_closure_composes_with_different_caller r saved caller n m store
    creation choose f chooseId fId chooseNamed chooseFound different fNamed fFound
  obtain ⟨p, producerFound⟩ := evaluateClosedSourceBody?_eventually_complete witnesses.1
  obtain ⟨c, callFound⟩ := evaluateClosedSourceExpression?_eventually_complete witnesses.2
  exact ⟨max p c, fun budget large =>
    ⟨producerFound budget (by omega), callFound budget (by omega)⟩⟩

end Tests.ClosedSourceConditionalClosure
end

section
-- leanmerge: from Solcore.Test.FrontendClosedSourceConditionalDepthProperties
/- Original conditionals retain independent marker ranges at every depth.
The constructor proof and full runner calculation are independent inductions. -/
set_option autoImplicit false
namespace Tests.ClosedSourceConditionalDepth
open Solcore Solcore.Frontend

private def tower (outer question colon guard : Nat → Syntax.SourceSpan)
    (leaf : Syntax.SourceSpan) (gate : Syntax.Identifier) :
    Nat → Syntax.Identifier → Syntax.Identifier → Syntax.Expr
  | 0, left, _ => ⟨leaf, .identifier left⟩
  | n + 1, left, right =>
      ⟨outer n, .conditional ⟨guard n, .identifier gate⟩ (question n)
        (tower outer question colon guard leaf gate n left right) (colon n)
        (tower outer question colon guard leaf gate n right left)⟩

private def selected (choice : Bool) : Nat → RuntimeValue → RuntimeValue → RuntimeValue
  | 0, left, _ => left
  | n + 1, left, right =>
      if choice then selected choice n left right else selected choice n right left

variable (outer question colon guard : Nat → Syntax.SourceSpan) (leaf : Syntax.SourceSpan)
  (owner : Resolved.DeclarationId) (names : LocalNameTable)
  (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
  (gate left right : Syntax.Identifier) (gateId leftId rightId : Resolved.LocalId)
  (choice : Bool) (leftValue rightValue : RuntimeValue)
  (gateNamed : LocalNameTable.Lookup names gate.value gateId)
  (gateFound : Resolved.LocalScope.Lookup captured gateId (.bool choice))
  (leftNamed : LocalNameTable.Lookup names left.value leftId)
  (leftFound : Resolved.LocalScope.Lookup captured leftId leftValue)
  (rightNamed : LocalNameTable.Lookup names right.value rightId)
  (rightFound : Resolved.LocalScope.Lookup captured rightId rightValue)

include gateNamed gateFound leftNamed leftFound rightNamed rightFound

private theorem original (n : Nat) :
    ClosedSourceExpressionEvaluates owner names captured store
      (tower outer question colon guard leaf gate n left right)
      (selected choice n leftValue rightValue) store := by
  induction n generalizing left right leftId rightId leftValue rightValue with
  | zero => exact .reference leftNamed leftFound
  | succ n ih =>
      cases choice
      · exact .conditionalFalse (.reference gateNamed gateFound)
          (ih right left rightId leftId rightValue leftValue
            rightNamed rightFound leftNamed leftFound)
      · exact .conditionalTrue (.reference gateNamed gateFound)
          (ih left right leftId rightId leftValue rightValue
            leftNamed leftFound rightNamed rightFound)

theorem original_endpoint_and_eventual_discovery (n : Nat) :
    ClosedSourceExpressionEvaluates owner names captured store
        (tower outer question colon guard leaf gate n left right)
        (selected choice n leftValue rightValue) store ∧
      ∃ required, ∀ budget, required ≤ budget →
        evaluateClosedSourceExpression? budget owner names captured store
          (tower outer question colon guard leaf gate n left right) =
          some (selected choice n leftValue rightValue, store) := by
  have evaluated := original outer question colon guard leaf owner names captured store
    gate left right gateId leftId rightId choice leftValue rightValue
    gateNamed gateFound leftNamed leftFound rightNamed rightFound n
  exact ⟨evaluated, evaluateClosedSourceExpression?_eventually_complete evaluated⟩

omit gateNamed gateFound leftNamed leftFound rightNamed rightFound in
private theorem reference_run {name : Syntax.Identifier} {id : Resolved.LocalId}
    {value : RuntimeValue} (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id value) (span : Syntax.SourceSpan)
    (budget : Nat) :
    evaluateClosedSourceExpression? (budget + 1) owner names captured store
      ⟨span, .identifier name⟩ = some (value, store) := by
  simp only [evaluateClosedSourceExpression?, LocalNameTable.lookup?_iff.mpr named,
    Resolved.LocalScope.lookup?_iff.mpr found, bind, Option.bind_some, pure]

theorem exact_outcome_at_every_budget (n budget : Nat) :
    evaluateClosedSourceExpression? budget owner names captured store
      (tower outer question colon guard leaf gate n left right) =
      if n + 1 ≤ budget then some (selected choice n leftValue rightValue, store) else none := by
  induction n generalizing left right leftId rightId leftValue rightValue budget with
  | zero =>
      cases budget with
      | zero => simp [evaluateClosedSourceExpression?]
      | succ budget =>
          simpa only [tower, selected, Nat.succ_eq_add_one, Nat.le_add_left,
            ↓reduceIte] using reference_run owner names captured store leftNamed leftFound leaf budget
  | succ n ih =>
      cases budget with
      | zero => simp [evaluateClosedSourceExpression?]
      | succ budget =>
          cases budget with
          | zero => simp [tower, evaluateClosedSourceExpression?, bind, Option.bind_none]
          | succ budget =>
              simp only [tower, evaluateClosedSourceExpression?_conditional,
                reference_run owner names captured store gateNamed gateFound,
                bind, Option.bind_some]
              cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte, selected]
              · rw [ih right left rightId leftId rightValue leftValue
                  rightNamed rightFound leftNamed leftFound]
                simp only [Nat.succ_le_succ_iff]
              · rw [ih left right leftId rightId leftValue rightValue
                  leftNamed leftFound rightNamed rightFound]
                simp only [Nat.succ_le_succ_iff]

theorem direct_threshold_result_supplies_soundness (n : Nat) :
    evaluateClosedSourceExpression? (n + 1) owner names captured store
        (tower outer question colon guard leaf gate n left right) =
        some (selected choice n leftValue rightValue, store) ∧
      ClosedSourceExpressionEvaluates owner names captured store
        (tower outer question colon guard leaf gate n left right)
        (selected choice n leftValue rightValue) store := by
  have result := exact_outcome_at_every_budget outer question colon guard leaf owner names
    captured store gate left right gateId leftId rightId choice leftValue rightValue
    gateNamed gateFound leftNamed leftFound rightNamed rightFound n (n + 1)
  simp only [Nat.le_refl, ↓reduceIte] at result
  exact ⟨result, evaluateClosedSourceExpression?_sound result⟩

omit gateFound leftFound rightFound in
theorem same_original_source_in_both_boolean_environments
    (environments : Bool → Resolved.LocalScope RuntimeValue)
    (guards : ∀ b, Resolved.LocalScope.Lookup (environments b) gateId (.bool b))
    (lefts : ∀ b, Resolved.LocalScope.Lookup (environments b) leftId leftValue)
    (rights : ∀ b, Resolved.LocalScope.Lookup (environments b) rightId rightValue)
    (n : Nat) :
    ∀ b, ClosedSourceExpressionEvaluates owner names (environments b) store
        (tower outer question colon guard leaf gate n left right)
        (selected b n leftValue rightValue) store ∧
      ∀ budget, evaluateClosedSourceExpression? budget owner names (environments b) store
        (tower outer question colon guard leaf gate n left right) =
        if n + 1 ≤ budget then some (selected b n leftValue rightValue, store) else none := by
  intro b
  exact ⟨original outer question colon guard leaf owner names (environments b) store
    gate left right gateId leftId rightId b leftValue rightValue
    gateNamed (guards b) leftNamed (lefts b) rightNamed (rights b) n,
    exact_outcome_at_every_budget outer question colon guard leaf owner names (environments b)
      store gate left right gateId leftId rightId b leftValue rightValue
      gateNamed (guards b) leftNamed (lefts b) rightNamed (rights b) n⟩

end Tests.ClosedSourceConditionalDepth
end

section
-- leanmerge: from Solcore.Test.FrontendClosedSourceDepthBoundaryProperties
/- Independent original witnesses and separate whole-Option calculations. -/
set_option autoImplicit false
namespace Tests.ClosedSourceDepthBoundaries
open Solcore Solcore.Frontend

private def groups (spans : Nat → Syntax.SourceSpan) (leaf : Syntax.SourceSpan)
    (name : Syntax.Identifier) : Nat → Syntax.Expr
  | 0 => ⟨leaf, .identifier name⟩
  | n + 1 => ⟨spans n, .group (groups spans leaf name n)⟩

private def blocks (spans : Nat → Syntax.SourceSpan) (returned : Syntax.SourceSpan)
    (child : Syntax.Expr) : Nat → Syntax.Block
  | 0 => ⟨spans 0, [⟨returned, .returnStmt (some child)⟩]⟩
  | n + 1 => ⟨spans (n + 1), [⟨spans n, .block (blocks spans returned child n).value⟩]⟩

variable (owner : Resolved.DeclarationId) (names : LocalNameTable)
  (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
  (name : Syntax.Identifier) (id : Resolved.LocalId) (value : RuntimeValue)
  (named : LocalNameTable.Lookup names name.value id)
  (found : Resolved.LocalScope.Lookup captured id value)
  (groupSpans blockSpans : Nat → Syntax.SourceSpan) (leaf returned : Syntax.SourceSpan)

include named found in
private theorem groups_original (n : Nat) :
    ClosedSourceExpressionEvaluates owner names captured store
      (groups groupSpans leaf name n) value store := by
  induction n with
  | zero => exact .reference named found
  | succ n ih => exact .group ih

include named found in
private theorem blocks_original (m n : Nat) :
    ClosedSourceBodyEvaluates owner names captured store
      (blocks blockSpans returned (groups groupSpans leaf name n) m) value store := by
  induction m with
  | zero => exact .expression (groups_original owner names captured store name id value
      named found groupSpans leaf n)
  | succ m ih =>
      apply ClosedSourceBodyEvaluates.block
      cases m <;> exact ih

include named found in
private theorem groups_run (n budget : Nat) :
    evaluateClosedSourceExpression? budget owner names captured store
      (groups groupSpans leaf name n) =
      if n + 1 ≤ budget then some (value, store) else none := by
  induction n generalizing budget with
  | zero =>
      cases budget with
      | zero => simp [evaluateClosedSourceExpression?]
      | succ budget =>
          simp only [groups, evaluateClosedSourceExpression?,
            LocalNameTable.lookup?_iff.mpr named, Resolved.LocalScope.lookup?_iff.mpr found,
            bind, Option.bind_some, pure, Nat.le_add_left, ↓reduceIte]
  | succ n ih =>
      cases budget with
      | zero => simp [evaluateClosedSourceExpression?]
      | succ budget =>
          simpa only [groups, evaluateClosedSourceExpression?, Nat.succ_le_succ_iff] using ih budget

include named found in
private theorem blocks_run (m n budget : Nat) :
    evaluateClosedSourceBody? budget owner names captured store
      (blocks blockSpans returned (groups groupSpans leaf name n) m) =
      if m + n + 2 ≤ budget then some (value, store) else none := by
  induction m generalizing budget with
  | zero =>
      cases budget with
      | zero => simp [evaluateClosedSourceBody?]
      | succ budget =>
          simpa only [blocks, evaluateClosedSourceBody?, Nat.zero_add,
            Nat.succ_le_succ_iff, Nat.add_assoc] using
            groups_run owner names captured store name id value named found groupSpans leaf n budget
  | succ m ih =>
      cases budget with
      | zero => simp [evaluateClosedSourceBody?]
      | succ budget =>
          have same : (m + 1) + n + 2 ≤ budget + 1 ↔ m + n + 2 ≤ budget := by omega
          cases m <;> simpa only [blocks, evaluateClosedSourceBody?, same] using ih budget

private theorem cutoff_unique {α : Type} (f : Nat → Option α) (value : α)
    (required previous : Nat)
    (formula : ∀ n, f n = if required ≤ n then some value else none)
    (below : f previous = none) (atNext : f (previous + 1) = some value) :
    required = previous + 1 := by
  have lower : previous < required := by
    by_cases order : required ≤ previous
    · have impossible := formula previous
      rw [if_pos order, below] at impossible
      cases impossible
    · omega
  have upper : required ≤ previous + 1 := by
    by_cases order : required ≤ previous + 1
    · exact order
    · have impossible := formula (previous + 1)
      rw [if_neg order, atNext] at impossible
      cases impossible
  omega

include named found in
theorem independent_groups_determine_the_general_cutoff (n : Nat) :
    ClosedSourceExpressionEvaluates owner names captured store
        (groups groupSpans leaf name n) value store ∧
      ∃ required : Nat, required = n + 1 ∧ ∀ budget,
        evaluateClosedSourceExpression? budget owner names captured store
          (groups groupSpans leaf name n) =
          if required ≤ budget then some (value, store) else none := by
  have original := groups_original owner names captured store name id value
    named found groupSpans leaf n
  obtain ⟨required, _, formula⟩ :=
    Solcore.Frontend.ClosedSourceExpressionEvaluates.exact_depth_threshold original
  have below := groups_run owner names captured store name id value
    named found groupSpans leaf n n
  have atNext := groups_run owner names captured store name id value
    named found groupSpans leaf n (n + 1)
  simp only [Nat.not_succ_le_self, ↓reduceIte] at below
  simp only [Nat.le_refl, ↓reduceIte] at atNext
  exact ⟨original, required, cutoff_unique _ _ required n formula below atNext, formula⟩

include named found in
theorem independent_blocks_determine_the_general_cutoff (m n : Nat) :
    ClosedSourceBodyEvaluates owner names captured store
        (blocks blockSpans returned (groups groupSpans leaf name n) m) value store ∧
      ∃ required : Nat, required = m + n + 2 ∧ ∀ budget,
        evaluateClosedSourceBody? budget owner names captured store
          (blocks blockSpans returned (groups groupSpans leaf name n) m) =
          if required ≤ budget then some (value, store) else none := by
  have original := blocks_original owner names captured store name id value
    named found groupSpans blockSpans leaf returned m n
  obtain ⟨required, _, formula⟩ :=
    Solcore.Frontend.ClosedSourceBodyEvaluates.exact_depth_threshold original
  have below := blocks_run owner names captured store name id value
    named found groupSpans blockSpans leaf returned m n (m + n + 1)
  have atNext := blocks_run owner names captured store name id value
    named found groupSpans blockSpans leaf returned m n (m + n + 2)
  simp only [show ¬ m + n + 2 ≤ m + n + 1 by omega, ↓reduceIte] at below
  simp only [Nat.le_refl, ↓reduceIte] at atNext
  exact ⟨original, required, cutoff_unique _ _ required (m + n + 1)
    formula below atNext, formula⟩

include named found in
theorem actual_group_boundaries_lift_and_restrict
    (n small large : Nat) (early : small ≤ n) (late : n + 1 ≤ large) :
    evaluateClosedSourceExpression? n owner names captured store
        (groups groupSpans leaf name n) = none ∧
      evaluateClosedSourceExpression? (n + 1) owner names captured store
        (groups groupSpans leaf name n) = some (value, store) ∧
      evaluateClosedSourceExpression? small owner names captured store
        (groups groupSpans leaf name n) = none ∧
      evaluateClosedSourceExpression? large owner names captured store
        (groups groupSpans leaf name n) = some (value, store) := by
  have below := groups_run owner names captured store name id value
    named found groupSpans leaf n n
  have atNext := groups_run owner names captured store name id value
    named found groupSpans leaf n (n + 1)
  simp only [Nat.not_succ_le_self, ↓reduceIte] at below
  simp only [Nat.le_refl, ↓reduceIte] at atNext
  exact ⟨below, atNext,
    Solcore.Frontend.evaluateClosedSourceExpression?_none_of_le early below,
    Solcore.Frontend.evaluateClosedSourceExpression?_monotone late atNext⟩

include named found in
theorem actual_block_boundaries_lift_and_restrict
    (m n small large : Nat) (early : small ≤ m + n + 1) (late : m + n + 2 ≤ large) :
    evaluateClosedSourceBody? (m + n + 1) owner names captured store
        (blocks blockSpans returned (groups groupSpans leaf name n) m) = none ∧
      evaluateClosedSourceBody? (m + n + 2) owner names captured store
        (blocks blockSpans returned (groups groupSpans leaf name n) m) = some (value, store) ∧
      evaluateClosedSourceBody? small owner names captured store
        (blocks blockSpans returned (groups groupSpans leaf name n) m) = none ∧
      evaluateClosedSourceBody? large owner names captured store
        (blocks blockSpans returned (groups groupSpans leaf name n) m) = some (value, store) := by
  have below := blocks_run owner names captured store name id value
    named found groupSpans blockSpans leaf returned m n (m + n + 1)
  have atNext := blocks_run owner names captured store name id value
    named found groupSpans blockSpans leaf returned m n (m + n + 2)
  simp only [show ¬ m + n + 2 ≤ m + n + 1 by omega, ↓reduceIte] at below
  simp only [Nat.le_refl, ↓reduceIte] at atNext
  exact ⟨below, atNext,
    Solcore.Frontend.evaluateClosedSourceBody?_none_of_le early below,
    Solcore.Frontend.evaluateClosedSourceBody?_monotone late atNext⟩

end Tests.ClosedSourceDepthBoundaries
end

section
-- leanmerge: from Solcore.Test.FrontendClosedSourceRunnerBoundaryProperties
set_option autoImplicit false
namespace Tests.ClosedSourceRunnerBoundaries
open Solcore Solcore.Frontend

theorem an_expression_witness_exists_exactly_for_a_finite_derivation
    {owner names captured store source value finalStore} :
    (∃ budget, evaluateClosedSourceExpression? budget owner names captured store source =
      some (value, finalStore)) ↔
    ClosedSourceExpressionEvaluates owner names captured store source value finalStore := by
  constructor
  · rintro ⟨budget, accepted⟩
    exact evaluateClosedSourceExpression?_sound accepted
  · intro evaluated
    obtain ⟨required, found⟩ := evaluateClosedSourceExpression?_eventually_complete evaluated
    exact ⟨required, found required (Nat.le_refl _)⟩

theorem a_body_witness_exists_exactly_for_a_finite_derivation
    {owner names captured store source value finalStore} :
    (∃ budget, evaluateClosedSourceBody? budget owner names captured store source =
      some (value, finalStore)) ↔
    ClosedSourceBodyEvaluates owner names captured store source value finalStore := by
  constructor
  · rintro ⟨budget, accepted⟩
    exact evaluateClosedSourceBody?_sound accepted
  · intro evaluated
    obtain ⟨required, found⟩ := evaluateClosedSourceBody?_eventually_complete evaluated
    exact ⟨required, found required (Nat.le_refl _)⟩

theorem successful_expression_budgets_cannot_change_actual_endpoints
    {firstBudget secondBudget owner names captured store source first firstStore second secondStore}
    (left : evaluateClosedSourceExpression? firstBudget owner names captured store source =
      some (first, firstStore))
    (right : evaluateClosedSourceExpression? secondBudget owner names captured store source =
      some (second, secondStore)) : first = second ∧ firstStore = secondStore :=
  (evaluateClosedSourceExpression?_sound left).deterministic
    (evaluateClosedSourceExpression?_sound right)

theorem successful_body_budgets_cannot_change_actual_endpoints
    {firstBudget secondBudget owner names captured store source first firstStore second secondStore}
    (left : evaluateClosedSourceBody? firstBudget owner names captured store source =
      some (first, firstStore))
    (right : evaluateClosedSourceBody? secondBudget owner names captured store source =
      some (second, secondStore)) : first = second ∧ firstStore = secondStore :=
  (evaluateClosedSourceBody?_sound left).deterministic
    (evaluateClosedSourceBody?_sound right)

theorem zero_depth_none_does_not_rule_out_an_independent_success
    {owner names captured store span tupleSpan} :
    evaluateClosedSourceExpression? 0 owner names captured store
      ⟨span, .tuple ⟨tupleSpan, []⟩⟩ = none ∧
    ClosedSourceExpressionEvaluates owner names captured store
      ⟨span, .tuple ⟨tupleSpan, []⟩⟩ .unit store ∧
    evaluateClosedSourceExpression? 1 owner names captured store
      ⟨span, .tuple ⟨tupleSpan, []⟩⟩ = some (.unit, store) := by
  exact ⟨by simp only [evaluateClosedSourceExpression?], .unit,
    by simp only [evaluateClosedSourceExpression?]⟩

private def selfCall (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span, .call ⟨span, .identifier name⟩ ⟨span, [⟨span, .identifier name⟩]⟩⟩
private def loopBody (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Block :=
  ⟨span, [⟨span, .returnStmt (some (selfCall span name))⟩]⟩
private def loopLambda (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span, .lambda span ⟨span, [⟨span, .inferred name⟩]⟩ none (loopBody span name)⟩
private def omegaSource (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span, .call (loopLambda span name) ⟨span, [loopLambda span name]⟩⟩

private theorem loopBody_none (budget : Nat) {owner names captured store span name} :
    evaluateClosedSourceBody? budget owner
      ((name.value, Resolved.freshLocalId owner (names.map Prod.snd)) :: names)
      ((Resolved.freshLocalId owner (names.map Prod.snd),
        .sourceClosure (loopLambda span name) owner names captured) :: captured)
      store (loopBody span name) = none := by
  induction budget using Nat.strongRecOn with
  | ind budget ih =>
      cases budget with
      | zero => simp only [evaluateClosedSourceBody?]
      | succ n =>
          cases n with
          | zero => simp only [loopBody, evaluateClosedSourceBody?, evaluateClosedSourceExpression?]
          | succ k =>
              cases k with
              | zero => simp only [loopBody, evaluateClosedSourceBody?, selfCall,
                  evaluateClosedSourceExpression?, bind, Option.bind_none]
              | succ l =>
                  have smaller := ih (l + 1) (by omega)
                  simpa only [loopBody, evaluateClosedSourceBody?, selfCall,
                    evaluateClosedSourceExpression?, loopLambda, sourceUnaryLambdaShape?,
                    LocalNameTable.lookup?, Resolved.LocalScope.lookup?, ↓reduceIte,
                    bind, Option.bind_some, pure] using smaller

theorem original_self_application_has_no_success_at_any_depth
    (budget : Nat) {owner names captured store span name} :
    evaluateClosedSourceExpression? budget owner names captured store
      (omegaSource span name) = none := by
  cases budget with
  | zero => simp only [evaluateClosedSourceExpression?]
  | succ n =>
      cases n with
      | zero => simp only [omegaSource, evaluateClosedSourceExpression?, bind, Option.bind_none]
      | succ k =>
          have body := loopBody_none (k + 1) (owner := owner) (names := names)
            (captured := captured) (store := store) (span := span) (name := name)
          simpa only [omegaSource, loopLambda, evaluateClosedSourceExpression?,
            sourceUnaryLambdaShape?, bind, Option.bind_some, pure] using body

theorem original_self_application_has_no_finite_successful_derivation
    {owner names captured store span name value finalStore} :
    ¬ ClosedSourceExpressionEvaluates owner names captured store
      (omegaSource span name) value finalStore := by
  intro evaluated
  obtain ⟨budget, found⟩ :=
    an_expression_witness_exists_exactly_for_a_finite_derivation.mpr evaluated
  rw [original_self_application_has_no_success_at_any_depth budget] at found
  cases found

end Tests.ClosedSourceRunnerBoundaries
end

section
-- leanmerge: from Solcore.Test.FrontendClosedSourceStoreBoundaryProperties
/- Store contents cannot supply lexical captures or execute an opaque host value.
Independent original exclusions and direct finite runs precede replay consumers. -/
set_option autoImplicit false
namespace Tests.ClosedSourceStoreBoundaries
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates
private def ref (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr := ⟨s,.identifier name⟩
private def call (s : Syntax.SourceSpan) (f x : Syntax.Identifier) : Syntax.Expr :=
  ⟨s,.call (ref s f) ⟨s,[ref s x]⟩⟩
private theorem exclude_replay {owner names captured initialStore source}
    (original : ∀ value final, ¬ E owner names captured initialStore source value final) :
    ∀ replacement value final, ¬ E owner names captured replacement source value final := by
  intro replacement value final other
  exact original value initialStore (other.replay_store initialStore)

/-- A missing lexical capture stays missing even when the replacement store contains data. -/
theorem replacing_store_does_not_fill_missing_capture
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (initialStore : List RuntimeValue) (s : Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (named : LocalNameTable.Lookup names name.value id) (missing : Resolved.LocalScope.lookup? captured id = none) :
    (∀ value final, ¬ E owner names captured initialStore (ref s name) value final) ∧
    (∀ budget, evaluateClosedSourceExpression? budget owner names captured initialStore (ref s name) = none) ∧
    (∀ replacement value final, ¬ E owner names captured replacement (ref s name) value final) ∧
    (∀ replacement budget, evaluateClosedSourceExpression? budget owner names captured replacement (ref s name) = none) := by
  have absent : ∀ value final, ¬ E owner names captured initialStore (ref s name) value final := by
    intro value final original
    cases original with
    | creation impossible => cases impossible
    | reference actualName actualValue =>
      cases actualName.id_unique named
      have accepted := Resolved.LocalScope.lookup?_iff.mpr actualValue
      rw [missing] at accepted
      cases accepted
  have direct : ∀ store budget, evaluateClosedSourceExpression? budget owner names captured store (ref s name) = none := by
    intro store budget
    cases budget <;> simp [ref,evaluateClosedSourceExpression?,LocalNameTable.lookup?_iff.mpr named,missing]
  have replayed : ∀ replacement budget, evaluateClosedSourceExpression? budget owner names captured replacement (ref s name) = none := by
    intro replacement budget
    rw [evaluateClosedSourceExpression?_replay_store budget owner names captured initialStore replacement,
      direct initialStore budget]
    rfl
  exact ⟨absent,direct initialStore,exclude_replay absent,replayed⟩

/-- Successful lexical input lookup does not make a host-function value a source closure. -/
theorem replacing_store_does_not_execute_host_callee
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (initialStore : List RuntimeValue) (s : Syntax.SourceSpan) (f x : Syntax.Identifier)
    (fid xid : Resolved.LocalId) (argument : RuntimeValue)
    (fn : LocalNameTable.Lookup names f.value fid)
    (fv : Resolved.LocalScope.Lookup captured fid (.hostFunction .storageWrite))
    (xn : LocalNameTable.Lookup names x.value xid) (xv : Resolved.LocalScope.Lookup captured xid argument) :
    E owner names captured initialStore (ref s f) (.hostFunction .storageWrite) initialStore ∧
    E owner names captured initialStore (ref s x) argument initialStore ∧
    (∀ value final, ¬ E owner names captured initialStore (call s f x) value final) ∧
    (∀ budget, evaluateClosedSourceExpression? budget owner names captured initialStore (call s f x) = none) ∧
    (∀ replacement value final, ¬ E owner names captured replacement (call s f x) value final) ∧
    (∀ replacement budget, evaluateClosedSourceExpression? budget owner names captured replacement (call s f x) = none) := by
  have picked : E owner names captured initialStore (ref s f) (.hostFunction .storageWrite) initialStore := .reference fn fv
  have supplied : E owner names captured initialStore (ref s x) argument initialStore := .reference xn xv
  have absent : ∀ value final, ¬ E owner names captured initialStore (call s f x) value final := by
    intro value final original
    cases original with
    | creation impossible => cases impossible
    | call _ callee _ _ => cases (callee.deterministic picked).1
  have direct : ∀ store budget, evaluateClosedSourceExpression? budget owner names captured store (call s f x) = none := by
    intro store budget
    cases budget with
    | zero => simp [evaluateClosedSourceExpression?]
    | succ budget =>
      cases budget <;> simp [call,ref,evaluateClosedSourceExpression?,LocalNameTable.lookup?_iff.mpr fn,
        Resolved.LocalScope.lookup?_iff.mpr fv,LocalNameTable.lookup?_iff.mpr xn,Resolved.LocalScope.lookup?_iff.mpr xv]
  have replayed : ∀ replacement budget, evaluateClosedSourceExpression? budget owner names captured replacement (call s f x) = none := by
    intro replacement budget
    rw [evaluateClosedSourceExpression?_replay_store budget owner names captured initialStore replacement,
      direct initialStore budget]
    rfl
  exact ⟨picked,supplied,absent,direct initialStore,exclude_replay absent,replayed⟩

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"StoreBoundary",by decide⟩],by decide⟩⟩,309⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def s : Syntax.SourceSpan := ⟨⟨.main,"store-boundary.sol"⟩,0,1⟩
private def name (n : String) : Syntax.Identifier := ⟨s,n⟩
private def coreValue : RuntimeValue := .ofCore
  (.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700])
private def saved : RuntimeValue := .sourceClosure ⟨s,.tuple ⟨s,[]⟩⟩ owner
  [("x",id 77),("x",id 88)] [(id 77,coreValue),(id 77,.unit)]
private def payload : RuntimeValue := .pair coreValue (.cellRef .word 900)
private def names : LocalNameTable := [("h",id 0),("x",id 1),("missing",id 2),("h",id 1),("x",id 0)]
private def captured : Resolved.LocalScope RuntimeValue :=
  [(id 0,.hostFunction .storageWrite),(id 0,saved),(id 1,payload),(id 1,.unit)]
private def initial : List RuntimeValue := [saved,payload]
private def replacement : List RuntimeValue := [.cellRef .word 900,.hostFunction .storageWrite,coreValue]

example : initial ≠ replacement ∧ replacement ≠ [] := by
  constructor
  · intro equal; cases equal
  · intro equal; cases equal

example : ∀ budget, evaluateClosedSourceExpression? budget owner names captured replacement (ref s (name "missing")) = none := by
  have absent := replacing_store_does_not_fill_missing_capture owner names captured initial s (name "missing") (id 2)
    (.tail (by decide) (.tail (by decide) .head)) (by rfl)
  exact absent.2.2.2 replacement

example : E owner names captured initial (ref s (name "x")) payload initial ∧
    (∀ store budget, evaluateClosedSourceExpression? budget owner names captured store (call s (name "h") (name "x")) = none) := by
  have absent := replacing_store_does_not_execute_host_callee owner names captured initial s (name "h") (name "x")
    (id 0) (id 1) payload .head .head (.tail (by decide) .head)
    (.tail (by decide) (.tail (by decide) .head))
  exact ⟨absent.2.1,absent.2.2.2.2.2⟩

end Tests.ClosedSourceStoreBoundaries
end

section
-- leanmerge: from Solcore.Test.FrontendClosedSourceStoreSymbolicProperties
/- Independent original constructors and direct finite runners precede replay.
Stores are replaced only at endpoints, never inside captured values. Arbitrary
mixed payloads, duplicate lexical rows and opaque cell references are retained. -/
set_option autoImplicit false
namespace Tests.ClosedSourceStoreSymbolic
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def ref (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr := ⟨s,.identifier name⟩
private def returning (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Block :=
  ⟨s,[⟨s,.returnStmt (some (ref s name))⟩]⟩
private def lambda (s : Syntax.SourceSpan) (name : Syntax.Identifier) (annotation : Option Syntax.TypeExpr) : Syntax.Expr :=
  ⟨s,.lambda s ⟨s,[⟨s,.inferred name⟩]⟩ annotation (returning s name)⟩
private def call (s : Syntax.SourceSpan) (f x : Syntax.Expr) : Syntax.Expr := ⟨s,.call f ⟨s,[x]⟩⟩
private def nested (s : Syntax.SourceSpan) (f x : Syntax.Identifier) : Syntax.Expr :=
  call s (ref s f) (call s (ref s f) (ref s x))
private theorem shape (s : Syntax.SourceSpan) (name : Syntax.Identifier) (annotation : Option Syntax.TypeExpr) :
    SourceUnaryLambdaShape (lambda s name annotation) name (returning s name) := .inferred
private theorem reference_run {s name owner names captured store id value}
    (n : Nat) (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id value) :
    evaluateClosedSourceExpression? (n+1) owner names captured store (ref s name) = some (value,store) := by
  simp only [ref,evaluateClosedSourceExpression?,LocalNameTable.lookup?_iff.mpr named,
    Resolved.LocalScope.lookup?_iff.mpr found,bind,Option.bind_some,pure]
private theorem fresh_body_run (s : Syntax.SourceSpan) (name : Syntax.Identifier) (n : Nat)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (value : RuntimeValue) :
    evaluateClosedSourceBody? (n+2) owner ((name.value,Resolved.freshLocalId owner (names.map Prod.snd))::names)
      ((Resolved.freshLocalId owner (names.map Prod.snd),value)::captured) store (returning s name) = some (value,store) := by
  simp only [returning,evaluateClosedSourceBody?]
  exact reference_run (n:=n) .head .head
private theorem nested_original {s name f x annotation co so cn sn cc sc store fid aid value}
    (fn : LocalNameTable.Lookup cn f.value fid)
    (ff : Resolved.LocalScope.Lookup cc fid (.sourceClosure (lambda s name annotation) so sn sc))
    (an : LocalNameTable.Lookup cn x.value aid) (af : Resolved.LocalScope.Lookup cc aid value) :
    E co cn cc store (nested s f x) value store :=
  .call (shape s name annotation) (.reference fn ff)
    (.call (shape s name annotation) (.reference fn ff) (.reference an af) (.expression (.reference .head .head)))
    (.expression (.reference .head .head))
private theorem nested_run {s name f x annotation co so cn sn cc sc store fid aid value}
    (fn : LocalNameTable.Lookup cn f.value fid)
    (ff : Resolved.LocalScope.Lookup cc fid (.sourceClosure (lambda s name annotation) so sn sc))
    (an : LocalNameTable.Lookup cn x.value aid) (af : Resolved.LocalScope.Lookup cc aid value) :
    evaluateClosedSourceExpression? 4 co cn cc store (nested s f x) = some (value,store) := by
  have f3 := reference_run (s:=s) (owner:=co) (store:=store) 2 fn ff
  have f2 := reference_run (s:=s) (owner:=co) (store:=store) 1 fn ff
  have x2 := reference_run (s:=s) (owner:=co) (store:=store) 1 an af
  have b2 := fresh_body_run s name 0 so sn sc store value
  have b3 := fresh_body_run s name 1 so sn sc store value
  simp only [nested,call,evaluateClosedSourceExpression?,f3,f2,x2,
    sourceUnaryLambdaShape?_iff.mpr (shape s name annotation),b2,b3,bind,Option.bind_some]

/-- Creation and two nested saved identity calls retain every captured field and
arbitrary mixed result when only the external store is replaced. -/
theorem saved_creation_and_nested_calls_replay
    (s : Syntax.SourceSpan) (name f x : Syntax.Identifier) (annotation : Option Syntax.TypeExpr)
    (co so : Resolved.DeclarationId) (cn sn : LocalNameTable) (cc sc : Resolved.LocalScope RuntimeValue)
    (creationStore invocationStore replacement : List RuntimeValue) (fid aid : Resolved.LocalId) (value : RuntimeValue)
    (fn : LocalNameTable.Lookup cn f.value fid)
    (ff : Resolved.LocalScope.Lookup cc fid (.sourceClosure (lambda s name annotation) so sn sc))
    (an : LocalNameTable.Lookup cn x.value aid) (af : Resolved.LocalScope.Lookup cc aid value) :
    E so sn sc creationStore (lambda s name annotation) (.sourceClosure (lambda s name annotation) so sn sc) creationStore ∧
    E co cn cc invocationStore (nested s f x) value invocationStore ∧
    evaluateClosedSourceExpression? 4 co cn cc invocationStore (nested s f x) = some (value,invocationStore) ∧
    E so sn sc replacement (lambda s name annotation) (.sourceClosure (lambda s name annotation) so sn sc) replacement ∧
    E co cn cc replacement (nested s f x) value replacement ∧
    (∀ actual final, E co cn cc invocationStore (nested s f x) actual final → final = invocationStore) ∧
    evaluateClosedSourceExpression? 4 co cn cc replacement (nested s f x) = some (value,replacement) ∧
    (∀ budget, evaluateClosedSourceExpression? budget co cn cc replacement (nested s f x) =
      (evaluateClosedSourceExpression? budget co cn cc invocationStore (nested s f x)).map (fun ep => (ep.1,replacement))) ∧
    evaluateClosedSourceExpression? 1 so sn sc replacement (lambda s name annotation) =
      some (.sourceClosure (lambda s name annotation) so sn sc,replacement) := by
  have created : E so sn sc creationStore (lambda s name annotation)
      (.sourceClosure (lambda s name annotation) so sn sc) creationStore := .creation (shape s name annotation)
  have original : E co cn cc invocationStore (nested s f x) value invocationStore := nested_original fn ff an af
  have direct := nested_run (co:=co) (store:=invocationStore) fn ff an af
  have creationRun : evaluateClosedSourceExpression? 1 so sn sc creationStore (lambda s name annotation) =
      some (.sourceClosure (lambda s name annotation) so sn sc,creationStore) := by
    simp only [lambda,evaluateClosedSourceExpression?,sourceUnaryLambdaShape?,bind,Option.bind_some,pure]
  have replay := fun budget => evaluateClosedSourceExpression?_replay_store budget co cn cc invocationStore replacement (nested s f x)
  exact ⟨created,original,direct,created.replay_store replacement,original.replay_store replacement,
    fun _ _ evaluated => evaluated.store_eq,by simpa only [direct,Option.map_some] using replay 4,replay,
    by simpa only [creationRun,Option.map_some] using
      evaluateClosedSourceExpression?_replay_store 1 so sn sc creationStore replacement (lambda s name annotation)⟩

private def skipped (s : Syntax.SourceSpan) (guard : Syntax.Identifier) (bad : Syntax.Expr) : Syntax.Expr :=
  ⟨s,.binary (ref s guard) ⟨s,.logicalAnd⟩ bad⟩
/-- No assumption about the skipped child is needed, even when it cannot run. -/
theorem skipped_child_keeps_full_store
    (s : Syntax.SourceSpan) (guard : Syntax.Identifier) (bad : Syntax.Expr)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (initial replacement : List RuntimeValue) (id : Resolved.LocalId)
    (named : LocalNameTable.Lookup names guard.value id) (found : Resolved.LocalScope.Lookup captured id (.bool false)) :
    E owner names captured initial (skipped s guard bad) (.bool false) initial ∧
    evaluateClosedSourceExpression? 1 owner names captured initial (skipped s guard bad) = none ∧
    evaluateClosedSourceExpression? 2 owner names captured initial (skipped s guard bad) = some (.bool false,initial) ∧
    E owner names captured replacement (skipped s guard bad) (.bool false) replacement ∧
    evaluateClosedSourceExpression? 1 owner names captured replacement (skipped s guard bad) = none ∧
    evaluateClosedSourceExpression? 2 owner names captured replacement (skipped s guard bad) = some (.bool false,replacement) ∧
    (∀ budget, evaluateClosedSourceExpression? budget owner names captured replacement (skipped s guard bad) =
      (evaluateClosedSourceExpression? budget owner names captured initial (skipped s guard bad)).map (fun ep => (ep.1,replacement))) := by
  have original : E owner names captured initial (skipped s guard bad) (.bool false) initial :=
    .andFalse (.reference named found)
  have low : evaluateClosedSourceExpression? 1 owner names captured initial (skipped s guard bad) = none := by
    simp [skipped,evaluateClosedSourceExpression?]
  have direct : evaluateClosedSourceExpression? 2 owner names captured initial (skipped s guard bad) = some (.bool false,initial) := by
    simp only [skipped,evaluateClosedSourceExpression?,reference_run 0 named found,bind,Option.bind_some,Bool.false_eq_true,↓reduceIte,pure]
  have replay := fun budget => evaluateClosedSourceExpression?_replay_store budget owner names captured initial replacement (skipped s guard bad)
  exact ⟨original,low,direct,original.replay_store replacement,
    by simpa only [low,Option.map_none] using replay 1,
    by simpa only [direct,Option.map_some] using replay 2,replay⟩

private def one : Core.Word := ⟨1,by decide⟩
private def literal (s : Syntax.SourceSpan) (text : String) : Syntax.CoreLiteral := ⟨s,.decimal text⟩
private def badBody (s : Syntax.SourceSpan) : Syntax.Block :=
  ⟨s,[⟨s,.returnStmt (some ⟨s,.literal ⟨s,.string "unselected"⟩⟩)⟩]⟩
private def arm (s : Syntax.SourceSpan) (text : String) (body : Syntax.Block) : Syntax.MatchCase :=
  ⟨s,⟨⟨s,.literal (literal s text)⟩,body⟩⟩
private def arms (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Nat → List Syntax.MatchCase
  | 0 => [arm s "1" (returning s name),arm s "1" (badBody s)]
  | n+1 => arm s "0" (badBody s) :: arms s name n
private def matching (s : Syntax.SourceSpan) (name : Syntax.Identifier) (n : Nat) : Syntax.Statement :=
  ⟨s,.matchWith ⟨s,⟨⟨s,.literal (literal s "1")⟩,[]⟩⟩ ⟨s,⟨arms s name n,some (badBody s)⟩⟩⟩
private def binding (s : Syntax.SourceSpan) (name payload : Syntax.Identifier) (annotation : Option Syntax.TypeExpr) (n : Nat) : Syntax.Block :=
  ⟨s,[⟨s,.letDecl name annotation (some (ref s payload))⟩,matching s name n]⟩
private theorem one_meaning (s : Syntax.SourceSpan) : WordLiteralDenotes (literal s "1") one :=
  .decimal (by decide) (.cons (.decimal (digit:=1) (by decide) rfl) .nil)
private theorem zero_meaning (s : Syntax.SourceSpan) : WordLiteralDenotes (literal s "0") Core.Word.zero :=
  .decimal (by decide) (.cons (.decimal (digit:=0) (by decide) rfl) .nil)
private theorem original_choice (s : Syntax.SourceSpan) (name : Syntax.Identifier) (n : Nat) :
    RuntimeWordMatchChooses (.word one) (arms s name n) (some (badBody s)) (returning s name) (n+1) := by
  induction n with
  | zero => exact .hit (.literal ⟨literal s "1",rfl,one_meaning s⟩)
  | succ n ih => exact .miss (.literal ⟨literal s "0",rfl,zero_meaning s⟩) (by decide) ih
private theorem binding_original {s name payload annotation n owner names captured store id value}
    (named : LocalNameTable.Lookup names payload.value id) (found : Resolved.LocalScope.Lookup captured id value) :
    B owner names captured store (binding s name payload annotation n) value store := by
  have tail : B owner ((name.value,Resolved.freshLocalId owner (names.map Prod.snd))::names)
      ((Resolved.freshLocalId owner (names.map Prod.snd),value)::captured) store ⟨s,[matching s name n]⟩ value store :=
    .wordMatch (.wordLiteral (one_meaning s)) (original_choice s name n) (.expression (.reference .head .head))
  cases annotation with
  | none => exact .inferred (.reference named found) tail
  | some t => exact .binding (.reference named found) tail
private theorem binding_run {s name payload annotation n owner names captured store id value}
    (named : LocalNameTable.Lookup names payload.value id) (found : Resolved.LocalScope.Lookup captured id value) :
    evaluateClosedSourceBody? 4 owner names captured store (binding s name payload annotation n) = some (value,store) := by
  have supplied := reference_run (s:=s) (owner:=owner) (store:=store) 2 named found
  have choice := chooseRuntimeWordMatch?_iff.mpr (original_choice s name n)
  have returned := fresh_body_run s name 0 owner names captured store value
  simp only [binding,matching,evaluateClosedSourceBody?,evaluateClosedSourceExpression?,supplied,
    interpretWordLiteral?_iff.mpr (one_meaning s),choice,returned,bind,Option.bind_some,pure]

/-- Typed or inferred fresh binding shadows duplicate rows. Ordered misses and
the first hit return the same opaque payload, not any unselected bad body. -/
theorem fresh_binding_and_ordered_match_replay
    (s : Syntax.SourceSpan) (name payload : Syntax.Identifier) (annotation : Option Syntax.TypeExpr) (n : Nat)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (initial replacement : List RuntimeValue) (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup names payload.value id) (found : Resolved.LocalScope.Lookup captured id value) :
    RuntimeWordMatchChooses (.word one) (arms s name n) (some (badBody s)) (returning s name) (n+1) ∧
    B owner names captured initial (binding s name payload annotation n) value initial ∧
    evaluateClosedSourceBody? 4 owner names captured initial (binding s name payload annotation n) = some (value,initial) ∧
    B owner names captured replacement (binding s name payload annotation n) value replacement ∧
    (∀ actual final, B owner names captured initial (binding s name payload annotation n) actual final → final = initial) ∧
    evaluateClosedSourceBody? 3 owner names captured initial (binding s name payload annotation n) = none ∧
    evaluateClosedSourceBody? 3 owner names captured replacement (binding s name payload annotation n) = none ∧
    evaluateClosedSourceBody? 4 owner names captured replacement (binding s name payload annotation n) = some (value,replacement) ∧
    (∀ budget, evaluateClosedSourceBody? budget owner names captured replacement (binding s name payload annotation n) =
      (evaluateClosedSourceBody? budget owner names captured initial (binding s name payload annotation n)).map (fun ep => (ep.1,replacement))) := by
  have choice := original_choice s name n
  have original : B owner names captured initial (binding s name payload annotation n) value initial := binding_original named found
  have direct := binding_run (s:=s) (name:=name) (annotation:=annotation) (n:=n) (owner:=owner) (store:=initial) named found
  have low : evaluateClosedSourceBody? 3 owner names captured initial (binding s name payload annotation n) = none := by
    have supplied := reference_run (s:=s) (owner:=owner) (store:=initial) 1 named found
    simp only [binding,matching,evaluateClosedSourceBody?,evaluateClosedSourceExpression?,supplied,
      interpretWordLiteral?_iff.mpr (one_meaning s),chooseRuntimeWordMatch?_iff.mpr choice,returning,
      evaluateClosedSourceBody?,evaluateClosedSourceExpression?,bind,Option.bind_some,pure]
  have replay := fun budget => evaluateClosedSourceBody?_replay_store budget owner names captured initial replacement (binding s name payload annotation n)
  exact ⟨choice,original,direct,original.replay_store replacement,fun _ _ evaluated => evaluated.store_eq,low,
    by simpa only [low,Option.map_none] using replay 3,
    by simpa only [direct,Option.map_some] using replay 4,replay⟩

private def owner (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"StoreReplay",by decide⟩],by decide⟩⟩,n⟩
private def co := owner 909
private def so := owner 309
private def cid (n : Nat) : Resolved.LocalId := ⟨co,n⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨so,n⟩
private def cs : Syntax.SourceSpan := ⟨⟨.main,"store-replay.sol"⟩,0,1⟩
private def idn (text : String) : Syntax.Identifier := ⟨cs,text⟩
private def opaqueValue : RuntimeValue := .pair (.cellRef .word 700)
  (.coreClosure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 900])
private def sn : LocalNameTable := [("p",sid 4),("p",sid 8)]
private def sc : Resolved.LocalScope RuntimeValue := [(sid 4,opaqueValue),(sid 4,.unit),(sid 8,.bool true)]
private def saved : RuntimeValue := .sourceClosure (lambda cs (idn "p") none) so sn sc
private def payload : RuntimeValue := .pair saved opaqueValue
private def cn : LocalNameTable := [("f",cid 0),("x",cid 1),("f",cid 9),("x",cid 99)]
private def cc : Resolved.LocalScope RuntimeValue := [(cid 0,saved),(cid 0,.unit),(cid 1,payload),(cid 1,.bool false)]
private def initial : List RuntimeValue := [opaqueValue,.hostFunction .storageWrite,saved,.cellRef .word 900]

example : co ≠ so ∧ initial ≠ [] := by decide

example (replacement : List RuntimeValue) : E co cn cc replacement (nested cs (idn "f") (idn "x")) payload replacement ∧
    evaluateClosedSourceExpression? 4 co cn cc replacement (nested cs (idn "f") (idn "x")) = some (payload,replacement) := by
  have original : E co cn cc initial (nested cs (idn "f") (idn "x")) payload initial :=
    nested_original (so:=so) (sn:=sn) (sc:=sc) (name:=idn "p") (annotation:=none) .head .head
      (.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head))
  have result := saved_creation_and_nested_calls_replay cs (idn "p") (idn "f") (idn "x") none
    co so cn sn cc sc [payload] initial replacement (cid 0) (cid 1) payload .head .head
      (.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head))
  exact ⟨result.2.2.2.2.1,result.2.2.2.2.2.2.1⟩

example (replacement : List RuntimeValue) (n : Nat) :
    B co cn cc replacement (binding cs (idn "x") (idn "x") none n) payload replacement ∧
    evaluateClosedSourceBody? 4 co cn cc replacement (binding cs (idn "x") (idn "x") none n) = some (payload,replacement) := by
  have original : B co cn cc initial (binding cs (idn "x") (idn "x") none n) payload initial :=
    binding_original (.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head))
  have result := fresh_binding_and_ordered_match_replay cs (idn "x") (idn "x") none n
    co cn cc initial replacement (cid 1) payload
      (.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head))
  exact ⟨result.2.2.2.1,result.2.2.2.2.2.2.2.1⟩

example (replacement : List RuntimeValue) :
    evaluateClosedSourceExpression? 1 co [("b",cid 2)] [(cid 2,.bool false)] initial (ref cs (idn "missing")) = none ∧
    E co [("b",cid 2)] [(cid 2,.bool false)] replacement
      (skipped cs (idn "b") (ref cs (idn "missing"))) (.bool false) replacement := by
  have original : E co [("b",cid 2)] [(cid 2,.bool false)] initial
      (skipped cs (idn "b") (ref cs (idn "missing"))) (.bool false) initial := .andFalse (.reference .head .head)
  have result := skipped_child_keeps_full_store cs (idn "b") (ref cs (idn "missing")) co
    [("b",cid 2)] [(cid 2,.bool false)] initial replacement (cid 2) .head .head
  exact ⟨by simp [evaluateClosedSourceExpression?,ref,idn,LocalNameTable.lookup?],result.2.2.2.1⟩
end Tests.ClosedSourceStoreSymbolic
end

section
-- leanmerge: from Solcore.Test.FrontendClosedSourceUnaryBoundaryProperties
/- Original saved-scope calls and actual-shape boundaries for unary primitives. -/
set_option autoImplicit false
namespace Tests.ClosedSourceUnaryBoundary
open Solcore Solcore.Frontend

private def one (op : Syntax.UnaryOp) (spans : Nat → Syntax.SourceSpan)
    (term : Syntax.Expr) : Syntax.Expr := ⟨spans 0, .unary ⟨spans 1, op⟩ term⟩
private def ref (spans : Nat → Syntax.SourceSpan) (name : String) : Syntax.Expr :=
  ⟨spans 2, .identifier ⟨spans 3, name⟩⟩
private def savedOriginal (spans : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨spans 4, .lambda (spans 5)
    ⟨spans 6, [⟨spans 7, .inferred ⟨spans 8, "ignored"⟩⟩]⟩ none
    ⟨spans 9, [⟨spans 10, .returnStmt (some (one .logicalNot spans (ref spans "saved")))⟩]⟩⟩
private def savedNames (owner : Resolved.DeclarationId) (tail : LocalNameTable) :=
  ("saved", (⟨owner, 7⟩ : Resolved.LocalId)) :: tail
private def savedCaptured (owner : Resolved.DeclarationId) (b : Bool)
    (tail : Resolved.LocalScope RuntimeValue) := (⟨owner, 7⟩, RuntimeValue.bool b) :: tail
private def callerNames (owner : Resolved.DeclarationId) (tail : LocalNameTable) :=
  ("picked", (⟨owner, 0⟩ : Resolved.LocalId)) :: ("saved", ⟨owner, 7⟩) :: tail
private def callerCaptured (owner : Resolved.DeclarationId) (made : RuntimeValue) (b : Bool)
    (tail : Resolved.LocalScope RuntimeValue) :=
  (⟨owner, 0⟩, made) :: (⟨owner, 7⟩, RuntimeValue.bool (!b)) :: tail
private def call (spans : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨spans 11, .call (ref (fun n => spans (n + 12)) "picked")
    ⟨spans 16, [⟨spans 17, .tuple ⟨spans 18, []⟩⟩]⟩⟩
private def outer (spans : Nat → Syntax.SourceSpan) :=
  one .logicalNot (fun n => spans (n + 19)) (call spans)

theorem saved_body_and_outer_call_images
    (spans : Nat → Syntax.SourceSpan) (callerOwner savedOwner : Resolved.DeclarationId)
    (different : callerOwner ≠ savedOwner) (input : Bool)
    (savedNameTail callerNameTail : LocalNameTable)
    (savedTail callerTail : Resolved.LocalScope RuntimeValue)
    (creationStore store : List RuntimeValue) :
    let original := savedOriginal spans
    let sn := savedNames savedOwner savedNameTail
    let sc := savedCaptured savedOwner input savedTail
    ClosedSourceExpressionEvaluates savedOwner sn sc creationStore original
      (.sourceClosure original savedOwner sn sc) creationStore ∧
    ∀ made, ClosedSourceExpressionEvaluates savedOwner sn sc creationStore
      original made creationStore →
      let cn := callerNames callerOwner callerNameTail
      let cc := callerCaptured callerOwner made input callerTail
      ClosedSourceExpressionEvaluates callerOwner cn cc store (call spans)
        (.bool (!input)) store ∧
      (∀ actual final, ClosedSourceExpressionEvaluates callerOwner cn cc store
        (outer spans) actual final ↔ actual = .bool input ∧ final = store) := by
  have created : ClosedSourceExpressionEvaluates savedOwner
      (savedNames savedOwner savedNameTail) (savedCaptured savedOwner input savedTail)
      creationStore (savedOriginal spans)
      (.sourceClosure (savedOriginal spans) savedOwner (savedNames savedOwner savedNameTail)
        (savedCaptured savedOwner input savedTail)) creationStore := .creation .inferred
  refine ⟨created, ?_⟩
  intro made returned
  obtain ⟨rfl, _⟩ := returned.deterministic created
  have fresh : Resolved.freshLocalId savedOwner
      ((savedNames savedOwner savedNameTail).map Prod.snd) ≠ ⟨savedOwner, 7⟩ := by
    intro same
    apply Resolved.freshLocalId_not_mem savedOwner
      ((savedNames savedOwner savedNameTail).map Prod.snd)
    rw [same]
    exact List.mem_cons_self
  have conflict : (⟨callerOwner, 7⟩ : Resolved.LocalId) ≠ ⟨savedOwner, 7⟩ := by
    intro same
    exact different (congrArg Resolved.LocalId.owner same)
  have invoked : ClosedSourceExpressionEvaluates callerOwner
      (callerNames callerOwner callerNameTail)
      (callerCaptured callerOwner
        (.sourceClosure (savedOriginal spans) savedOwner (savedNames savedOwner savedNameTail)
          (savedCaptured savedOwner input savedTail)) input callerTail)
      store (call spans) (.bool (!input)) store :=
    .call .inferred (.reference .head .head) .unit
      (.expression (.logicalNot
        (.reference (.tail (by change "ignored" ≠ "saved"; decide) .head) (.tail fresh .head))))
  refine ⟨invoked, ?_⟩
  intro actual final
  constructor
  · intro evaluated
    obtain ⟨b, child, same⟩ := closedSourceExpressionEvaluates_logicalNot_iff.mp evaluated
    obtain ⟨valueSame, rfl⟩ := child.deterministic invoked
    cases valueSame
    exact ⟨by simpa only [Bool.not_not] using same, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact closedSourceExpressionEvaluates_logicalNot_iff.mpr
      ⟨!input, invoked, by simp only [Bool.not_not]⟩

private def rejectNames (owner : Resolved.DeclarationId) (tail : LocalNameTable) :=
  ("w", (⟨owner, 0⟩ : Resolved.LocalId)) :: ("b", ⟨owner, 1⟩) ::
    ("u", ⟨owner, 2⟩) :: ("f", ⟨owner, 3⟩) :: tail
private def rejectCaptured (owner : Resolved.DeclarationId) (w : Core.Word) (b : Bool)
    (closure : Syntax.Expr) (tail : Resolved.LocalScope RuntimeValue) :=
  (⟨owner, 0⟩, RuntimeValue.word w) :: (⟨owner, 1⟩, .bool b) ::
    (⟨owner, 2⟩, .unit) :: (⟨owner, 3⟩, .sourceClosure closure owner [] []) :: tail
private def rejectedTerms (spans : Nat → Syntax.SourceSpan) : List Syntax.Expr :=
  [one .logicalNot spans (ref spans "w"), one .bitNot spans (ref spans "b"),
    one .logicalNot spans (one .bitNot (fun n => spans (n + 4)) (ref spans "w")),
    one .bitNot spans (one .logicalNot (fun n => spans (n + 4)) (ref spans "b")),
    one .logicalNot spans (ref spans "u"), one .bitNot spans (ref spans "u"),
    one .logicalNot spans (ref spans "f"), one .bitNot spans (ref spans "f")]
private def missingRef (spans : Nat → Syntax.SourceSpan) := ref spans "missing"

private theorem wrong_bool {owner names captured store operand value finalStore}
    (original : ClosedSourceExpressionEvaluates owner names captured store operand value finalStore)
    (wrong : ∀ b, value ≠ .bool b) (spans : Nat → Syntax.SourceSpan) :
    ∀ actual final, ¬ ClosedSourceExpressionEvaluates owner names captured store
      (one .logicalNot spans operand) actual final := by
  intro actual final evaluated
  obtain ⟨b, child, _⟩ := closedSourceExpressionEvaluates_logicalNot_iff.mp evaluated
  exact wrong b (original.deterministic child).1

private theorem wrong_word {owner names captured store operand value finalStore}
    (original : ClosedSourceExpressionEvaluates owner names captured store operand value finalStore)
    (wrong : ∀ w, value ≠ .word w) (spans : Nat → Syntax.SourceSpan) :
    ∀ actual final, ¬ ClosedSourceExpressionEvaluates owner names captured store
      (one .bitNot spans operand) actual final := by
  intro actual final evaluated
  obtain ⟨w, child, _⟩ := closedSourceExpressionEvaluates_bitNot_iff.mp evaluated
  exact wrong w (original.deterministic child).1

theorem wrong_missing_zero_and_nested_mismatch
    (spans : Nat → Syntax.SourceSpan) (owner : Resolved.DeclarationId)
    (nameTail : LocalNameTable) (captureTail : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (word : Core.Word) (choice : Bool)
    (closure : Syntax.Expr) :
    let names := rejectNames owner nameTail
    let captured := rejectCaptured owner word choice closure captureTail
    (∀ term ∈ rejectedTerms spans, ∀ budget,
      evaluateClosedSourceExpression? budget owner names captured store term = none ∧
      ∀ actual final, ¬ ClosedSourceExpressionEvaluates owner names captured store
        term actual final) ∧
    (∀ op : Syntax.UnaryOp, ∀ budget,
      evaluateClosedSourceExpression? budget owner [] captureTail store
        (one op spans (missingRef spans)) = none) ∧
    (∀ term, evaluateClosedSourceExpression? 0 owner names captured store term = none) := by
  have w : ClosedSourceExpressionEvaluates owner (rejectNames owner nameTail)
      (rejectCaptured owner word choice closure captureTail) store
      (ref spans "w") (.word word) store := .reference .head .head
  have b : ClosedSourceExpressionEvaluates owner (rejectNames owner nameTail)
      (rejectCaptured owner word choice closure captureTail) store
      (ref spans "b") (.bool choice) store :=
    .reference (.tail (by change "w" ≠ "b"; decide) .head)
      (.tail (by intro h; have := congrArg Resolved.LocalId.binderIndex h; simp at this) .head)
  have u : ClosedSourceExpressionEvaluates owner (rejectNames owner nameTail)
      (rejectCaptured owner word choice closure captureTail) store (ref spans "u") .unit store :=
    .reference (.tail (by change "w" ≠ "u"; decide) (.tail (by change "b" ≠ "u"; decide) .head))
      (.tail (by intro h; have := congrArg Resolved.LocalId.binderIndex h; simp at this)
        (.tail (by intro h; have := congrArg Resolved.LocalId.binderIndex h; simp at this) .head))
  have f : ClosedSourceExpressionEvaluates owner (rejectNames owner nameTail)
      (rejectCaptured owner word choice closure captureTail) store (ref spans "f")
      (.sourceClosure closure owner [] []) store :=
    .reference (.tail (by change "w" ≠ "f"; decide) (.tail (by change "b" ≠ "f"; decide)
      (.tail (by change "u" ≠ "f"; decide) .head)))
      (.tail (by intro h; have := congrArg Resolved.LocalId.binderIndex h; simp at this)
        (.tail (by intro h; have := congrArg Resolved.LocalId.binderIndex h; simp at this)
          (.tail (by intro h; have := congrArg Resolved.LocalId.binderIndex h; simp at this) .head)))
  have innerW : ClosedSourceExpressionEvaluates owner (rejectNames owner nameTail)
      (rejectCaptured owner word choice closure captureTail) store
      (one .bitNot (fun n => spans (n + 4)) (ref spans "w")) (.word word.bitNot) store := .bitNot w
  have innerB : ClosedSourceExpressionEvaluates owner (rejectNames owner nameTail)
      (rejectCaptured owner word choice closure captureTail) store
      (one .logicalNot (fun n => spans (n + 4)) (ref spans "b")) (.bool (!choice)) store := .logicalNot b
  have innerRuns :
      evaluateClosedSourceExpression? 2 owner (rejectNames owner nameTail)
        (rejectCaptured owner word choice closure captureTail) store
        (one .bitNot (fun n => spans (n + 4)) (ref spans "w")) = some (.word word.bitNot, store) ∧
      evaluateClosedSourceExpression? 2 owner (rejectNames owner nameTail)
        (rejectCaptured owner word choice closure captureTail) store
        (one .logicalNot (fun n => spans (n + 4)) (ref spans "b")) = some (.bool (!choice), store) := by
    simp only [one, evaluateClosedSourceExpression?_logicalNot, evaluateClosedSourceExpression?_bitNot]
    simp [ref, evaluateClosedSourceExpression?, rejectNames, rejectCaptured,
      LocalNameTable.lookup?, Resolved.LocalScope.lookup?]
  refine ⟨?_, ?_, fun _ => by rw [evaluateClosedSourceExpression?]⟩
  · intro term member budget
    constructor
    · simp only [rejectedTerms, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases budget with _ | (_ | (_ | budget)) <;>
        simp only [one, evaluateClosedSourceExpression?_logicalNot, evaluateClosedSourceExpression?_bitNot] <;>
        simp [ref, evaluateClosedSourceExpression?, rejectNames, rejectCaptured,
          LocalNameTable.lookup?, Resolved.LocalScope.lookup?]
    · simp only [rejectedTerms, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact wrong_bool w (by intro _ h; cases h) spans
      · exact wrong_word b (by intro _ h; cases h) spans
      · exact wrong_bool innerW (by intro _ h; cases h) spans
      · exact wrong_word innerB (by intro _ h; cases h) spans
      · exact wrong_bool u (by intro _ h; cases h) spans
      · exact wrong_word u (by intro _ h; cases h) spans
      · exact wrong_bool f (by intro _ h; cases h) spans
      · exact wrong_word f (by intro _ h; cases h) spans
  · intro op budget
    cases op <;> rcases budget with _ | (_ | budget) <;>
      simp only [one, evaluateClosedSourceExpression?_logicalNot, evaluateClosedSourceExpression?_bitNot] <;>
      simp [missingRef, ref, evaluateClosedSourceExpression?, LocalNameTable.lookup?]

end Tests.ClosedSourceUnaryBoundary
end

section
-- leanmerge: from Solcore.Test.FrontendClosedSourceUnaryProperties
/- Independent old-API unary costs precede original mixed-value image and depth laws.
Complete Core and mixed tails/stores remain separate; no projection is asserted. -/
set_option autoImplicit false
namespace Tests.ClosedSourceUnary
open Solcore Solcore.Frontend

private def nest (op : Syntax.UnaryOp) (spans : Nat → Syntax.SourceSpan) :
    Nat → Syntax.Expr → Syntax.Expr
  | 0, leaf => leaf
  | n + 1, leaf =>
      ⟨spans (2 * n), .unary ⟨spans (2 * n + 1), op⟩ (nest op spans n leaf)⟩

private def bval : Nat → Bool → Bool
  | 0, input => input
  | n + 1, input => !(bval n input)

private def wval : Nat → Core.Word → Core.Word
  | 0, input => input
  | n + 1, input => (wval n input).bitNot

private def coreNest (op : Core.UnaryOp) : Nat → Core.Expr
  | 0 => .var 0
  | n + 1 => .unary op (coreNest op n)

private def resolvedNest (op : Core.UnaryOp) (id : Resolved.LocalId) : Nat → Resolved.Expr
  | 0 => .var id
  | n + 1 => .unary op (resolvedNest op id n)

private theorem bool_resolution (n : Nat) (spans : Nat → Syntax.SourceSpan)
    (leafSpan : Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (names : LocalNameTable) (named : LocalNameTable.Lookup names name.value id) :
    ResolvesLocalExpression names (nest .logicalNot spans n ⟨leafSpan, .identifier name⟩)
      (resolvedNest .boolNot id n) := by
  induction n with
  | zero => exact .identifier named
  | succ n ih => exact .logicalNot ih

private theorem word_resolution (n : Nat) (spans : Nat → Syntax.SourceSpan)
    (leafSpan : Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (names : LocalNameTable) (named : LocalNameTable.Lookup names name.value id) :
    ResolvesLocalExpression names (nest .bitNot spans n ⟨leafSpan, .identifier name⟩)
      (resolvedNest .wordNot id n) := by
  induction n with
  | zero => exact .identifier named
  | succ n ih => exact .bitNot ih

private theorem nesting_lowered (op : Core.UnaryOp) (id : Resolved.LocalId)
    (scope : List Resolved.LocalId) (n : Nat) :
    Resolved.Lowers (id :: scope) (resolvedNest op id n) (coreNest op n) := by
  induction n with
  | zero => exact .var .head
  | succ n ih => exact .unary ih

private theorem independent_bool_cost (n : Nat) (spans : Nat → Syntax.SourceSpan)
    (leafSpan : Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (names : LocalNameTable) (input : Bool) (coreTail : Resolved.Environment)
    (coreStore : Core.Store) (named : LocalNameTable.Lookup names name.value id) :
    let original := nest .logicalNot spans n ⟨leafSpan, .identifier name⟩
    LocalExpressionEvaluatesWithCost names ((id, .bool input) :: coreTail)
      coreStore original (.bool (bval n input)) coreStore (2 * n + 1) ∧
    Core.Steps (2 * n + 1)
      (Core.State.initial (coreNest .boolNot n)
        (.bool input :: Resolved.LocalScope.values coreTail) coreStore)
      (Core.State.final (.bool (bval n input)) coreStore) := by
  have cost : LocalExpressionEvaluatesWithCost names ((id, .bool input) :: coreTail)
      coreStore (nest .logicalNot spans n ⟨leafSpan, .identifier name⟩)
      (.bool (bval n input)) coreStore (2 * n + 1) := by
    induction n with
    | zero => exact .identifier named .head
    | succ n ih =>
        simpa [nest, bval, Nat.mul_add, Nat.add_assoc] using
          LocalExpressionEvaluatesWithCost.logicalNot ih
  exact ⟨cost, cost.toSteps (bool_resolution n spans leafSpan name id names named)
    (nesting_lowered .boolNot id (Resolved.LocalScope.ids coreTail) n)⟩

private theorem independent_word_cost (n : Nat) (spans : Nat → Syntax.SourceSpan)
    (leafSpan : Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (names : LocalNameTable) (input : Core.Word) (coreTail : Resolved.Environment)
    (coreStore : Core.Store) (named : LocalNameTable.Lookup names name.value id) :
    let original := nest .bitNot spans n ⟨leafSpan, .identifier name⟩
    LocalExpressionEvaluatesWithCost names ((id, .word input) :: coreTail)
      coreStore original (.word (wval n input)) coreStore (2 * n + 1) ∧
    Core.Steps (2 * n + 1)
      (Core.State.initial (coreNest .wordNot n)
        (.word input :: Resolved.LocalScope.values coreTail) coreStore)
      (Core.State.final (.word (wval n input)) coreStore) := by
  have cost : LocalExpressionEvaluatesWithCost names ((id, .word input) :: coreTail)
      coreStore (nest .bitNot spans n ⟨leafSpan, .identifier name⟩)
      (.word (wval n input)) coreStore (2 * n + 1) := by
    induction n with
    | zero => exact .identifier named .head
    | succ n ih =>
        simpa [nest, wval, Nat.mul_add, Nat.add_assoc] using
          LocalExpressionEvaluatesWithCost.bitNot ih
  exact ⟨cost, cost.toSteps (word_resolution n spans leafSpan name id names named)
    (nesting_lowered .wordNot id (Resolved.LocalScope.ids coreTail) n)⟩

private theorem original_bool (n : Nat) (spans : Nat → Syntax.SourceSpan)
    (leafSpan : Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (input : Bool)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id (.bool input)) :
    ClosedSourceExpressionEvaluates owner names captured store
      (nest .logicalNot spans n ⟨leafSpan, .identifier name⟩) (.bool (bval n input)) store := by
  induction n with
  | zero => exact .reference named found
  | succ n ih => exact .logicalNot ih

private theorem original_word (n : Nat) (spans : Nat → Syntax.SourceSpan)
    (leafSpan : Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (input : Core.Word)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id (.word input)) :
    ClosedSourceExpressionEvaluates owner names captured store
      (nest .bitNot spans n ⟨leafSpan, .identifier name⟩) (.word (wval n input)) store := by
  induction n with
  | zero => exact .reference named found
  | succ n ih => exact .bitNot ih

private theorem bool_images (n : Nat) (spans : Nat → Syntax.SourceSpan)
    (leafSpan : Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (input : Bool)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id (.bool input)) :
    ∀ actual final, ClosedSourceExpressionEvaluates owner names captured store
      (nest .logicalNot spans n ⟨leafSpan, .identifier name⟩) actual final ↔
      actual = .bool (bval n input) ∧ final = store := by
  induction n with
  | zero =>
      intro actual final
      constructor
      · intro evaluated
        cases evaluated with
        | reference otherNamed otherFound =>
            cases named.id_unique otherNamed
            exact ⟨otherFound.value_unique found, rfl⟩
        | creation shape => cases shape
      · rintro ⟨rfl, rfl⟩; exact .reference named found
  | succ n ih =>
      intro actual final
      have image := closedSourceExpressionEvaluates_logicalNot_iff
        (owner := owner) (names := names) (captured := captured) (initialStore := store)
        (finalStore := final) (span := spans (2 * n)) (operatorSpan := spans (2 * n + 1))
        (operand := nest .logicalNot spans n ⟨leafSpan, .identifier name⟩) (value := actual)
      constructor
      · intro evaluated
        obtain ⟨value, child, same⟩ := image.mp evaluated
        obtain ⟨valueEq, storeEq⟩ := (ih _ _).mp child
        rw [RuntimeValue.bool.inj valueEq] at same
        exact ⟨same, storeEq⟩
      · rintro ⟨same, storeEq⟩
        refine image.mpr ⟨bval n input, ?_, same⟩
        rw [storeEq]
        exact original_bool n spans leafSpan name id owner names captured store input named found

private theorem word_images (n : Nat) (spans : Nat → Syntax.SourceSpan)
    (leafSpan : Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (input : Core.Word)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id (.word input)) :
    ∀ actual final, ClosedSourceExpressionEvaluates owner names captured store
      (nest .bitNot spans n ⟨leafSpan, .identifier name⟩) actual final ↔
      actual = .word (wval n input) ∧ final = store := by
  induction n with
  | zero =>
      intro actual final
      constructor
      · intro evaluated
        cases evaluated with
        | reference otherNamed otherFound =>
            cases named.id_unique otherNamed
            exact ⟨otherFound.value_unique found, rfl⟩
        | creation shape => cases shape
      · rintro ⟨rfl, rfl⟩; exact .reference named found
  | succ n ih =>
      intro actual final
      have image := closedSourceExpressionEvaluates_bitNot_iff
        (owner := owner) (names := names) (captured := captured) (initialStore := store)
        (finalStore := final) (span := spans (2 * n)) (operatorSpan := spans (2 * n + 1))
        (operand := nest .bitNot spans n ⟨leafSpan, .identifier name⟩) (value := actual)
      constructor
      · intro evaluated
        obtain ⟨value, child, same⟩ := image.mp evaluated
        obtain ⟨valueEq, storeEq⟩ := (ih _ _).mp child
        rw [RuntimeValue.word.inj valueEq] at same
        exact ⟨same, storeEq⟩
      · rintro ⟨same, storeEq⟩
        refine image.mpr ⟨wval n input, ?_, same⟩
        rw [storeEq]
        exact original_word n spans leafSpan name id owner names captured store input named found

private theorem bool_depth (n : Nat) (spans : Nat → Syntax.SourceSpan)
    (leafSpan : Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (input : Bool)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id (.bool input)) :
    evaluateClosedSourceExpression? (n + 1) owner names captured store
      (nest .logicalNot spans n ⟨leafSpan, .identifier name⟩) = some (.bool (bval n input), store) ∧
    evaluateClosedSourceExpression? n owner names captured store
      (nest .logicalNot spans n ⟨leafSpan, .identifier name⟩) = none := by
  induction n with
  | zero =>
      simp [nest, bval, evaluateClosedSourceExpression?, LocalNameTable.lookup?_iff.mpr named,
        Resolved.LocalScope.lookup?_iff.mpr found]
  | succ n ih =>
      simp only [nest, bval, evaluateClosedSourceExpression?_logicalNot, ih.1, ih.2,
        bind, Option.bind_some, Option.bind_none, pure, and_self]

private theorem word_depth (n : Nat) (spans : Nat → Syntax.SourceSpan)
    (leafSpan : Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (input : Core.Word)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id (.word input)) :
    evaluateClosedSourceExpression? (n + 1) owner names captured store
      (nest .bitNot spans n ⟨leafSpan, .identifier name⟩) = some (.word (wval n input), store) ∧
    evaluateClosedSourceExpression? n owner names captured store
      (nest .bitNot spans n ⟨leafSpan, .identifier name⟩) = none := by
  induction n with
  | zero =>
      simp [nest, wval, evaluateClosedSourceExpression?, LocalNameTable.lookup?_iff.mpr named,
        Resolved.LocalScope.lookup?_iff.mpr found]
  | succ n ih =>
      simp only [nest, wval, evaluateClosedSourceExpression?_bitNot, ih.1, ih.2,
        bind, Option.bind_some, Option.bind_none, pure, and_self]

theorem bool_nesting_original_images_and_cost
    (n : Nat) (spans : Nat → Syntax.SourceSpan) (leafSpan : Syntax.SourceSpan)
    (name : Syntax.Identifier) (id : Resolved.LocalId)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (input : Bool) (coreTail : Resolved.Environment) (coreStore : Core.Store)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id (.bool input)) :
    let original := nest .logicalNot spans n ⟨leafSpan, .identifier name⟩
    LocalExpressionEvaluatesWithCost names ((id, .bool input) :: coreTail)
      coreStore original (.bool (bval n input)) coreStore (2 * n + 1) ∧
    Core.Steps (2 * n + 1)
      (Core.State.initial (coreNest .boolNot n)
        (.bool input :: Resolved.LocalScope.values coreTail) coreStore)
      (Core.State.final (.bool (bval n input)) coreStore) ∧
    ClosedSourceExpressionEvaluates owner names captured store original
      (.bool (bval n input)) store ∧
    (∀ actual final, ClosedSourceExpressionEvaluates owner names captured store
      original actual final ↔ actual = .bool (bval n input) ∧ final = store) ∧
    evaluateClosedSourceExpression? (n + 1) owner names captured store original =
      some (.bool (bval n input), store) ∧
    evaluateClosedSourceExpression? n owner names captured store original = none := by
  have cost := independent_bool_cost n spans leafSpan name id names input coreTail coreStore named
  have original := original_bool n spans leafSpan name id owner names captured store input named found
  exact ⟨cost.1, cost.2, original,
    bool_images n spans leafSpan name id owner names captured store input named found,
    bool_depth n spans leafSpan name id owner names captured store input named found⟩

theorem word_nesting_original_images_and_cost
    (n : Nat) (spans : Nat → Syntax.SourceSpan) (leafSpan : Syntax.SourceSpan)
    (name : Syntax.Identifier) (id : Resolved.LocalId)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (input : Core.Word) (coreTail : Resolved.Environment) (coreStore : Core.Store)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id (.word input)) :
    let original := nest .bitNot spans n ⟨leafSpan, .identifier name⟩
    LocalExpressionEvaluatesWithCost names ((id, .word input) :: coreTail)
      coreStore original (.word (wval n input)) coreStore (2 * n + 1) ∧
    Core.Steps (2 * n + 1)
      (Core.State.initial (coreNest .wordNot n)
        (.word input :: Resolved.LocalScope.values coreTail) coreStore)
      (Core.State.final (.word (wval n input)) coreStore) ∧
    ClosedSourceExpressionEvaluates owner names captured store original
      (.word (wval n input)) store ∧
    (∀ actual final, ClosedSourceExpressionEvaluates owner names captured store
      original actual final ↔ actual = .word (wval n input) ∧ final = store) ∧
    evaluateClosedSourceExpression? (n + 1) owner names captured store original =
      some (.word (wval n input), store) ∧
    evaluateClosedSourceExpression? n owner names captured store original = none := by
  have cost := independent_word_cost n spans leafSpan name id names input coreTail coreStore named
  have original := original_word n spans leafSpan name id owner names captured store input named found
  exact ⟨cost.1, cost.2, original,
    word_images n spans leafSpan name id owner names captured store input named found,
    word_depth n spans leafSpan name id owner names captured store input named found⟩

end Tests.ClosedSourceUnary
end

section
-- leanmerge: from Solcore.Test.FrontendParsedClosedSourceClosures
set_option autoImplicit false
namespace Tests
namespace ParsedClosedSourceClosures
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private abbrev Store := List RuntimeValue
private abbrev Captures := Resolved.LocalScope RuntimeValue
private def check (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def word (n : Nat) : Core.Word := ⟨n % Core.wordModulus,Nat.mod_lt _ (by decide)⟩
private def zero : RuntimeValue := .word (word 0)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ClosedSourceCalls",by decide⟩],by decide⟩⟩,157⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=900},700⟩
private def names : LocalNameTable := [("saved",sid 7),("other",sid 8),("c",sid 3),("tag",sid 31),("saved",sid 9),("x",foreign)]
private def captures (s o : RuntimeValue) (c hit : Bool) : Captures :=
  [(sid 32,.unit),(sid 7,s),(sid 8,o),(sid 31,.word (word (if hit then 0 else 1))),(sid 7,.bool false),(sid 3,.bool c),(foreign,.unit)]
private def pn := ("x",sid 32)::names
private def pe (s o : RuntimeValue) (c hit : Bool) := (sid 32,s)::captures s o c hit
private def fn := ("f",sid 33)::pn
private def closure (source : Syntax.Expr) (s o : RuntimeValue) (c hit : Bool) : RuntimeValue := .sourceClosure source owner pn (pe s o c hit)
private def fe (source : Syntax.Expr) (s o : RuntimeValue) (c hit : Bool) := (sid 33,closure source s o c hit)::pe s o c hit
private def tn := ("x",sid 34)::fn
private def te (source : Syntax.Expr) (s o : RuntimeValue) (c hit : Bool) := (sid 34,zero)::fe source s o c hit
private theorem fresh0 : Resolved.freshLocalId owner (names.map Prod.snd)=sid 32 := by decide
private theorem fresh1 : Resolved.freshLocalId owner (pn.map Prod.snd)=sid 33 := by decide
private theorem fresh2 : Resolved.freshLocalId owner (fn.map Prod.snd)=sid 34 := by decide
private structure Unary (source : Syntax.Expr) where
  name : Syntax.Identifier
  body : Syntax.Block
  shape : SourceUnaryLambdaShape source name body
private def unary : (source : Syntax.Expr) → IO (Unary source)
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred n⟩]⟩ _ b⟩ => pure ⟨n,b,.inferred⟩
  | ⟨_,.lambda _ ⟨_,[⟨_,.typed none n _⟩]⟩ _ b⟩ => pure ⟨n,b,.typed⟩
  | _ => throw (IO.userError "original unary source shape")
private def reference (ns : LocalNameTable) (es : Captures) (store : Store) (source : Syntax.Expr)
    (spelling : String) (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup ns spelling id) (found : Resolved.LocalScope.Lookup es id value) :
    IO (PLift (E owner ns es store source value store)) := do
  match shape : source with
  | ⟨_,.identifier n⟩ => if same : n.value=spelling then return ⟨by rw [shape]; exact .reference (same ▸ named) found⟩ else throw (IO.userError "original reference spelling")
  | _ => throw (IO.userError "original identifier")
private def pairBody (s o a : RuntimeValue) (c hit : Bool) (store : Store) (body : Syntax.Block) :
    IO (PLift (B owner (("y",sid 33)::pn) ((sid 33,a)::pe s o c hit) store body (.pair s a) store)) := do
  match shape : body with
  | ⟨_,[⟨_,.returnStmt (some ⟨_,.tuple ⟨_,[x,y]⟩⟩)⟩]⟩ =>
    let left ← reference (("y",sid 33)::pn) ((sid 33,a)::pe s o c hit) store x "x" (sid 32) s (.tail (by decide) .head) (.tail (by decide) .head)
    let right ← reference (("y",sid 33)::pn) ((sid 33,a)::pe s o c hit) store y "y" (sid 33) a .head .head
    return ⟨by rw [shape]; exact .expression (.pair left.down right.down)⟩
  | _ => throw (IO.userError "saved original pair return")
private def av (k : Nat) (s o : RuntimeValue) : RuntimeValue := match k with | 0 => zero | 1 => o | 2 => s | _ => .unit
private def argument (k : Nat) (fs : Syntax.Expr) (s o : RuntimeValue) (c hit : Bool) (store : Store) (e : Syntax.Expr) :
    IO (PLift (E owner tn (te fs s o c hit) store e (av k s o) store)) := do
  match index : k with
  | 0 =>
    let value ← reference tn (te fs s o c hit) store e "x" (sid 34) zero .head .head
    return ⟨by simpa only [index,av] using value.down⟩
  | 1 =>
    let value ← reference tn (te fs s o c hit) store e "other" (sid 8) o
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
    return ⟨by simpa only [index,av] using value.down⟩
  | 2 =>
    let value ← reference tn (te fs s o c hit) store e "saved" (sid 7) s
      (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
    return ⟨by simpa only [index,av] using value.down⟩
  | _+3 => match shape : e with
    | ⟨_,.tuple ⟨_,[]⟩⟩ => return ⟨by rw [shape,index]; exact .unit⟩
    | _ => throw (IO.userError "original empty tuple argument")
private def applyF (k : Nat) (fs : Syntax.Expr) (s o : RuntimeValue) (c hit : Bool) (store : Store) (e : Syntax.Expr) :
    IO (PLift (E owner tn (te fs s o c hit) store e (.pair s (av k s o)) store)) := do
  match shape : e with
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
    let header ← unary fs
    if parameter : header.name.value="y" then
      let callee ← reference tn (te fs s o c hit) store f "f" (sid 33) (closure fs s o c hit) (.tail (by decide) .head) (.tail (by decide) .head)
      let arg ← argument k fs s o c hit store a
      let body ← pairBody s o (av k s o) c hit store header.body
      return ⟨by rw [shape]; exact .call header.shape callee.down arg.down (by simpa only [parameter,fresh1] using body.down)⟩
    else throw (IO.userError "inner original parameter y")
  | _ => throw (IO.userError "original f unary call")
private def answer (s o : RuntimeValue) (c hit : Bool) : RuntimeValue :=
  if c then if hit then .pair (.pair s zero) (.pair (.pair s o) (.pair .unit s)) else .pair s s else .pair s o
private def returnedCall (k : Nat) (fs : Syntax.Expr) (s o : RuntimeValue) (c hit : Bool) (store : Store) (body : Syntax.Block) :
    IO (PLift (B owner tn (te fs s o c hit) store body (.pair s (av k s o)) store)) := do
  match shape : body with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let result ← applyF k fs s o c hit store e; return ⟨by rw [shape]; exact .expression result.down⟩
  | _ => throw (IO.userError "original selected call return")
private def four (fs : Syntax.Expr) (s o : RuntimeValue) (c hit : Bool) (store : Store) (body : Syntax.Block) :
    IO (PLift (B owner tn (te fs s o c hit) store body (.pair (.pair s zero) (.pair (.pair s o) (.pair .unit s))) store)) := do
  match shape : body with
  | ⟨_,[⟨_,.returnStmt (some ⟨_,.tuple ⟨_,[a,b,⟨_,.tuple ⟨_,[]⟩⟩,saved]⟩⟩)⟩]⟩ =>
    let left ← applyF 0 fs s o c hit store a; let middle ← applyF 1 fs s o c hit store b
    let last ← argument 2 fs s o c hit store saved
    return ⟨by rw [shape]; exact .expression (.many left.down (.many middle.down (.pair .unit last.down)))⟩
  | _ => throw (IO.userError "original flat four tuple with explicit unit third element")
private def selected (fs : Syntax.Expr) (s o : RuntimeValue) (c hit : Bool) (store : Store) (body : Syntax.Block) :
    IO (PLift (B owner tn (te fs s o c hit) store body (if hit then .pair (.pair s zero) (.pair (.pair s o) (.pair .unit s)) else .pair s s) store)) := do
  match shape : body with
  | ⟨_,[⟨_,.matchWith ⟨_,⟨tag,[]⟩⟩ ⟨_,⟨[first,wild],none⟩⟩⟩]⟩ =>
    let scrutinee ← reference tn (te fs s o c hit) store tag "tag" (sid 31) (.word (word (if hit then 0 else 1)))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))))
    match literal : first.value.pattern, wildcard : wild.value.pattern with
    | ⟨_,.literal ⟨_,.decimal "0"⟩⟩,⟨_,.group ⟨_,.group ⟨_,.wildcard _⟩⟩⟩ =>
      have pm : WordMatchPatternClassifies first.value.pattern (some (word 0)) := by rw [literal]; exact .literal ⟨_,rfl,.decimal (by decide) (.cons (.decimal (digit:=0) (by decide) rfl) .nil)⟩
      have wm : WordMatchPatternClassifies wild.value.pattern none := by rw [wildcard]; exact .group (.group (.wildcard rfl))
      if h : hit=true then
        let branch ← four fs s o c hit store first.value.body
        return ⟨by rw [shape]; simpa only [h,↓reduceIte] using ClosedSourceBodyEvaluates.wordMatch scrutinee.down (by simpa only [h,↓reduceIte] using RuntimeWordMatchChooses.hit pm) branch.down⟩
      else
        have hfalse : hit=false := by cases hit <;> simp_all
        let branch ← returnedCall 2 fs s o c hit store wild.value.body
        return ⟨by rw [shape]; simpa only [hfalse,Bool.false_eq_true,↓reduceIte,av] using ClosedSourceBodyEvaluates.wordMatch scrutinee.down (by simpa only [hfalse,Bool.false_eq_true,↓reduceIte] using RuntimeWordMatchChooses.miss pm (show word 1≠word 0 by decide) (.wildcard wm)) branch.down⟩
    | _,_ => throw (IO.userError "original literal/grouped-wildcard patterns")
  | _ => throw (IO.userError "original single-scrutinee two-arm match")
private def tailBody (fs : Syntax.Expr) (s o : RuntimeValue) (c hit : Bool) (store : Store) (body : Syntax.Block) :
    IO (PLift (B owner tn (te fs s o c hit) store body (answer s o c hit) store)) := do
  match shape : body with
  | ⟨_,[⟨_,.ifThen condition thenBody (some elseBody)⟩]⟩ =>
    let guard ← reference tn (te fs s o c hit) store condition "c" (sid 3) (.bool c)
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))))))
    if h : c=true then
      match explicit : thenBody with
      | ⟨_,[⟨innerSpan,.block statements⟩]⟩ =>
        let branch ← selected fs s o c hit store ⟨innerSpan,statements⟩
        have guardTrue : E owner tn (te fs s o c hit) store condition (.bool true) store := by simpa only [h] using guard.down
        have selectedBody : B owner tn (te fs s o c hit) store thenBody (if hit then .pair (.pair s zero) (.pair (.pair s o) (.pair .unit s)) else .pair s s) store := by rw [explicit]; exact .block branch.down
        return ⟨by rw [shape]; simpa only [answer,h,↓reduceIte] using ClosedSourceBodyEvaluates.ifTrue guardTrue selectedBody⟩
      | _ => throw (IO.userError "original explicit then block")
    else
      have hfalse : c=false := by cases c <;> simp_all
      let branch ← returnedCall 1 fs s o c hit store elseBody
      have guardFalse : E owner tn (te fs s o c hit) store condition (.bool false) store := by simpa only [hfalse] using guard.down
      return ⟨by rw [shape]; simpa only [answer,hfalse,Bool.false_eq_true,↓reduceIte,av] using ClosedSourceBodyEvaluates.ifFalse guardFalse branch.down⟩
  | _ => throw (IO.userError "original terminal conditional")
private def mainBody (s o : RuntimeValue) (c hit : Bool) (store : Store) (body : Syntax.Block) :
    IO (PLift (B owner pn (pe s o c hit) store body (answer s o c hit) store)) := do
  match shape : body with
  | ⟨span,⟨_,.letDecl f none (some fs)⟩::⟨xs,.letDecl x (some annotation) (some ⟨literalSpan,.literal literal⟩)⟩::⟨ds,.expression discard true⟩::rest⟩ =>
    let header ← unary fs
    if valid : f.value="f" ∧ x.value="x" then
      match zeroShape : literal with
      | ⟨_,.decimal "0"⟩ =>
        let ending ← tailBody fs s o c hit store ⟨span,rest⟩
        let discarded ← applyF 3 fs s o c hit store discard
        have tail : B owner tn (te fs s o c hit) store ⟨span,⟨ds,.expression discard true⟩::rest⟩ (answer s o c hit) store := .discard discarded.down ending.down
        have zeroProof : WordLiteralDenotes literal (word 0) := by rw [zeroShape]; exact .decimal (by decide) (.cons (.decimal (digit:=0) (by decide) rfl) .nil)
        have typed : B owner fn (fe fs s o c hit) store ⟨span,⟨xs,.letDecl x (some annotation) (some ⟨literalSpan,.literal literal⟩)⟩::⟨ds,.expression discard true⟩::rest⟩ (answer s o c hit) store :=
          .binding (.wordLiteral zeroProof) (by simpa only [valid.2,fresh2,tn,te,zero] using tail)
        return ⟨by rw [shape]; exact .inferred (.creation header.shape) (by simpa only [valid.1,fresh1,fn,fe,closure] using typed)⟩
      | _ => throw (IO.userError "original zero initializer")
    else throw (IO.userError "original function/shadow names")
  | _ => throw (IO.userError "original inferred f/typed x/discard prefix")
private def completed {ns es store source value} (proof : E owner ns es store source value store) : IO Unit := do
  have _ : ∀ v final, E owner ns es store source v final → v=value ∧ final=store := fun _ _ other => other.deterministic proof
  match shape : source with
  | ⟨span,.call callee ⟨argsSpan,[argument]⟩⟩ =>
    have literal : E owner ns es store ⟨span,.call callee ⟨argsSpan,[argument]⟩⟩ value store := by simpa only [shape] using proof
    have opened := closedSourceExpressionEvaluates_call_iff.mp literal
    have _ := (closedSourceExpressionEvaluates_call_iff (span:=span) (argumentsSpan:=argsSpan)).mpr opened
    pure ()
  | _ => throw (IO.userError "completed original unary call")
private def mainCall (s o : RuntimeValue) (c hit : Bool) (store : Store) (source : Syntax.Expr) : IO Unit := do
  match shape : source with
  | ⟨_,.call ⟨_,.group fs⟩ ⟨_,[arg]⟩⟩ =>
    let header ← unary fs
    if parameter : header.name.value="x" then
      let argument ← reference names (captures s o c hit) store arg "saved" (sid 7) s .head (.tail (by decide) .head)
      let body ← mainBody s o c hit store header.body
      have openBody := closedSourceBodyEvaluates_iff.mp body.down
      have closedBody := closedSourceBodyEvaluates_iff.mpr openBody
      have _ : ∀ v final, B owner pn (pe s o c hit) store header.body v final → v=answer s o c hit ∧ final=store := fun _ _ other => other.deterministic closedBody
      have evaluated : E owner names (captures s o c hit) store source (answer s o c hit) store := by
        rw [shape]; exact .call header.shape (.group (.creation header.shape)) argument.down (by simpa only [parameter,fresh0,pn,pe] using closedBody)
      completed evaluated
    else throw (IO.userError "outer original x")
  | _ => throw (IO.userError "original grouped outer lambda call")
private def nestedCall (s o : RuntimeValue) (c hit : Bool) (store : Store) (source : Syntax.Expr) : IO Unit := do
  match shape : source with
  | ⟨_,.call ⟨_,.group ⟨_,.call ⟨_,.group fs⟩ ⟨_,[arg]⟩⟩⟩ ⟨_,[other]⟩⟩ =>
    let outer ← unary fs
    match returned : outer.body with
    | ⟨_,[⟨_,.returnStmt (some innerSource)⟩]⟩ =>
      let inner ← unary innerSource
      if parameters : outer.name.value="x" ∧ inner.name.value="y" then
        let a ← reference names (captures s o c hit) store arg "saved" (sid 7) s .head (.tail (by decide) .head)
        let b ← reference names (captures s o c hit) store other "other" (sid 8) o (.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head))
        have innerCreated : B owner pn (pe s o c hit) store outer.body (closure innerSource s o c hit) store := by rw [returned]; exact .expression (.creation inner.shape)
        let pair ← pairBody s o o c hit store inner.body
        have evaluated : E owner names (captures s o c hit) store source (.pair s o) store := by
          rw [shape]; exact .call (savedNames:=pn) (savedCaptured:=pe s o c hit) inner.shape (.group (.call outer.shape (.group (.creation outer.shape)) a.down (by simpa only [parameters.1,fresh0,pn,pe,closure] using innerCreated))) b.down (by simpa only [parameters.2,fresh1] using pair.down)
        completed evaluated
      else throw (IO.userError "original nested x/y names")
    | _ => throw (IO.userError "original returned lambda expression")
  | _ => throw (IO.userError "two original nested unary calls")
private def bareCall (s o : RuntimeValue) (c hit : Bool) (store : Store) (source : Syntax.Expr) : IO Unit := do
  match shape : source with
  | ⟨_,.call ⟨_,.group fs⟩ ⟨_,[arg]⟩⟩ =>
    let header ← unary fs
    match originalBody : header.body with
    | ⟨_,[⟨_,.matchWith ⟨_,⟨x,[]⟩⟩ ⟨_,⟨[],some ⟨_,[⟨_,.returnStmt none⟩]⟩⟩⟩⟩]⟩ =>
      if parameter : header.name.value="x" then
        let a ← reference names (captures s o c hit) store arg "saved" (sid 7) s .head (.tail (by decide) .head)
        let scrutinee ← reference pn (pe s o c hit) store x "x" (sid 32) s .head .head
        have body : B owner pn (pe s o c hit) store header.body .unit store := by rw [originalBody]; exact .wordMatch scrutinee.down .fallback .bare
        have _ := closedSourceBodyEvaluates_iff.mp body
        have evaluated : E owner names (captures s o c hit) store source .unit store := by
          rw [shape]; exact .call header.shape (.group (.creation header.shape)) a.down (by simpa only [parameter,fresh0,pn,pe] using body)
        completed evaluated
      else throw (IO.userError "original bare lambda parameter")
    | _ => throw (IO.userError "original default-only bare body")
  | _ => throw (IO.userError "original bare lambda call")
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"closed-source-captures.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next => check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && source.span == Syntax.SourceSpan.fullFile file) "full original source/span"; return source
  | .reject _ _ => throw (IO.userError "parser rejection")
  | .invariant _ => throw (IO.userError "parser invariant")
end ParsedClosedSourceClosures

open ParsedClosedSourceClosures in
/-- Constructor-built callback-free proofs for original source closure calls; no execution bound or typing claim. -/
def frontendParsedClosedSourceClosureTests : IO Unit := do
  let mainSource ← parsed "(lam(x:Unknown)->Unknown{let f=lam(y){return (x,y);};let x:Missing=0;f(());if(c){{match(tag){case 0{return (f(x),f(other),(),saved);}case ((_)){return f(saved);}}}}else{return f(other);}})(saved)"
  let nested ← parsed "((lam(x){return lam(y){return (x,y);};})(saved))(other)"
  let bare ← parsed "(lam(x){match(x){default{return;}}})(saved)"
  let inert ← parsed "lam(){return absent;}"
  let saved := Solcore.Frontend.RuntimeValue.sourceClosure inert owner names [(sid 32,.bool false)]
  for other in [.hostFunction .storageWrite,.coreClosure .unit .word (.var 99) [saved,.cellRef .word 700]] do
    for store in [[.unit],[saved,.cellRef (.function .word .word) 1]] do
      mainCall saved other true true store mainSource
      mainCall saved other true false store mainSource
      mainCall saved other false true store mainSource
      nestedCall saved other false false store nested
      bareCall saved other true false store bare

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedClosedSourceConditionals
/- Independent original certificates precede search; actual returned closures and
stores are reused under a different caller. None is not a runtime fault. -/
set_option autoImplicit false
namespace Tests
namespace ParsedClosedSourceConditionals
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev C := Resolved.LocalScope V
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def check (b : Bool) (label : String) : IO Unit := unless b do throw (IO.userError label)
private def mainText := "(lam(x:Unknown)->Unknown{let f=c?lam(y){return d?(x,y):(y,x);}:lam(y){return (y,x);};let x:Missing=0;return ((c?f:lam(y){return (x,y);})(c?x:other),f);})(saved)"
private def yesText := "(c?lam(y){return y;}:missing())(saved)"
private def noText := "(c?missing():lam(y){return y;})(saved)"
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ClosedSourceConditionals",by decide⟩],by decide⟩⟩,159⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=900},700⟩
private def w (n : Nat) : Core.Word := ⟨n % Core.wordModulus,Nat.mod_lt _ (by decide)⟩
private def names : LocalNameTable := [("saved",sid 7),("other",sid 8),("c",sid 3),("d",sid 31),("saved",sid 9),("x",foreign)]
private def rows (s o d : V) (c : Bool) (extra : C) : C :=
  [(sid 32,.unit),(sid 7,s),(sid 8,o),(sid 31,d),(sid 7,.bool false),(sid 3,.bool c),(foreign,.unit)]++extra
private def pn := ("x",sid 32)::names
private def pe (s o d : V) (c : Bool) (extra : C) := (sid 32,s)::rows s o d c extra
private def fn := ("f",sid 33)::pn
private def fv (fs : Syntax.Expr) (s o d : V) (c : Bool) (extra : C) : V := .sourceClosure fs owner pn (pe s o d c extra)
private def tn := ("x",sid 34)::fn
private def te (fs : Syntax.Expr) (s o d : V) (c : Bool) (extra : C) := (sid 34,RuntimeValue.word (w 0))::(sid 33,fv fs s o d c extra)::pe s o d c extra
private theorem fresh0 : Resolved.freshLocalId owner (names.map Prod.snd)=sid 32 := by decide
private theorem fresh1 : Resolved.freshLocalId owner (pn.map Prod.snd)=sid 33 := by decide
private theorem fresh2 : Resolved.freshLocalId owner (fn.map Prod.snd)=sid 34 := by decide
private theorem fresh3 : Resolved.freshLocalId owner (tn.map Prod.snd)=sid 35 := by decide
private def pairResult (reverse : Bool) (x a : V) : V := if reverse then .pair a x else .pair x a
private def ref (own : Resolved.DeclarationId) (ns : LocalNameTable) (es : C) (st : List V) (e : Syntax.Expr)
    (name : String) (id : Resolved.LocalId) (value : V) (named : LocalNameTable.Lookup ns name id) (found : Resolved.LocalScope.Lookup es id value) : IO (PLift (E own ns es st e value st)) := do
  match shape : e with
  | ⟨_,.identifier n⟩ => if same : n.value=name then return ⟨by rw [shape]; exact .reference (same ▸ named) found⟩ else throw (IO.userError "original reference name")
  | _ => throw (IO.userError "original reference")
private structure OriginalConditional (source : Syntax.Expr) where
  span : Syntax.SourceSpan
  condition : Syntax.Expr
  question : Syntax.SourceSpan
  yes : Syntax.Expr
  colon : Syntax.SourceSpan
  no : Syntax.Expr
  exactSource : source=⟨span,.conditional condition question yes colon no⟩
private def originalConditional : (source : Syntax.Expr) → IO (OriginalConditional source)
  | ⟨s,.conditional c q y colon n⟩ => do
    let text := if s.endByte==30 then if colon.startByte==20 then yesText else noText else mainText
    check ([(31,84,32,62),(47,60,48,54),(110,135,111,113),(137,146,138,140),(1,30,2,20),(1,30,2,12)].contains (s.startByte,s.endByte,q.startByte,colon.startByte) && text.toUTF8[q.startByte]? == some 63 && text.toUTF8[colon.startByte]? == some 58) "literal original ranges and punctuation bytes"
    check (s.contains c.span && s.contains y.span && s.contains n.span && c.span.endByte≤q.startByte &&
      q.length==1 && q.endByte≤y.span.startByte && y.span.endByte≤colon.startByte && colon.length==1 && colon.endByte≤n.span.startByte) "original ?: spans and order"
    pure ⟨s,c,q,y,colon,n,rfl⟩
  | _ => throw (IO.userError "original conditional")
private theorem chosen {source own ns es st value} (p : OriginalConditional source) (c : Bool)
    (guard : E own ns es st p.condition (.bool c) st)
    (branch : E own ns es st (if c then p.yes else p.no) value st) : E own ns es st source value st := by
  rw [p.exactSource]
  have independent : E own ns es st ⟨p.span,.conditional p.condition p.question p.yes p.colon p.no⟩ value st := by
    cases c <;> first | exact .conditionalFalse guard branch | exact .conditionalTrue guard branch
  exact closedSourceExpressionEvaluates_conditional_iff.mpr (closedSourceExpressionEvaluates_conditional_iff.mp independent)
private def law {source} (p : OriginalConditional source) (ns : LocalNameTable) (es : C) (st : List V) : IO Unit := do
  for n in [0,1,3,10] do
    let selected := do
      let (.bool c,m) ← evaluateClosedSourceExpression? n owner ns es st p.condition | none
      evaluateClosedSourceExpression? n owner ns es m (if c then p.yes else p.no)
    have equation : evaluateClosedSourceExpression? (n+1) owner ns es st source=selected := by
      rw [p.exactSource]; exact evaluateClosedSourceExpression?_conditional n owner ns es st p.span p.question p.colon p.condition p.yes p.no
    match left : evaluateClosedSourceExpression? (n+1) owner ns es st source, right : selected with
    | some (v,s),some (v',s') => have _ : v=v' ∧ s=s' := Prod.mk.inj (Option.some.inj (left.symm.trans (equation.trans right))); pure ()
    | none,none => pure ()
    | _,_ => throw (IO.userError "original conditional exact executable equation")
private structure Function (source : Syntax.Expr) (ns : LocalNameTable) (es : C) (st : List V) (result : V → V) where
  parameter : Syntax.Identifier
  body : Syntax.Block
  shape : SourceUnaryLambdaShape source parameter body
  named : parameter.value="y"
  evaluated : ∀ a, B owner (("y",Resolved.freshLocalId owner (ns.map Prod.snd))::ns)
    ((Resolved.freshLocalId owner (ns.map Prod.snd),a)::es) st body (result a) st
private def pairLambda (source : Syntax.Expr) (ns : LocalNameTable) (es : C) (st : List V)
    (x : V) (id : Resolved.LocalId) (named : LocalNameTable.Lookup ns "x" id) (found : Resolved.LocalScope.Lookup es id x)
    (different : Resolved.freshLocalId owner (ns.map Prod.snd) ≠ id) (reverse : Bool) : IO (Function source ns es st (pairResult reverse x)) := do
  match shape : source with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred y⟩]⟩ none ⟨_,[⟨_,.returnStmt (some ⟨_,.tuple ⟨_,[⟨_,.identifier l⟩,⟨_,.identifier r⟩]⟩⟩)⟩]⟩⟩ =>
    if valid : y.value="y" ∧ l.value=(if reverse then "y" else "x") ∧ r.value=(if reverse then "x" else "y") then
      return ⟨y,_,by rw [shape]; exact .inferred,valid.1,fun a => by
        cases reverse <;> simp only [pairResult,Bool.false_eq_true,↓reduceIte] at valid ⊢
        · exact .expression (.pair (.reference (valid.2.1 ▸ .tail (by decide) named) (.tail different found)) (.reference (valid.2.2 ▸ .head) .head))
        · exact .expression (.pair (.reference (valid.2.1 ▸ .head) .head) (.reference (valid.2.2 ▸ .tail (by decide) named) (.tail different found)))⟩
    else throw (IO.userError "original ordered x/y pair")
  | _ => throw (IO.userError "original pair lambda")
private def conditionalLambda (source : Syntax.Expr) (s o : V) (b : Bool) (extra : C) (st : List V) :
    IO (Function source pn (pe s o (.bool b) true extra) st (pairResult (!b) s)) := do
  match shape : source with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred y⟩]⟩ none ⟨_,[⟨_,.returnStmt (some nested)⟩]⟩⟩ =>
    if named : y.value="y" then
      let p ← originalConditional nested
      match yes : p.yes, no : p.no with
      | ⟨_,.tuple ⟨_,[⟨_,.identifier x⟩,⟨_,.identifier a⟩]⟩⟩, ⟨_,.tuple ⟨_,[⟨_,.identifier a'⟩,⟨_,.identifier x'⟩]⟩⟩ =>
        if valid : x.value="x" ∧ a.value="y" ∧ a'.value="y" ∧ x'.value="x" then
          match guard : p.condition with
          | ⟨_,.identifier d⟩ =>
            if dname : d.value="d" then
              return ⟨y,_,by rw [shape]; exact .inferred,named,fun v => by
                refine .expression ?_
                apply chosen p b
                · rw [guard,fresh1]
                  exact .reference (dname ▸ .tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
                · cases b <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,↓reduceIte,pairResult,yes,no,fresh1]
                  · exact .pair (.reference (valid.2.2.1 ▸ .head) .head) (.reference (valid.2.2.2 ▸ .tail (by decide) .head) (.tail (by decide) .head))
                  · exact .pair (.reference (valid.1 ▸ .tail (by decide) .head) (.tail (by decide) .head)) (.reference (valid.2.1 ▸ .head) .head)⟩
            else throw (IO.userError "original d guard")
          | _ => throw (IO.userError "original guard reference")
        else throw (IO.userError "original conditional pair order")
      | _,_ => throw (IO.userError "original conditional pairs")
    else throw (IO.userError "original y parameter")
  | _ => throw (IO.userError "original conditional lambda")
private def fr (c b : Bool) (s : V) : V → V := if c then pairResult (!b) s else pairResult true s
private def selectedFunction {source} (p : OriginalConditional source) (s o d : V) (c b : Bool) (extra : C) (st : List V)
    (guardEq : c=true → d=.bool b) : IO (Function (if c then p.yes else p.no) pn (pe s o d c extra) st (fr c b s)) := do
  if h : c=true then
    let f ← conditionalLambda p.yes s o b extra st
    return by simpa only [h,guardEq h,fr,↓reduceIte] using f
  else
    have hfalse : c=false := by cases c <;> simp_all
    let f ← pairLambda p.no pn (pe s o d c extra) st s (sid 32) .head .head (by rw [fresh1]; decide) true
    return by simpa only [hfalse,fr,Bool.false_eq_true,↓reduceIte] using f
private def immediate (c b : Bool) (s o : V) : V := if c then fr c b s (.word (w 0)) else .pair (.word (w 0)) o
private def mainCall {fs s o d c b extra st} (f : Function fs pn (pe s o d c extra) st (fr c b s)) (source : Syntax.Expr) :
    IO (PLift (E owner tn (te fs s o d c extra) st source (immediate c b s o) st)) := do
  match shape : source with
  | ⟨_,.call ⟨_,.group callee⟩ ⟨_,[argument]⟩⟩ =>
    let p ← originalConditional callee; let q ← originalConditional argument
    let g ← ref owner tn (te fs s o d c extra) st p.condition "c" (sid 3) (.bool c)
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))))))
    let h ← ref owner tn (te fs s o d c extra) st q.condition "c" (sid 3) (.bool c)
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))))))
    if yes : c=true then
      let head ← ref owner tn (te fs s o d c extra) st p.yes "f" (sid 33) (fv fs s o d c extra) (.tail (by decide) .head) (.tail (by decide) .head)
      let arg ← ref owner tn (te fs s o d c extra) st q.yes "x" (sid 34) (.word (w 0)) .head .head
      return ⟨by
        subst c; rw [shape]; simp only [immediate,↓reduceIte]; exact .call f.shape
          (.group (chosen p true g.down (by simpa only [↓reduceIte,fv] using head.down)))
          (chosen q true h.down (by simpa only [↓reduceIte] using arg.down))
          (by simpa only [f.named] using f.evaluated (.word (w 0)))⟩
    else
      have no : c=false := by cases c <;> simp_all
      let post ← pairLambda p.no tn (te fs s o d c extra) st (.word (w 0)) (sid 34) .head .head (by rw [fresh3]; decide) false
      let arg ← ref owner tn (te fs s o d c extra) st q.no "other" (sid 8) o
        (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
      return ⟨by
        subst c; rw [shape]; simp only [immediate,Bool.false_eq_true,↓reduceIte]; exact .call post.shape
          (.group (chosen p false g.down (by simpa only [Bool.false_eq_true,↓reduceIte] using (show E owner tn (te fs s o d false extra) st p.no (.sourceClosure p.no owner tn (te fs s o d false extra)) st from .creation post.shape))))
          (chosen q false h.down (by simpa only [Bool.false_eq_true,↓reduceIte] using arg.down))
          (by simpa only [post.named,pairResult,Bool.false_eq_true,↓reduceIte] using post.evaluated o)⟩
  | _ => throw (IO.userError "original conditional callee/argument")
private structure Witness (source : Syntax.Expr) (s o d : V) (c b : Bool) (extra : C) (st : List V) where
  fs : Syntax.Expr
  f : Function fs pn (pe s o d c extra) st (fr c b s)
  originalBody : Syntax.Block
  body : B owner pn (pe s o d c extra) st originalBody (.pair (immediate c b s o) (fv fs s o d c extra)) st
  whole : E owner names (rows s o d c extra) st source (.pair (immediate c b s o) (fv fs s o d c extra)) st
private def witness (source : Syntax.Expr) (s o d : V) (c b : Bool) (extra : C) (st : List V)
    (guardEq : c=true → d=.bool b) : IO (Witness source s o d c b extra st) := do
  match original : source with
  | ⟨_,.call ⟨_,.group ⟨_,.lambda _ ⟨_,[⟨_,.typed none parameter _⟩]⟩ _ body⟩⟩ ⟨_,[argument]⟩⟩ =>
    match prefixShape : body with
    | ⟨span,[⟨_,.letDecl n none (some initial)⟩,⟨ls,.letDecl x (some annotation) (some ⟨ws,.literal ⟨litSpan,.decimal "0"⟩⟩)⟩,⟨rs,.returnStmt (some ⟨ts,.tuple ⟨ps,[called,returned]⟩⟩)⟩]⟩ =>
      if valid : parameter.value="x" ∧ n.value="f" ∧ x.value="x" then
        let p ← originalConditional initial; let fs := if c then p.yes else p.no
        let f ← selectedFunction p s o d c b extra st guardEq
        let g ← ref owner pn (pe s o d c extra) st p.condition "c" (sid 3) (.bool c)
          (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))))
        let call ← mainCall f called
        let ret ← ref owner tn (te fs s o d c extra) st returned "f" (sid 33) (fv fs s o d c extra) (.tail (by decide) .head) (.tail (by decide) .head)
        let a ← ref owner names (rows s o d c extra) st argument "saved" (sid 7) s .head (.tail (by decide) .head)
        have ending : B owner tn (te fs s o d c extra) st ⟨span,[⟨rs,.returnStmt (some ⟨ts,.tuple ⟨ps,[called,returned]⟩⟩)⟩]⟩ (.pair (immediate c b s o) (fv fs s o d c extra)) st := .expression (.pair call.down ret.down)
        have zero : WordLiteralDenotes ⟨litSpan,.decimal "0"⟩ (w 0) := .decimal (by decide) (.cons (.decimal (digit:=0) (by decide) rfl) .nil)
        have typed : B owner fn ((sid 33,fv fs s o d c extra)::pe s o d c extra) st
            ⟨span,[⟨ls,.letDecl x (some annotation) (some ⟨ws,.literal ⟨litSpan,.decimal "0"⟩⟩)⟩,⟨rs,.returnStmt (some ⟨ts,.tuple ⟨ps,[called,returned]⟩⟩)⟩]⟩ (.pair (immediate c b s o) (fv fs s o d c extra)) st :=
          .binding (.wordLiteral zero) (by simpa only [valid.2.2,fresh2,tn,te] using ending)
        have bodyProof : B owner pn (pe s o d c extra) st body (.pair (immediate c b s o) (fv fs s o d c extra)) st := by
          rw [prefixShape]; exact .inferred (chosen p c g.down (.creation f.shape)) (by simpa only [valid.2.1,fresh1,fn,fv] using typed)
        return ⟨fs,f,body,bodyProof,by rw [original]; exact .call SourceUnaryLambdaShape.typed (.group (.creation SourceUnaryLambdaShape.typed)) a.down (by simpa only [valid.1,fresh0,pn,pe] using bodyProof)⟩
      else throw (IO.userError "original x/f/shadow binders")
    | _ => throw (IO.userError "original initializer/shadow/return")
  | _ => throw (IO.userError "original grouped typed call")
private def caller := {owner with declarationIndex:=160}
private def rid (n : Nat) : Resolved.LocalId := ⟨caller,n⟩
private def callNames : LocalNameTable := [("picked",rid 0),("other",rid 1)]
private def reapplied {fs ns es st result} (f : Function fs ns es st result) (source : Syntax.Expr) (o : V) :
    IO (PLift (E caller callNames [(rid 0,.sourceClosure fs owner ns es),(rid 1,o)] st source (result o) st)) := do
  match shape : source with
  | ⟨_,.call callee ⟨_,[argument]⟩⟩ =>
    let a ← ref caller callNames [(rid 0,.sourceClosure fs owner ns es),(rid 1,o)] st callee "picked" (rid 0) (.sourceClosure fs owner ns es) .head .head
    let b ← ref caller callNames [(rid 0,.sourceClosure fs owner ns es),(rid 1,o)] st argument "other" (rid 1) o (.tail (by decide) .head) (.tail (by decide) .head)
    return ⟨by rw [shape]; exact .call f.shape a.down b.down (by simpa only [f.named] using f.evaluated o)⟩
  | _ => throw (IO.userError "original different-caller call")
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"closed-source-conditionals.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next => check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && source.span==Syntax.SourceSpan.fullFile file) "complete original AST/span"; return source
  | _ => throw (IO.userError "original parser")
private def run {source s o d c b extra st} (proof : Witness source s o d c b extra st) (picked : Syntax.Expr) : IO Unit := do
  let next ← reapplied proof.f picked o
  have _ := evaluateClosedSourceExpression?_eventually_complete proof.whole
  have _ := evaluateClosedSourceBody?_eventually_complete proof.body
  have _ := evaluateClosedSourceExpression?_eventually_complete next.down
  let depth := if c then 10 else 9
  match proof.originalBody.value with
  | [⟨_,.letDecl _ _ (some initial)⟩,_,⟨_,.returnStmt (some ⟨_,.tuple ⟨_,[⟨_,.call ⟨_,.group callee⟩ ⟨_,[argument]⟩⟩,_]⟩⟩)⟩] =>
    let p ← originalConditional initial
    law p pn (pe s o d c extra) st
    law (← originalConditional callee) tn (te proof.fs s o d c extra) st
    law (← originalConditional argument) tn (te proof.fs s o d c extra) st
    match p.yes.value with
    | .lambda _ _ _ ⟨_,[⟨_,.returnStmt (some nested)⟩]⟩ => law (← originalConditional nested) (("y",sid 33)::pn) ((sid 33,.word (w 0))::pe s o d c extra) st
    | _ => throw (IO.userError "original nested conditional law")
  | _ => throw (IO.userError "original conditional law positions")
  for budget in List.range (depth+3) do
    match actual : evaluateClosedSourceExpression? budget owner names (rows s o d c extra) st source with
    | none => check (budget<depth) "expression below threshold; None is not a fault"
    | some (value,final) =>
      match actualShape : value with
      | .pair (.pair _ _) (.sourceClosure fs own ns es) =>
        check (depth≤budget && fs==proof.fs && own==owner && ns==pn && es.map Prod.fst==(pe s o d c extra).map Prod.fst && final.length==st.length) "actual returned original closure and raw store"
        have same := (evaluateClosedSourceExpression?_sound actual).deterministic proof.whole
        have saved : RuntimeValue.sourceClosure fs own ns es=fv proof.fs s o d c extra := by rw [actualShape] at same; exact (RuntimeValue.pair.inj same.1).2
        have independent : E caller callNames [(rid 0,.sourceClosure fs own ns es),(rid 1,o)] final picked (fr c b s o) final := by simpa only [saved,same.2,fv] using next.down
        for more in List.range 8 do
          match computed : evaluateClosedSourceExpression? more caller callNames [(rid 0,.sourceClosure fs own ns es),(rid 1,o)] final picked with
          | none => check (more<(if c then 5 else 4)) "returned closure below threshold"
          | some (v,store) => check ((if c then 5 else 4)≤more && store.length==final.length && (match v with | .pair _ _ => true | _ => false)) "actual reapplied mixed pair"; have _ := (evaluateClosedSourceExpression?_sound computed).deterministic independent; pure ()
      | _ => throw (IO.userError "actual result pair and returned source closure")
    match actual : evaluateClosedSourceBody? budget owner pn (pe s o d c extra) st proof.originalBody with
    | none => check (budget+1<depth) "body below threshold"
    | some (value,store) => check (depth≤budget+1) "body threshold"; have _ := (evaluateClosedSourceBody?_sound actual).deterministic proof.body; pure ()
private def standalone (source : Syntax.Expr) (s o : V) (c : Bool) (extra : C) (st : List V) : IO Unit := do
  match shape : source with
  | ⟨_,.call ⟨_,.group callee⟩ ⟨_,[argument]⟩⟩ =>
    let p ← originalConditional callee; let fs := if c then p.yes else p.no
    match original : fs with
    | ⟨_,.lambda _ ⟨_,[⟨_,.inferred y⟩]⟩ none ⟨_,[⟨_,.returnStmt (some ⟨_,.identifier r⟩)⟩]⟩⟩ =>
      if valid : y.value="y" ∧ r.value="y" then
        let g ← ref owner names (rows s o .unit c extra) st p.condition "c" (sid 3) (.bool c) (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
        let a ← ref owner names (rows s o .unit c extra) st argument "saved" (sid 7) s .head (.tail (by decide) .head)
        have lambda : SourceUnaryLambdaShape fs y _ := by rw [original]; exact .inferred
        have independent : E owner names (rows s o .unit c extra) st source s st := by
          rw [shape]; exact .call lambda (.group (chosen p c g.down (.creation lambda))) a.down (.expression (.reference (by rw [valid.1,valid.2]; exact .head) .head))
        have _ := evaluateClosedSourceExpression?_eventually_complete independent
        law p names (rows s o .unit c extra) st
        for n in List.range 7 do
          match actual : evaluateClosedSourceExpression? n owner names (rows s o .unit c extra) st source with
          | none => check (n<4) "identity selected closure depth"
          | some (v,store) => check (4≤n) "identity actual threshold"; have _ := (evaluateClosedSourceExpression?_sound actual).deterministic independent; pure ()
        check ((evaluateClosedSourceExpression? 40 owner names (rows s o .unit (!c) extra) st source).isNone) "selected missing zero-arity branch is unsupported"
      else throw (IO.userError "original identity references")
    | _ => throw (IO.userError "original selected identity lambda")
  | _ => throw (IO.userError "original standalone call")
end ParsedClosedSourceConditionals
open ParsedClosedSourceConditionals Solcore.Frontend in
/-- Parsed conditional selection preserves original captures and actual mixed endpoints. -/
def frontendParsedClosedSourceConditionalTests : IO Unit := do
  let source ← parsed mainText; let picked ← parsed "picked(other)"
  let yes ← parsed yesText; let no ← parsed noText; let inert ← parsed "lam(){return absent;}"
  let s := RuntimeValue.sourceClosure inert caller [("unseen",foreign)] [(sid 32,.bool false)]
  for o in [.hostFunction .storageWrite,.coreClosure .unit .word (.var 99) [s,.cellRef .word 700]] do
    for extra in [[],[(sid 32,o),(foreign,s)]] do
      for store in [[.unit],[s,.cellRef (.function .word .word) 1]] do
        for b in [true,false] do
          run (← witness source s o (.bool b) true b extra store (by intro _; rfl)) picked
          run (← witness source s o (.bool b) false b extra store (by simp)) picked
        run (← witness source s o o false true extra store (by simp)) picked
        check ((evaluateClosedSourceExpression? 40 owner names (rows s o o true extra) store source).isNone) "visited non-Bool d has no supported success"
        check ((evaluateClosedSourceExpression? 40 owner names ((sid 3,o)::rows s o .unit true extra) store source).isNone) "non-Bool c has no supported success"
        standalone yes s o true extra store; standalone no s o false extra store
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedClosedSourceCoreImage
/- Original gate and two independent derivations precede semantic search.
Actual mixed endpoints enter each iff unchanged; all existential elimination stays in Prop. -/
set_option autoImplicit false
namespace Tests.ParsedClosedSourceCoreImage
open Solcore Solcore.Frontend
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ClosedSourceCoreImage",by decide⟩],by decide⟩⟩,171⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=900},700⟩
private def names : LocalNameTable := [("x",sid 7),("c",sid 3),("y",sid 8),("z",foreign),("x",sid 9)]
private def env (c : Core.Value) (x y z shadow : Core.Value) (extra : Resolved.Environment) :=
  [(sid 8,y),(sid 7,x),(sid 3,c),(foreign,z),(sid 7,shadow)] ++ extra
private def up (environment : Resolved.Environment) := environment.map (fun e => (e.1,RuntimeValue.ofCore e.2))
private def seven : Core.Word := ⟨7,by decide⟩
private def result (x y z : Core.Value) := Core.Value.pair x (.pair .unit (.pair (.word seven) (.pair y z)))
private structure Cert (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Expr) (value : Core.Value) (cost : Nat) : Type where
  fragment : ClosedSourceDataExpression source
  closed : ClosedSourceExpressionEvaluates owner table (up environment) (store.map RuntimeValue.ofCore)
    source (RuntimeValue.ofCore value) (store.map RuntimeValue.ofCore)
  old : LocalExpressionEvaluatesWithCost table environment store source value store cost
private theorem mapped {environment : Resolved.Environment} {id : Resolved.LocalId} {value : Core.Value}
    (h : Resolved.LocalScope.Lookup environment id value) :
    Resolved.LocalScope.Lookup (up environment) id (RuntimeValue.ofCore value) := by
  induction h with
  | head => exact .head
  | tail different _ ih => exact .tail different ih
private def reference (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) (spelling : String) (id : Resolved.LocalId) (value : Core.Value)
    (named : LocalNameTable.Lookup table spelling id) (found : Resolved.LocalScope.Lookup environment id value) :
    IO (Cert table environment store source value 1) := do
  match shape : source with
  | ⟨_,.identifier name⟩ =>
    if h : name.value=spelling then
      have n : LocalNameTable.Lookup table name.value id := h ▸ named
      return by rw [shape]; exact ⟨.reference,.reference n (mapped found),.identifier n found⟩
    else throw (IO.userError "original reference spelling")
  | _ => throw (IO.userError "original reference")
private def lastZ (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) (z : Core.Value) (grouped : Bool)
    (named : LocalNameTable.Lookup table "z" foreign) (found : Resolved.LocalScope.Lookup environment foreign z) :
    IO (Cert table environment store source z 1) := do
  if grouped then
    match shape : source with
    | ⟨span,.group child⟩ =>
      check (span.startByte==13 && span.endByte==16) "original grouped z range"
      let h ← reference table environment store child "z" foreign z named found
      return by rw [shape]; exact ⟨.group h.fragment,.group h.closed,.group h.old⟩
    | _ => throw (IO.userError "original group")
  else reference table environment store source "z" foreign z named found
private def branch (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) (a b : String) (i j : Resolved.LocalId) (x y z : Core.Value) (grouped : Bool)
    (nx : LocalNameTable.Lookup table a i) (ny : LocalNameTable.Lookup table b j)
    (nz : LocalNameTable.Lookup table "z" foreign) (fx : Resolved.LocalScope.Lookup environment i x)
    (fy : Resolved.LocalScope.Lookup environment j y) (fz : Resolved.LocalScope.Lookup environment foreign z) :
    IO (Cert table environment store source (result x y z) 17) := do
  match shape : source with
  | ⟨span,.tuple ⟨ts,[first,⟨_,.tuple ⟨_,[]⟩⟩,⟨_,.literal ⟨litSpan,.decimal spelling⟩⟩,⟨_,.tuple ⟨_,[second,last]⟩⟩]⟩⟩ =>
    check (span==ts) "original tuple span"
    if h : spelling="7" then
      let hx ← reference table environment store first a i x nx fx
      let hy ← reference table environment store second b j y ny fy
      let hz ← lastZ table environment store last z grouped nz fz
      have meaning : WordLiteralDenotes ⟨litSpan,.decimal spelling⟩ seven := by
        subst spelling
        exact .decimal (by decide) (.cons (.decimal (digit := 7) (by decide) (by decide)) .nil)
      return by
        rw [shape]; refine ⟨.many hx.fragment (.many .unit (.pair .literal (.pair hy.fragment hz.fragment))), ?_,
          .many hx.old (.many .unit (.pair (.wordLiteral meaning) (.pair hy.old hz.old)))⟩
        simp only [result,RuntimeValue.ofCore]
        exact .many hx.closed (.many .unit (.pair (.wordLiteral meaning) (.pair hy.closed hz.closed)))
    else throw (IO.userError "original decimal seven")
  | _ => throw (IO.userError "original four-tuple")
private def witness (source : Syntax.Expr) (c : Bool) (x y z shadow : Core.Value)
    (extra : Resolved.Environment) (store : Core.Store) :
    IO (Cert names (env (.bool c) x y z shadow extra) store source
      (if c then result x y z else result y x z) 20) := do
  let e := env (.bool c) x y z shadow extra
  have nx : LocalNameTable.Lookup names "x" (sid 7) := .head
  have nc : LocalNameTable.Lookup names "c" (sid 3) := .tail (by decide) .head
  have ny : LocalNameTable.Lookup names "y" (sid 8) := .tail (by decide) (.tail (by decide) .head)
  have nz : LocalNameTable.Lookup names "z" foreign := .tail (by decide) (.tail (by decide) (.tail (by decide) .head))
  have fx : Resolved.LocalScope.Lookup e (sid 7) x := .tail (by decide) .head
  have fc : Resolved.LocalScope.Lookup e (sid 3) (.bool c) := .tail (by decide) (.tail (by decide) .head)
  have fy : Resolved.LocalScope.Lookup e (sid 8) y := .head
  have fz : Resolved.LocalScope.Lookup e foreign z := .tail (by decide) (.tail (by decide) (.tail (by decide) .head))
  match shape : source with
  | ⟨span,.conditional guard q yes colon no⟩ =>
    check (span.startByte==0 && span.endByte==33 && q.startByte==1 && q.endByte==2 && colon.startByte==18 && colon.endByte==19 && yes.span.startByte==2 && yes.span.endByte==18 && no.span.startByte==19 && no.span.endByte==33) "original conditional ranges"
    let hc ← reference names e store guard "c" (sid 3) (.bool c) nc fc
    let ht ← branch names e store yes "x" "y" (sid 7) (sid 8) x y z true nx ny nz fx fy fz
    let hf ← branch names e store no "y" "x" (sid 8) (sid 7) y x z false ny nx nz fy fx fz
    return by
      rw [shape]; refine ⟨.conditional hc.fragment ht.fragment hf.fragment, ?_, ?_⟩
      · cases c <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · exact .conditionalFalse (by simpa only [RuntimeValue.ofCore] using hc.closed) hf.closed
        · exact .conditionalTrue (by simpa only [RuntimeValue.ofCore] using hc.closed) ht.closed
      · cases c <;> first | exact .ifTrue hc.old ht.old | exact .ifFalse hc.old hf.old
  | _ => throw (IO.userError "original conditional")
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"closed-source-core-image.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && source.span==Syntax.SourceSpan.fullFile file) "complete original AST/span"
    return source
  | _ => throw (IO.userError "original parser")
-- Context identity order is exact; the opaque runtime payloads are deliberately not assumed typed.
private def context (e : Resolved.Environment) (bad : Bool := false) : Resolved.Context :=
  e.map (fun row => (row.1,if row.1=sid 3 then .bool else if bad && row.1==sid 8 then .word else .unit))
private def coreChecks (table : LocalNameTable) (e : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) (actual : Core.Value) (cost : Nat) (mv : RuntimeValue) (ms : List RuntimeValue)
    (g : ClosedSourceDataExpression source)
    (closed : ClosedSourceExpressionEvaluates owner table (up e) (store.map RuntimeValue.ofCore) source mv ms)
    (old : LocalExpressionEvaluatesWithCost table e store source actual store cost) : IO Unit := do
  match resolvedResult : resolveLocalExpression? table source with
  | none => throw (IO.userError "whole resolution")
  | some resolved =>
    let resolution := resolveLocalExpression?_sound resolvedResult
    match lowerResult : resolved.lower? (Resolved.LocalScope.ids e) with
    | none => throw (IO.userError "whole lowering at runtime IDs")
    | some loweredCore =>
      let lowered := Resolved.Expr.lower?_sound lowerResult
      have image := (g.core_evaluates_iff resolution lowered).mp closed
      proof image
      match accepted : elaborateLocalExpression? table (context e) source with
      | none => throw (IO.userError "whole checker")
      | some (core,ty) =>
        have sameIds : Resolved.LocalScope.ids e = Resolved.LocalScope.ids (context e) := by
          simp only [Resolved.LocalScope.ids,context,List.map_map,Function.comp_def]
        have sameCore : loweredCore=core := by
          obtain ⟨r,rr,ll,_⟩ := elaborateLocalExpression?_sound accepted
          cases resolution.deterministic rr
          exact lowered.deterministic (sameIds ▸ ll)
        check (core==loweredCore && ty==.product .unit (.product .unit (.product .word (.product .unit .unit)))) "actual checked and lowered Core/type"
        let actualLowered : Resolved.Lowers (Resolved.LocalScope.ids e) resolved core := sameCore ▸ lowered
        for fuel in [0,cost-1,cost,cost+1] do
          match ran : Core.runStateful fuel (Core.State.initial core (Resolved.LocalScope.values e) store) with
          | .done value finalStore =>
            let actualCore := Core.runStateful_evaluation_sound ran
            let actualOld := (elaborateLocalExpression?_run_done_sound accepted sameIds ran).1
            proof (actualOld.deterministic old.erase)
            proof (show ClosedSourceExpressionEvaluates owner table (up e) (store.map RuntimeValue.ofCore) source mv ms from by
              obtain ⟨v,s,hv,hs,ev⟩ := image
              have same := ((resolution.core_evaluates_iff lowered).mpr ev).deterministic actualOld
              exact (g.core_evaluates_iff resolution actualLowered).mpr
                ⟨value,finalStore,hv.trans (congrArg _ same.1),hs.trans (congrArg _ same.2),actualCore⟩)
            proof ((old.runStateful_done_iff (fuel := fuel) resolution actualLowered).mp (by
              have ⟨vv,ss⟩ := actualOld.deterministic old.erase
              simpa only [vv,ss] using ran))
            check (value==actual && finalStore==store && cost<=fuel) "actual Core full payload/store/cost"
          | .outOfFuel suspended =>
            proof ((old.runStateful_outOfFuel_iff resolution actualLowered).mp ⟨suspended,ran⟩)
            check (fuel<cost) "Core exact exhaustion"
          | .fault _ _ => throw (IO.userError "unexpected Core fault")
private def runSuccessful (table : LocalNameTable) (e : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) (expected : Core.Value) (expectedCost threshold : Nat)
    (h : Cert table e store source expected expectedCost) (withCore : Bool) : IO Unit := do
  match oldResult : evaluateLocalExpressionWithCost? table e source with
  | none => throw (IO.userError "independent old success")
  | some (actual,cost) =>
    let old := evaluateLocalExpressionWithCost?_sound oldResult store
    proof (old.deterministic h.old)
    check (actual==expected && cost==expectedCost) "actual complete old payload and cost"
    for depth in [0,threshold-1,threshold,threshold+1] do
      match actualResult : evaluateClosedSourceExpression? depth owner table (up e) (store.map RuntimeValue.ofCore) source with
      | none => check (depth < threshold) "actual missing below depth threshold"
      | some (actualValue,actualFinal) =>
        check (depth >= threshold) "actual success at depth threshold"
        if withCore then
          match actualValue with
          | .pair _ (.pair .unit (.pair (.word w) (.pair _ _))) => check (w==seven) "actual nested full-result shape"
          | _ => throw (IO.userError "actual mixed result shape")
        let closed := evaluateClosedSourceExpression?_sound actualResult
        have reflected := h.fragment.local_evaluates_iff.mp closed
        have allOutputs : actualValue=RuntimeValue.ofCore actual ∧ actualFinal=store.map RuntimeValue.ofCore := by
          obtain ⟨v,s,hv,hs,ev⟩ := reflected
          obtain ⟨rfl,rfl⟩ := ev.deterministic old.erase
          exact ⟨hv,hs⟩
        proof ((h.fragment.local_evaluates_iff (owner := owner)).mpr ⟨actual,store,allOutputs.1,allOutputs.2,old.erase⟩)
        proof (closed.deterministic h.closed)
        if withCore then coreChecks table e store source actual cost actualValue actualFinal h.fragment closed old
        check (actualValue.toCore?==some actual && actualFinal.mapM RuntimeValue.toCore?==some store)
          "actual full mixed payload and whole store after image reflection"
private def boundaryWitness (source : Syntax.Expr) (x y z : Core.Value) (store : Core.Store) (mappedName : Bool) :
    IO (Cert (names ++ if mappedName then [("missing",sid 99)] else [])
      (env (.bool true) x y z .unit []) store source x 4) := do
  let table := names ++ if mappedName then [("missing",sid 99)] else []
  let e := env (.bool true) x y z .unit []
  match shape : source with
  | ⟨span,.conditional guard q yes colon ⟨_,.identifier missing⟩⟩ =>
    check (span.endByte==11 && q.startByte==1 && q.endByte==2 && colon.startByte==3 && colon.endByte==4 && missing.value=="missing") "original missing boundary"
    let hc ← reference table e store guard "c" (sid 3) (.bool true)
      (.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head))
    let hx ← reference table e store yes "x" (sid 7) x .head (.tail (by decide) .head)
    return by
      rw [shape]; exact ⟨.conditional hc.fragment hx.fragment .reference,
        .conditionalTrue (by simpa only [RuntimeValue.ofCore] using hc.closed) hx.closed,.ifTrue hc.old hx.old⟩
  | _ => throw (IO.userError "original missing conditional")
private def boundaryChecks (source : Syntax.Expr) (x y z : Core.Value) (store : Core.Store) : IO Unit := do
  for mappedName in [false,true] do
    let table := names ++ if mappedName then [("missing",sid 99)] else []
    let e := env (.bool true) x y z .unit []
    let h ← boundaryWitness source x y z store mappedName
    runSuccessful table e store source x 4 2 h false
    check ((elaborateLocalExpression? table (context e) source).isNone) "whole checker cannot skip missing"
    match resolveLocalExpression? table source with
    | none => check (!mappedName) "whole resolution failure despite selected success"
    | some r => check (mappedName && r==.ifE (.var (sid 3)) (.var (sid 7)) (.var (sid 99)) &&
        (r.lower? (Resolved.LocalScope.ids e)).isNone) "resolved unselected ID prevents whole lowering"
    let visited := env (.bool false) x y z .unit []
    check ((evaluateLocalExpressionWithCost? table visited source).isNone &&
      (evaluateClosedSourceExpression? 40 owner table (up visited) (store.map RuntimeValue.ofCore) source).isNone) "visited missing is actual None, not a fault claim"
end ParsedClosedSourceCoreImage
open Solcore Solcore.Frontend ParsedClosedSourceCoreImage
def frontendParsedClosedSourceCoreImageTests : IO Unit := do
  let source ← parsed "c?(x,(),7,(y,(z))):(y,(),7,(x,z))"
  let x : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .unit 700]
  let y : Core.Value := .hostFunction .storageWrite
  let z : Core.Value := .cellRef (.function .word .word) 700
  for c in [true,false] do
    for extra in [[],[(sid 7,z),(foreign,x)]] do
      for store in [[],[x,.cellRef (.function .unit .word) 1]] do
        let h ← witness source c x y z (.word seven) extra store
        let e := env (.bool c) x y z (.word seven) extra
        runSuccessful names e store source (if c then result x y z else result y x z) 20 (if c then 7 else 6) h true
        check ((elaborateLocalExpression? names (context e true) source).isNone) "raw success does not make both branches equally typed"
  let badGuard := env (.word seven) x y z .unit []
  check ((evaluateLocalExpressionWithCost? names badGuard source).isNone &&
    (evaluateClosedSourceExpression? 40 owner names (up badGuard) [] source).isNone) "non-Bool guard actual None"
  let boundary ← parsed "c?x:missing"
  boundaryChecks boundary x y z [x,z]
  IO.println "ADR0293 parsed actual-output raw/Core image, independent depth/cost, and whole-pipeline boundaries GREEN"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedClosedSourceDepth
/- Independent original certificates precede search; actual returned closures and
stores are reused under a different caller. None is not a runtime fault. -/
set_option autoImplicit false
namespace Tests
namespace ParsedClosedSourceDepth
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev C := Resolved.LocalScope V
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def check (b : Bool) (label : String) : IO Unit := unless b do throw (IO.userError label)
private def mainText := "(lam(x:Unknown)->Unknown{let f=c?lam(y){return d?(x,y):(y,x);}:lam(y){return (y,x);};let x:Missing=0;return f;})(saved)"
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ClosedSourceDepth",by decide⟩],by decide⟩⟩,161⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=900},700⟩
private def w (n : Nat) : Core.Word := ⟨n % Core.wordModulus,Nat.mod_lt _ (by decide)⟩
private def names : LocalNameTable := [("saved",sid 7),("other",sid 8),("c",sid 3),("d",sid 31),("saved",sid 9),("x",foreign)]
private def rows (s o d : V) (c : Bool) (extra : C) : C :=
  [(sid 32,.unit),(sid 7,s),(sid 8,o),(sid 31,d),(sid 7,.bool false),(sid 3,.bool c),(foreign,.unit)]++extra
private def pn := ("x",sid 32)::names
private def pe (s o d : V) (c : Bool) (extra : C) := (sid 32,s)::rows s o d c extra
private def fn := ("f",sid 33)::pn
private def fv (fs : Syntax.Expr) (s o d : V) (c : Bool) (extra : C) : V := .sourceClosure fs owner pn (pe s o d c extra)
private def tn := ("x",sid 34)::fn
private def te (fs : Syntax.Expr) (s o d : V) (c : Bool) (extra : C) := (sid 34,RuntimeValue.word (w 0))::(sid 33,fv fs s o d c extra)::pe s o d c extra
private theorem fresh0 : Resolved.freshLocalId owner (names.map Prod.snd)=sid 32 := by decide
private theorem fresh1 : Resolved.freshLocalId owner (pn.map Prod.snd)=sid 33 := by decide
private theorem fresh2 : Resolved.freshLocalId owner (fn.map Prod.snd)=sid 34 := by decide
private def pairResult (reverse : Bool) (x a : V) : V := if reverse then .pair a x else .pair x a
private def ref (own : Resolved.DeclarationId) (ns : LocalNameTable) (es : C) (st : List V) (e : Syntax.Expr)
    (name : String) (id : Resolved.LocalId) (value : V) (named : LocalNameTable.Lookup ns name id) (found : Resolved.LocalScope.Lookup es id value) : IO (PLift (E own ns es st e value st)) := do
  match shape : e with
  | ⟨_,.identifier n⟩ => if same : n.value=name then return ⟨by rw [shape]; exact .reference (same ▸ named) found⟩ else throw (IO.userError "original reference name")
  | _ => throw (IO.userError "original reference")
private structure OriginalConditional (source : Syntax.Expr) where
  span : Syntax.SourceSpan
  condition : Syntax.Expr
  question : Syntax.SourceSpan
  yes : Syntax.Expr
  colon : Syntax.SourceSpan
  no : Syntax.Expr
  exactSource : source=⟨span,.conditional condition question yes colon no⟩
private def originalConditional : (source : Syntax.Expr) → IO (OriginalConditional source)
  | ⟨s,.conditional c q y colon n⟩ => do
    check ([(31,84,32,62),(47,60,48,54)].contains (s.startByte,s.endByte,q.startByte,colon.startByte) && mainText.toUTF8[q.startByte]? == some 63 && mainText.toUTF8[colon.startByte]? == some 58) "literal original ranges and punctuation bytes"
    check (s.contains c.span && s.contains y.span && s.contains n.span && c.span.endByte≤q.startByte &&
      q.length==1 && q.endByte≤y.span.startByte && y.span.endByte≤colon.startByte && colon.length==1 && colon.endByte≤n.span.startByte) "original ?: spans and order"
    pure ⟨s,c,q,y,colon,n,rfl⟩
  | _ => throw (IO.userError "original conditional")
private theorem chosen {source own ns es st value} (p : OriginalConditional source) (c : Bool)
    (guard : E own ns es st p.condition (.bool c) st)
    (branch : E own ns es st (if c then p.yes else p.no) value st) : E own ns es st source value st := by
  rw [p.exactSource]
  have independent : E own ns es st ⟨p.span,.conditional p.condition p.question p.yes p.colon p.no⟩ value st := by
    cases c <;> first | exact .conditionalFalse guard branch | exact .conditionalTrue guard branch
  exact closedSourceExpressionEvaluates_conditional_iff.mpr (closedSourceExpressionEvaluates_conditional_iff.mp independent)
private structure Function (source : Syntax.Expr) (ns : LocalNameTable) (es : C) (st : List V) (result : V → V) where
  parameter : Syntax.Identifier
  body : Syntax.Block
  shape : SourceUnaryLambdaShape source parameter body
  named : parameter.value="y"
  evaluated : ∀ a, B owner (("y",Resolved.freshLocalId owner (ns.map Prod.snd))::ns)
    ((Resolved.freshLocalId owner (ns.map Prod.snd),a)::es) st body (result a) st
private def pairLambda (source : Syntax.Expr) (ns : LocalNameTable) (es : C) (st : List V)
    (x : V) (id : Resolved.LocalId) (named : LocalNameTable.Lookup ns "x" id) (found : Resolved.LocalScope.Lookup es id x)
    (different : Resolved.freshLocalId owner (ns.map Prod.snd) ≠ id) (reverse : Bool) : IO (Function source ns es st (pairResult reverse x)) := do
  match shape : source with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred y⟩]⟩ none ⟨_,[⟨_,.returnStmt (some ⟨_,.tuple ⟨_,[⟨_,.identifier l⟩,⟨_,.identifier r⟩]⟩⟩)⟩]⟩⟩ =>
    if valid : y.value="y" ∧ l.value=(if reverse then "y" else "x") ∧ r.value=(if reverse then "x" else "y") then
      return ⟨y,_,by rw [shape]; exact .inferred,valid.1,fun a => by
        cases reverse <;> simp only [pairResult,Bool.false_eq_true,↓reduceIte] at valid ⊢
        · exact .expression (.pair (.reference (valid.2.1 ▸ .tail (by decide) named) (.tail different found)) (.reference (valid.2.2 ▸ .head) .head))
        · exact .expression (.pair (.reference (valid.2.1 ▸ .head) .head) (.reference (valid.2.2 ▸ .tail (by decide) named) (.tail different found)))⟩
    else throw (IO.userError "original ordered x/y pair")
  | _ => throw (IO.userError "original pair lambda")
private def conditionalLambda (source : Syntax.Expr) (s o : V) (b : Bool) (extra : C) (st : List V) :
    IO (Function source pn (pe s o (.bool b) true extra) st (pairResult (!b) s)) := do
  match shape : source with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred y⟩]⟩ none ⟨_,[⟨_,.returnStmt (some nested)⟩]⟩⟩ =>
    if named : y.value="y" then
      let p ← originalConditional nested
      match yes : p.yes, no : p.no with
      | ⟨_,.tuple ⟨_,[⟨_,.identifier x⟩,⟨_,.identifier a⟩]⟩⟩, ⟨_,.tuple ⟨_,[⟨_,.identifier a'⟩,⟨_,.identifier x'⟩]⟩⟩ =>
        if valid : x.value="x" ∧ a.value="y" ∧ a'.value="y" ∧ x'.value="x" then
          match guard : p.condition with
          | ⟨_,.identifier d⟩ =>
            if dname : d.value="d" then
              return ⟨y,_,by rw [shape]; exact .inferred,named,fun v => by
                refine .expression ?_
                apply chosen p b
                · rw [guard,fresh1]
                  exact .reference (dname ▸ .tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
                · cases b <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,↓reduceIte,pairResult,yes,no,fresh1]
                  · exact .pair (.reference (valid.2.2.1 ▸ .head) .head) (.reference (valid.2.2.2 ▸ .tail (by decide) .head) (.tail (by decide) .head))
                  · exact .pair (.reference (valid.1 ▸ .tail (by decide) .head) (.tail (by decide) .head)) (.reference (valid.2.1 ▸ .head) .head)⟩
            else throw (IO.userError "original d guard")
          | _ => throw (IO.userError "original guard reference")
        else throw (IO.userError "original conditional pair order")
      | _,_ => throw (IO.userError "original conditional pairs")
    else throw (IO.userError "original y parameter")
  | _ => throw (IO.userError "original conditional lambda")

private def fr (c b : Bool) (s : V) : V → V := if c then pairResult (!b) s else pairResult true s
private def function (fs : Syntax.Expr) (s o d : V) (c b : Bool) (extra : C) (st : List V)
    (guardEq : c=true → d=.bool b) : IO (Function fs pn (pe s o d c extra) st (fr c b s)) := do
  if h : c=true then
    let f ← conditionalLambda fs s o b extra st
    return by simpa only [h,guardEq h,fr,↓reduceIte] using f
  else
    have hfalse : c=false := by cases c <;> simp_all
    let f ← pairLambda fs pn (pe s o d c extra) st s (sid 32) .head .head (by rw [fresh1]; decide) true
    return by simpa only [hfalse,fr,Bool.false_eq_true,↓reduceIte] using f
private structure Witness (source : Syntax.Expr) (s o d : V) (c : Bool) (extra : C) (st : List V) where
  fs : Syntax.Expr
  originalBody : Syntax.Block
  body : B owner pn (pe s o d c extra) st originalBody (fv fs s o d c extra) st
  whole : E owner names (rows s o d c extra) st source (fv fs s o d c extra) st
private def witness (source : Syntax.Expr) (s o d : V) (c : Bool) (extra : C) (st : List V) : IO (Witness source s o d c extra st) := do
  match original : source with
  | ⟨_,.call ⟨_,.group ⟨_,.lambda _ ⟨_,[⟨_,.typed none parameter _⟩]⟩ _ body⟩⟩ ⟨_,[argument]⟩⟩ =>
    match prefixShape : body with
    | ⟨span,[⟨_,.letDecl n none (some initial)⟩,⟨ls,.letDecl x (some annotation) (some ⟨ws,.literal ⟨litSpan,.decimal "0"⟩⟩)⟩,⟨rs,.returnStmt (some returned)⟩]⟩ =>
      if valid : parameter.value="x" ∧ n.value="f" ∧ x.value="x" then
        let p ← originalConditional initial; let fs := if c then p.yes else p.no
        match fsShape : fs with
        | ⟨_,.lambda _ ⟨_,[⟨_,.inferred y⟩]⟩ none inner⟩ =>
          have lambda : SourceUnaryLambdaShape fs y inner := by rw [fsShape]; exact .inferred
          let g ← ref owner pn (pe s o d c extra) st p.condition "c" (sid 3) (.bool c)
            (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))))
          let ret ← ref owner tn (te fs s o d c extra) st returned "f" (sid 33) (fv fs s o d c extra) (.tail (by decide) .head) (.tail (by decide) .head)
          let a ← ref owner names (rows s o d c extra) st argument "saved" (sid 7) s .head (.tail (by decide) .head)
          have zero : WordLiteralDenotes ⟨litSpan,.decimal "0"⟩ (w 0) := .decimal (by decide) (.cons (.decimal (digit:=0) (by decide) rfl) .nil)
          have typed : B owner fn ((sid 33,fv fs s o d c extra)::pe s o d c extra) st
              ⟨span,[⟨ls,.letDecl x (some annotation) (some ⟨ws,.literal ⟨litSpan,.decimal "0"⟩⟩)⟩,⟨rs,.returnStmt (some returned)⟩]⟩ (fv fs s o d c extra) st :=
            .binding (.wordLiteral zero) (by simpa only [valid.2.2,fresh2,tn,te] using (show B owner tn (te fs s o d c extra) st ⟨span,[⟨rs,.returnStmt (some returned)⟩]⟩ (fv fs s o d c extra) st from .expression ret.down))
          have bodyProof : B owner pn (pe s o d c extra) st body (fv fs s o d c extra) st := by
            rw [prefixShape]; exact .inferred (chosen p c g.down (.creation lambda)) (by simpa only [valid.2.1,fresh1,fn,fv] using typed)
          return ⟨fs,body,bodyProof,by rw [original]; exact .call SourceUnaryLambdaShape.typed (.group (.creation SourceUnaryLambdaShape.typed)) a.down (by simpa only [valid.1,fresh0,pn,pe] using bodyProof)⟩
        | _ => throw (IO.userError "original selected unary source")
      else throw (IO.userError "original x/f/shadow binders")
    | _ => throw (IO.userError "original initializer/shadow/return")
  | _ => throw (IO.userError "original grouped typed call")
private def caller := {owner with declarationIndex:=162}
private def rid (n : Nat) : Resolved.LocalId := ⟨caller,n⟩
private def callNames : LocalNameTable := [("picked",rid 0),("other",rid 1)]
private def reapplied {fs ns es st result} (f : Function fs ns es st result) (source : Syntax.Expr) (o : V) :
    IO (PLift (E caller callNames [(rid 0,.sourceClosure fs owner ns es),(rid 1,o)] st source (result o) st)) := do
  match shape : source with
  | ⟨_,.call callee ⟨_,[argument]⟩⟩ =>
    let a ← ref caller callNames [(rid 0,.sourceClosure fs owner ns es),(rid 1,o)] st callee "picked" (rid 0) (.sourceClosure fs owner ns es) .head .head
    let b ← ref caller callNames [(rid 0,.sourceClosure fs owner ns es),(rid 1,o)] st argument "other" (rid 1) o (.tail (by decide) .head) (.tail (by decide) .head)
    return ⟨by rw [shape]; exact .call f.shape a.down b.down (by simpa only [f.named] using f.evaluated o)⟩
  | _ => throw (IO.userError "original different-caller call")
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"closed-source-depth.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next => check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && source.span==Syntax.SourceSpan.fullFile file) "complete original AST/span"; return source
  | _ => throw (IO.userError "original parser")
/- Adjacent budgets are handwritten constructor heights. The existential cutoff
stays in Prop and never selects an IO budget. -/
private theorem thresholdAt {α : Type} {search : Nat → Option α} {expected actual : α} {n : Nat}
    (low : search n=none) (high : search (n+1)=some actual)
    (threshold : ∃ required : Nat, 0<required ∧ ∀ budget, search budget=if required≤budget then some expected else none) :
    ∃ required : Nat, required=n+1 ∧ 0<required ∧ ∀ budget, search budget=if required≤budget then some expected else none := by
  obtain ⟨required,positive,formula⟩ := threshold
  have below : ¬required≤n := by intro order; have h := formula n; rw [if_pos order,low] at h; cases h
  have above : required≤n+1 := by
    by_cases order : required≤n+1
    · exact order
    · have h := formula (n+1); rw [if_neg order,high] at h; cases h
  exact ⟨required,by omega,positive,formula⟩
private def absent {α : Type} (search : Nat → Option α) (large : Nat)
    (down : ∀ {small large : Nat}, small≤large → search large=none → search small=none) : IO (PLift (search large=none)) := do
  match rejected : search large with
  | some _ => throw (IO.userError "independently chosen insufficient budget unexpectedly succeeds")
  | none =>
    for small in [0,1,large/2,large] do
      if order : small≤large then
        have predicted := down order rejected
        match actual : search small with
        | none => pure ()
        | some _ => have impossible := predicted.symm.trans actual; nomatch impossible
    return ⟨rejected⟩
private def depth {α : Type} {expected : α} (search : Nat → Option α) (n : Nat)
    (stable : ∀ {small large : Nat} {actual : α}, small≤large → search small=some actual → search large=some actual)
    (down : ∀ {small large : Nat}, small≤large → search large=none → search small=none)
    (threshold : ∃ required : Nat, 0<required ∧ ∀ budget, search budget=if required≤budget then some expected else none)
    (inspect : α → IO Unit) : IO {actual : α // search (n+1)=some actual ∧
      ∀ budget, search budget=if n+1≤budget then some expected else none} := do
  match accepted : search (n+1) with
  | none => throw (IO.userError "independently witnessed successful budget absent")
  | some endpoint =>
    inspect endpoint
    for larger in [n+1,n+2,n+5,n+13] do
      if order : n+1≤larger then
        have predicted := stable order accepted
        match actual : search larger with
        | none => have impossible := actual.symm.trans predicted; nomatch impossible
        | some observed => inspect observed; have _ : observed=endpoint := Option.some.inj (actual.symm.trans predicted); pure ()
    let rejected ← absent search n down
    have cutoff := thresholdAt rejected.down accepted threshold
    return ⟨endpoint,accepted,by obtain ⟨required,same,_,formula⟩ := cutoff; simpa only [same] using formula⟩
private def run {source s o d c extra st} (proof : Witness source s o d c extra st) (picked : Syntax.Expr)
    (b canCall : Bool) (guardEq : canCall=true → c=true → d=.bool b) : IO Unit := do
  let next : Option (PLift (E caller callNames [(rid 0,fv proof.fs s o d c extra),(rid 1,o)] st picked (fr c b s o) st)) ←
    if enabled : canCall=true then do
      let f ← function proof.fs s o d c b extra st (guardEq enabled)
      pure (some (← reapplied f picked o))
    else pure none
  let inspect : V × List V → IO Unit := fun (value,final) => match value with
    | .sourceClosure fs own ns es => check (fs==proof.fs && own==owner && ns==pn && es.map Prod.fst==(pe s o d c extra).map Prod.fst && final.length==st.length) "actual returned original closure and raw store"
    | _ => throw (IO.userError "actual returned source closure")
  let actual ← depth (fun n => evaluateClosedSourceExpression? n owner names (rows s o d c extra) st source) 4
    (fun order accepted => evaluateClosedSourceExpression?_monotone order accepted)
    (fun order rejected => evaluateClosedSourceExpression?_none_of_le order rejected)
    (ClosedSourceExpressionEvaluates.exact_depth_threshold proof.whole) inspect
  let final := actual.val.2
  match actualShape : actual.val.1 with
  | .sourceClosure fs own ns es =>
    have same := (evaluateClosedSourceExpression?_sound actual.property.1).deterministic proof.whole
    have saved : RuntimeValue.sourceClosure fs own ns es=fv proof.fs s o d c extra := by rw [actualShape] at same; exact same.1
    match next with
    | some certificate =>
      have independent : E caller callNames [(rid 0,.sourceClosure fs own ns es),(rid 1,o)] final picked (fr c b s o) final := by simpa only [saved,final,same.2] using certificate.down
      let result ← depth (fun n => evaluateClosedSourceExpression? n caller callNames [(rid 0,.sourceClosure fs own ns es),(rid 1,o)] final picked) (if c then 4 else 3)
        (fun order accepted => evaluateClosedSourceExpression?_monotone order accepted)
        (fun order rejected => evaluateClosedSourceExpression?_none_of_le order rejected)
        (ClosedSourceExpressionEvaluates.exact_depth_threshold independent)
        (fun (v,t) => check (t.length==final.length && (match v with | .pair _ _ => true | _ => false)) "actual reapplied mixed pair")
      have _ := (evaluateClosedSourceExpression?_sound result.property.1).deterministic independent
      pure ()
    | none =>
      let _ ← absent (fun n => evaluateClosedSourceExpression? n caller callNames [(rid 0,.sourceClosure fs own ns es),(rid 1,o)] final picked) 40
        (fun order rejected => evaluateClosedSourceExpression?_none_of_le order rejected)
      pure ()
  | _ => throw (IO.userError "actual main returned source closure")
  let body ← depth (fun n => evaluateClosedSourceBody? n owner pn (pe s o d c extra) st proof.originalBody) 3
    (fun order accepted => evaluateClosedSourceBody?_monotone order accepted)
    (fun order rejected => evaluateClosedSourceBody?_none_of_le order rejected)
    (ClosedSourceBodyEvaluates.exact_depth_threshold proof.body) inspect
  have _ := (evaluateClosedSourceBody?_sound body.property.1).deterministic proof.body
  pure ()
end ParsedClosedSourceDepth
open ParsedClosedSourceDepth Solcore.Frontend in
/-- Independent parsed closure endpoints and actual derivation-depth boundaries. -/
def frontendParsedClosedSourceDepthTests : IO Unit := do
  let source ← parsed mainText; let picked ← parsed "picked(other)"; let inert ← parsed "lam(){return absent;}"
  let s := RuntimeValue.sourceClosure inert caller [("unseen",foreign)] [(sid 32,.bool false)]
  for o in [.hostFunction .storageWrite,.coreClosure .unit .word (.var 99) [s,.cellRef .word 700]] do
    for extra in [[],[(sid 32,o),(foreign,s)]] do
      for store in [[.unit],[s,.cellRef (.function .word .word) 1]] do
        for c in [true,false] do
          for b in [true,false] do
            run (← witness source s o (.bool b) c extra store) picked b true (by intro _ _; rfl)
        run (← witness source s o o false extra store) picked true true (by simp)
        run (← witness source s o o true extra store) picked true false (by simp)
        let _ ← absent (fun n => evaluateClosedSourceExpression? n owner names ((sid 3,o)::rows s o .unit true extra) store source) 40
          (fun order rejected => evaluateClosedSourceExpression?_none_of_le order rejected)
        pure ()
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedClosedSourceEvaluation
/- Independent original certificates precede depth search. Actual returned closures
are inspected and identified through soundness, then reapplied at a different owner.
None is not a fault; depth is neither cost nor resumable fuel. -/
set_option autoImplicit false
namespace Tests
namespace ParsedClosedSourceEvaluation
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev C := Resolved.LocalScope V
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def check (b : Bool) (label : String) : IO Unit := unless b do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ClosedSourceRunner",by decide⟩],by decide⟩⟩,157⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=900},700⟩
private def w (n : Nat) : Core.Word := ⟨n % Core.wordModulus,Nat.mod_lt _ (by decide)⟩
private def names : LocalNameTable := [("saved",sid 7),("other",sid 8),("c",sid 3),("tag",sid 31),("saved",sid 9),("x",foreign)]
private def rows (s o tag : V) (c : Bool) (extra : C) : C :=
  [(sid 32,.unit),(sid 7,s),(sid 8,o),(sid 31,tag),(sid 7,.bool false),(sid 3,.bool c),(foreign,.unit)]++extra
private def pn := ("x",sid 32)::names
private def pe (s o tag : V) (c : Bool) (extra : C) := (sid 32,s)::rows s o tag c extra
private def fn := ("f",sid 33)::pn
private def fval (fs : Syntax.Expr) (s o tag : V) (c : Bool) (extra : C) : V := .sourceClosure fs owner pn (pe s o tag c extra)
private def tn := ("x",sid 34)::fn
private def te (fs : Syntax.Expr) (s o tag : V) (c : Bool) (extra : C) := (sid 34,RuntimeValue.word (w 0))::(sid 33,fval fs s o tag c extra)::pe s o tag c extra
private theorem fresh0 : Resolved.freshLocalId owner (names.map Prod.snd)=sid 32 := by decide
private theorem fresh1 : Resolved.freshLocalId owner (pn.map Prod.snd)=sid 33 := by decide
private theorem fresh2 : Resolved.freshLocalId owner (fn.map Prod.snd)=sid 34 := by decide
private def result (fs : Syntax.Expr) (s o tag : V) (c hit : Bool) (extra : C) : V :=
  if c then if hit then .pair (.pair s (.word (w 0))) (.pair (fval fs s o tag c extra) .unit) else .unit else .pair s o
private def ref (own : Resolved.DeclarationId) (ns : LocalNameTable) (es : C) (st : List V) (e : Syntax.Expr)
    (name : String) (id : Resolved.LocalId) (value : V) (named : LocalNameTable.Lookup ns name id) (found : Resolved.LocalScope.Lookup es id value) : IO (PLift (E own ns es st e value st)) := do
  match shape : e with
  | ⟨_,.identifier n⟩ => if same : n.value=name then return ⟨by rw [shape]; exact .reference (same ▸ named) found⟩ else throw (IO.userError "original reference name")
  | _ => throw (IO.userError "original reference")
private def zeroPattern (p : Syntax.Pattern) : IO (PLift (WordMatchPatternClassifies p (some (w 0)))) := do
  match shape : p with
  | ⟨_,.literal ⟨_,.decimal "0"⟩⟩ => return ⟨by rw [shape]; exact .literal ⟨_,rfl,.decimal (by decide) (.cons (.decimal (digit:=0) (by decide) rfl) .nil)⟩⟩
  | ⟨_,.literal ⟨_,.hexadecimal "0x00"⟩⟩ => return ⟨by rw [shape]; exact .literal ⟨_,rfl,.hexadecimal rfl (by decide) (.cons (.decimal (digit:=0) (by decide) rfl) (.cons (.decimal (digit:=0) (by decide) rfl) .nil))⟩⟩
  | _ => throw (IO.userError "original zero pattern")
private def wildcard (p : Syntax.Pattern) : IO (PLift (WordMatchPatternClassifies p none)) := do
  match shape : p with
  | ⟨_,.group ⟨_,.group ⟨_,.wildcard _⟩⟩⟩ => return ⟨by rw [shape]; exact .group (.group (.wildcard rfl))⟩
  | _ => throw (IO.userError "original grouped wildcard")
private def selection {v cases defaultBody selected tests} (proof : RuntimeWordMatchChooses v cases defaultBody selected tests) : IO Unit := do
  have _ := chooseRuntimeWordMatch?_iff.mpr proof
  match actual : chooseRuntimeWordMatch? v cases defaultBody with
  | some (body,count) => check (body == selected && count==tests) "actual selector body/count"; have _ := (chooseRuntimeWordMatch?_iff.mp actual).deterministic proof; pure ()
  | none => throw (IO.userError "independently witnessed selection missing")
private def absentChoice (v : V) (cases : List Syntax.MatchCase) (originalDefault : Option Syntax.Block) : IO Unit := do
  match absent : chooseRuntimeWordMatch? v cases originalDefault with
  | none =>
    have _ : ∀ body count, ¬RuntimeWordMatchChooses v cases originalDefault body count := by
      intro body count choice
      have accepted := chooseRuntimeWordMatch?_iff.mpr choice
      rw [absent] at accepted
      cases accepted
    pure ()
  | some _ => throw (IO.userError "unsupported or literal-first non-Word selection")
private structure Function (s o tag : V) (c : Bool) (extra : C) (st : List V) where
  source : Syntax.Expr
  parameter : Syntax.Identifier
  body : Syntax.Block
  shape : SourceUnaryLambdaShape source parameter body
  named : parameter.value="y"
  pair : ∀ a, B owner (("y",sid 33)::pn) ((sid 33,a)::pe s o tag c extra) st body (.pair s a) st
private def function (fs : Syntax.Expr) (s o tag : V) (c : Bool) (extra : C) (st : List V) : IO {f : Function s o tag c extra st // f.source=fs} := do
  match shape : fs with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred y⟩]⟩ _ ⟨_,[⟨_,.returnStmt (some ⟨_,.tuple ⟨_,[⟨_,.identifier x⟩,⟨_,.identifier arg⟩]⟩⟩)⟩]⟩⟩ =>
    if valid : y.value="y" ∧ x.value="x" ∧ arg.value="y" then
      return ⟨⟨fs,y,_,by rw [shape]; exact .inferred,valid.1,fun a => .expression (.pair
        (.reference (by simpa only [valid.2.1] using
          (show LocalNameTable.Lookup (("y",sid 33)::pn) "x" (sid 32) from .tail (by decide) .head)) (.tail (by decide) .head))
        (.reference (by simpa only [valid.2.2] using
          (show LocalNameTable.Lookup (("y",sid 33)::pn) "y" (sid 33) from .head)) .head))⟩,rfl⟩
    else throw (IO.userError "original captured x/y")
  | _ => throw (IO.userError "original inner pair lambda")
private def applyF {s o tag c extra st} (f : Function s o tag c extra st) (e : Syntax.Expr) (other : Bool) : IO (PLift (E owner tn (te f.source s o tag c extra) st e (.pair s (if other then o else .word (w 0))) st)) := do
  match shape : e with
  | ⟨_,.call callee ⟨_,[argument]⟩⟩ =>
    let head ← ref owner tn (te f.source s o tag c extra) st callee "f" (sid 33) (fval f.source s o tag c extra) (.tail (by decide) .head) (.tail (by decide) .head)
    if h : other=true then
      let a ← ref owner tn (te f.source s o tag c extra) st argument "other" (sid 8) o (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
      return ⟨by rw [shape]; simp only [h,↓reduceIte]; exact .call f.shape head.down a.down (by simpa only [f.named,fresh1] using f.pair o)⟩
    else
      have hfalse : other=false := by cases other <;> simp_all
      let a ← ref owner tn (te f.source s o tag c extra) st argument "x" (sid 34) (.word (w 0)) .head .head
      return ⟨by rw [shape]; simp only [hfalse,Bool.false_eq_true,↓reduceIte]; exact .call f.shape head.down a.down (by simpa only [f.named,fresh1] using f.pair (.word (w 0)))⟩
  | _ => throw (IO.userError "original f call")
private def selected {s o tag c extra st} (f : Function s o tag c extra st) (hit : Bool)
    (tagEq : tag=.word (w (if hit then 0 else 1))) (body : Syntax.Block) :
    IO (PLift (B owner tn (te f.source s o tag c extra) st body
      (if hit then .pair (.pair s (.word (w 0))) (.pair (fval f.source s o tag c extra) .unit) else .unit) st)) := do
  match shape : body with
  | ⟨_,[⟨_,.matchWith ⟨_,⟨scrutinee,[]⟩⟩ ⟨_,⟨[first,duplicate,last],none⟩⟩⟩]⟩ =>
    let r ← ref owner tn (te f.source s o tag c extra) st scrutinee "tag" (sid 31) tag
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))))
    let p ← zeroPattern first.value.pattern; let d ← zeroPattern duplicate.value.pattern; let q ← wildcard last.value.pattern
    if h : hit=true then
      match branch : first.value.body with
      | ⟨_,[⟨_,.returnStmt (some ⟨_,.tuple ⟨_,[call,identifier,⟨_,.tuple ⟨_,[]⟩⟩]⟩⟩)⟩]⟩ =>
        let a ← applyF f call false
        let b ← ref owner tn (te f.source s o tag c extra) st identifier "f" (sid 33) (fval f.source s o tag c extra) (.tail (by decide) .head) (.tail (by decide) .head)
        have choice : RuntimeWordMatchChooses tag [first,duplicate,last] none first.value.body 1 := by rw [tagEq,h]; exact .hit p.down
        selection choice
        return ⟨by rw [shape]; simp only [h,↓reduceIte]; exact .wordMatch r.down choice (by rw [branch]; exact .expression (.many a.down (.pair b.down .unit)))⟩
      | _ => throw (IO.userError "original flat three-tuple")
    else
      have hfalse : hit=false := by cases hit <;> simp_all
      match branch : last.value.body with
      | ⟨_,[⟨_,.returnStmt none⟩]⟩ =>
        have choice : RuntimeWordMatchChooses tag [first,duplicate,last] none last.value.body 2 := by rw [tagEq,hfalse]; exact .miss p.down (by decide) (.miss d.down (by decide) (.wildcard q.down))
        selection choice
        return ⟨by rw [shape]; simp only [hfalse,Bool.false_eq_true,↓reduceIte]; exact .wordMatch r.down choice (by rw [branch]; exact .bare)⟩
      | _ => throw (IO.userError "original bare wildcard body")
  | _ => throw (IO.userError "original three-arm match")
private def ending {s o tag c extra st} (f : Function s o tag c extra st) (hit : Bool) (tagEq : c=true → tag=.word (w (if hit then 0 else 1))) (body : Syntax.Block) : IO (PLift (B owner tn (te f.source s o tag c extra) st body (result f.source s o tag c hit extra) st)) := do
  match shape : body with
  | ⟨_,[⟨_,.ifThen condition thenBody (some elseBody)⟩]⟩ =>
    let r ← ref owner tn (te f.source s o tag c extra) st condition "c" (sid 3) (.bool c)
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))))))
    if h : c=true then
      match block : thenBody with
      | ⟨_,[⟨span,.block statements⟩]⟩ =>
        let a ← selected f hit (tagEq h) ⟨span,statements⟩
        have conditionTrue : E owner tn (te f.source s o tag c extra) st condition (.bool true) st := by simpa only [h] using r.down
        return ⟨by rw [shape]; simp only [result,h,↓reduceIte]; exact .ifTrue (by simpa only [h] using conditionTrue) (by rw [block]; exact .block (by simpa only [h] using a.down))⟩
      | _ => throw (IO.userError "original explicit block")
    else
      have hfalse : c=false := by cases c <;> simp_all
      match branch : elseBody with
      | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ =>
        let a ← applyF f e true
        return ⟨by rw [shape]; simp only [result,hfalse,Bool.false_eq_true,↓reduceIte]; exact .ifFalse (by simpa only [hfalse] using r.down) (by rw [branch]; exact .expression (by simpa only [hfalse,↓reduceIte] using a.down))⟩
      | _ => throw (IO.userError "original else return")
  | _ => throw (IO.userError "original conditional")
private structure Witness (source : Syntax.Expr) (s o tag : V) (c hit : Bool) (extra : C) (st : List V) where
  f : Function s o tag c extra st
  originalBody : Syntax.Block
  body : B owner pn (pe s o tag c extra) st originalBody (result f.source s o tag c hit extra) st
  whole : E owner names (rows s o tag c extra) st source (result f.source s o tag c hit extra) st
private def witness (source : Syntax.Expr) (s o tag : V) (c hit : Bool) (extra : C) (st : List V) (tagEq : c=true → tag=.word (w (if hit then 0 else 1))) : IO (Witness source s o tag c hit extra st) := do
  match original : source with
  | ⟨_,.call ⟨_,.group ⟨_,.lambda _ ⟨_,[⟨_,.typed none parameter _⟩]⟩ _ body⟩⟩ ⟨_,[argument]⟩⟩ =>
    match prefixShape : body with
    | ⟨span,⟨_,.letDecl n none (some fs)⟩::⟨ls,.letDecl x (some annotation) (some ⟨ws,.literal literal⟩)⟩::⟨ds,.expression ⟨us,.tuple ⟨ts,[]⟩⟩ true⟩::rest⟩ =>
      if valid : parameter.value="x" ∧ n.value="f" ∧ x.value="x" then
        match numeric : literal with
        | ⟨_,.decimal "0"⟩ =>
          let ⟨f,fsEq⟩ ← function fs s o tag c extra st; let tail ← ending f hit tagEq ⟨span,rest⟩
          let a ← ref owner names (rows s o tag c extra) st argument "saved" (sid 7) s .head (.tail (by decide) .head)
          have zero : WordLiteralDenotes literal (w 0) := by rw [numeric]; exact .decimal (by decide) (.cons (.decimal (digit:=0) (by decide) rfl) .nil)
          have typed : B owner fn ((sid 33,fval fs s o tag c extra)::pe s o tag c extra) st
              ⟨span,⟨ls,.letDecl x (some annotation) (some ⟨ws,.literal literal⟩)⟩::
                ⟨ds,.expression ⟨us,.tuple ⟨ts,[]⟩⟩ true⟩::rest⟩ (result fs s o tag c hit extra) st :=
            .binding (.wordLiteral zero) (by simpa only [fsEq,valid.2.2,fresh2,tn,te] using
              (ClosedSourceBodyEvaluates.discard ClosedSourceExpressionEvaluates.unit tail.down))
          have b : B owner pn (pe s o tag c extra) st body (result fs s o tag c hit extra) st := by
            rw [prefixShape]; exact .inferred (.creation (by simpa only [fsEq] using f.shape))
              (by simpa only [valid.2.1,fresh1,fn,fval] using typed)
          return ⟨f,body,by simpa only [fsEq] using b,by
            rw [original]; exact .call SourceUnaryLambdaShape.typed (.group (.creation SourceUnaryLambdaShape.typed))
              a.down (by simpa only [fsEq,valid.1,fresh0,pn,pe] using b)⟩
        | _ => throw (IO.userError "original zero initializer")
      else throw (IO.userError "original binder names")
    | _ => throw (IO.userError "original typed/inferred/discard prefix")
  | _ => throw (IO.userError "original grouped unary call")
private def caller := {owner with declarationIndex:=158}
private def rid (n : Nat) : Resolved.LocalId := ⟨caller,n⟩
private def callNames : LocalNameTable := [("picked",rid 0),("other",rid 1)]
private def reapplied {s o tag c extra st} (f : Function s o tag c extra st) (source : Syntax.Expr) : IO (PLift (E caller callNames [(rid 0,fval f.source s o tag c extra),(rid 1,o)] st source (.pair s o) st)) := do
  match shape : source with
  | ⟨_,.call callee ⟨_,[argument]⟩⟩ =>
    let a ← ref caller callNames [(rid 0,fval f.source s o tag c extra),(rid 1,o)] st callee "picked" (rid 0) (fval f.source s o tag c extra) .head .head
    let b ← ref caller callNames [(rid 0,fval f.source s o tag c extra),(rid 1,o)] st argument "other" (rid 1) o (.tail (by decide) .head) (.tail (by decide) .head)
    return ⟨by rw [shape]; exact .call f.shape a.down b.down (by simpa only [f.named,fresh1] using f.pair o)⟩
  | _ => throw (IO.userError "original different-caller call")
private def run {source s o tag c hit extra st} (proof : Witness source s o tag c hit extra st) (picked : Syntax.Expr) (depth : Nat) : IO Unit := do
  have _ := evaluateClosedSourceExpression?_eventually_complete proof.whole
  have _ := evaluateClosedSourceBody?_eventually_complete proof.body
  let next ← reapplied proof.f picked
  have created : E owner pn (pe s o tag c extra) st proof.f.source (fval proof.f.source s o tag c extra) st := .creation proof.f.shape
  for budget in [0,1,2] do
    match actual : evaluateClosedSourceExpression? budget owner pn (pe s o tag c extra) st proof.f.source with
    | none => check (budget==0) "creation needs depth1 even without body evaluation"
    | some (value,store) =>
      match value with
      | .sourceClosure fs own ns es => check (0<budget && fs==proof.f.source && own==owner && ns==pn && es.map Prod.fst==(pe s o tag c extra).map Prod.fst && store.length==st.length) "actual creation fields"
      | _ => throw (IO.userError "actual creation is a source closure")
      have _ := (evaluateClosedSourceExpression?_sound actual).deterministic created
      pure ()
  for budget in List.range (depth+4) do
    match actual : evaluateClosedSourceExpression? budget owner names (rows s o tag c extra) st source with
    | none => check (budget<depth) "low depth None, not a fault"
    | some (value,final) =>
      check (depth≤budget && final.length==st.length) "actual full endpoint threshold"
      if chosen : c=true ∧ hit=true then
        match actualShape : value with
        | .pair (.pair _ (.word zero)) (.pair (.sourceClosure fs own ns es) .unit) =>
          check (zero==w 0 && fs==proof.f.source && own==owner && ns==pn && es.map Prod.fst==(pe s o tag c extra).map Prod.fst) "computed original closure/capture layout"
          have same := (evaluateClosedSourceExpression?_sound actual).deterministic proof.whole
          have saved : RuntimeValue.sourceClosure fs own ns es=fval proof.f.source s o tag c extra := by
            have valueEq := same.1
            rw [actualShape] at valueEq
            simp only [result,chosen.1,chosen.2,↓reduceIte] at valueEq
            simpa only [chosen.1] using (RuntimeValue.pair.inj (RuntimeValue.pair.inj valueEq).2).1
          have independent : E caller callNames [(rid 0,.sourceClosure fs own ns es),(rid 1,o)] final picked (.pair s o) final := by simpa only [saved,same.2] using next.down
          have _ := evaluateClosedSourceExpression?_eventually_complete independent
          for more in List.range 8 do
            match computed : evaluateClosedSourceExpression? more caller callNames [(rid 0,.sourceClosure fs own ns es),(rid 1,o)] final picked with
            | none => check (more<4) "returned closure low depth"
            | some (v,store) => check (4≤more && store.length==final.length && (match v with | .pair _ _ => true | _ => false)) "returned closure threshold/pair"; have _ := (evaluateClosedSourceExpression?_sound computed).deterministic independent; pure ()
        | _ => throw (IO.userError "actual returned closure shape")
      else
        check (match value with | .unit => c && !hit | .pair _ _ => !c | _ => false) "actual selected endpoint shape"
        have _ := (evaluateClosedSourceExpression?_sound actual).deterministic proof.whole
        pure ()
    match actual : evaluateClosedSourceBody? budget owner pn (pe s o tag c extra) st proof.originalBody with
    | none => check (budget+1<depth) "body low depth"
    | some (value,store) => check (depth≤budget+1) "body threshold"; have _ := (evaluateClosedSourceBody?_sound actual).deterministic proof.body; pure ()
private def boundaries (source : Syntax.Expr) (actual : V) : IO Unit := do
  match source with
  | ⟨_,.lambda _ _ _ ⟨_,[⟨_,.matchWith _ ⟨_,⟨[first,bad],some originalDefault⟩⟩⟩]⟩⟩ =>
    let p ← wildcard first.value.pattern
    selection (show RuntimeWordMatchChooses actual [first,bad] (some originalDefault) first.value.body 0 from .wildcard p.down)
    selection (show RuntimeWordMatchChooses actual [] (some originalDefault) originalDefault 0 from .fallback)
    absentChoice actual [bad] (some originalDefault)
    absentChoice actual [] none
  | _ => throw (IO.userError "original boundary arms/default")
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"closed-source-evaluator.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next => check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && source.span==Syntax.SourceSpan.fullFile file) "complete original AST/span"; return source
  | _ => throw (IO.userError "original parser")
end ParsedClosedSourceEvaluation

open ParsedClosedSourceEvaluation Solcore.Frontend in
/-- Actual depth-bounded results meet independently constructed original source certificates. -/
def frontendParsedClosedSourceEvaluationTests : IO Unit := do
  let source ← parsed "(lam(x:Unknown)->Unknown{let f=lam(y){return (x,y);};let x:Missing=0;();if(c){{match(tag){case 0{return (f(x),f,());}case 0x00{return absent;}case ((_)){return;}}}}else{return f(other);}})(saved)"
  let picked ← parsed "picked(other)"
  let boundary ← parsed "lam(z){match(z){case ((_)){return z;}case Missing{return absent;}default{return;}}}"
  let inert ← parsed "lam(){return absent;}"
  let s := Solcore.Frontend.RuntimeValue.sourceClosure inert caller [("unseen",foreign)] [(sid 32,.bool false)]
  for o in [.hostFunction .storageWrite,.coreClosure .unit .word (.var 99) [s,.cellRef .word 700]] do
    for extra in [[],[(sid 32,o),(foreign,s)]] do
      for store in [[.unit],[s,.cellRef (.function .word .word) 1]] do
        let hit ← witness source s o (.word (w 0)) true true extra store (by intro _; rfl)
        run hit picked 13
        let miss ← witness source s o (.word (w 1)) true false extra store (by intro _; rfl)
        run miss picked 8
        for tag in [s,o] do
          let skipped ← witness source s o tag false true extra store (by simp)
          run skipped picked 10
          match hit.originalBody.value with
          | [_,_,_,⟨_,.ifThen _ ⟨_,[⟨_,.block [⟨_,.matchWith _ ⟨_,⟨cases,originalDefault⟩⟩⟩]⟩]⟩ _⟩] => absentChoice tag cases originalDefault
          | _ => throw (IO.userError "original unvisited match fields")
          check ((evaluateClosedSourceExpression? 40 owner names (rows s o tag true extra) store source).isNone) "literal-first non-Word absence is not a fault"
    boundaries boundary o
  boundaries boundary s

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedClosedSourceOwner
/- Actual parsed creation/call and fresh typed/inferred bindings precede owner
transport. Annotation syntax is inert; fixed successful runs are fixture checks,
not a same-budget covariance law or a heap/location-validity claim. -/
set_option autoImplicit false
namespace Tests.ParsedClosedSourceOwner
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner (n : Nat) : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ParsedOwner",by decide⟩],by decide⟩⟩,n⟩
private def so := owner 311
private def co := owner 711
private def fo := owner 911
private def lid (o : Resolved.DeclarationId) (i : Nat) : Resolved.LocalId := ⟨o,i⟩
private def shift (o : Resolved.DeclarationId) : Resolved.DeclarationId := {o with declarationIndex:=o.declarationIndex+5}
private theorem shift_injective : Function.Injective shift := by
  intro a b same
  have hm := congrArg Resolved.DeclarationId.moduleId same
  have hi := congrArg Resolved.DeclarationId.declarationIndex same
  cases a; cases b
  simp only [shift,Resolved.DeclarationId.mk.injEq] at hm hi ⊢
  exact ⟨hm,by omega⟩
private def sn : LocalNameTable := [("q",lid so 8),("foreign",lid fo 99),("q",lid so 99),("q",lid fo 8)]
private def se (v : V) : Resolved.LocalScope V :=
  [(lid fo 8,.unit),(lid so 8,v),(lid so 8,.bool false),(lid so 100,.cellRef .word 800),
   (lid so 101,.hostFunction .storageWrite),(lid so 102,.bool false),(lid fo 100,v)]
private def cn : LocalNameTable := [("f",lid co 1),("x",lid co 2),("x",lid fo 2),("f",lid co 99),("x",lid co 99)]
private def ce (saved av : V) : Resolved.LocalScope V :=
  [(lid fo 1,.unit),(lid co 1,saved),(lid co 1,.bool false),(lid fo 2,.unit),(lid co 2,av),(lid co 2,.unit)]
private def core : V := .ofCore (.closure .unit .word (.var 99) [.cellRef .word 701,.hostFunction .storageWrite])
private def mixed (source : Syntax.Expr) (caller saved foreign : Resolved.DeclarationId) : V :=
  .pair (.sourceClosure source saved [("q",lid saved 8),("q",lid foreign 8)]
    [(lid saved 8,.coreClosure .unit .word (.var 17)
      [.sourceClosure source foreign [("q",lid caller 8)] [(lid caller 8,.cellRef .word 702),(lid caller 8,.unit)],core]),
     (lid saved 8,.bool false)]) (.pair core (.cellRef .word 703))
private theorem mixed_fields (source : Syntax.Expr) :
    (mixed source co so fo).mapOwners shift = mixed source (shift co) (shift so) (shift fo) := by
  simp only [mixed,core,RuntimeValue.ofCore,List.attach_map_val,RuntimeValue.mapOwners_sourceClosure,
    RuntimeValue.mapOwners_coreClosure,RuntimeValue.mapOwners,mapRuntimeCapturedOwners,
    LocalNameTable.mapIds,ownerLocalIdMap,lid,List.map_cons,List.map_nil]
private def span (f : Syntax.SourceFile) (a b : Nat) : Syntax.SourceSpan := ⟨f.id,a,b⟩
private def ref (f : Syntax.SourceFile) (a b : Nat) (n : String) : Syntax.Expr := ⟨span f a b,.identifier ⟨span f a b,n⟩⟩
private def ty (f : Syntax.SourceFile) (a b : Nat) : Syntax.TypeExpr :=
  ⟨span f a b,.named ⟨span f a b,⟨⟨⟨span f a b,"Unit"⟩,[]⟩⟩⟩ none⟩
private def expectedLambda (typed : Bool) (f : Syntax.SourceFile) : Syntax.Expr :=
  let d := if typed then 5 else 0
  ⟨span f 0 (38+d),.lambda (span f 0 3)
    ⟨span f 3 (6+d),[if typed then ⟨span f 4 10,.typed none ⟨span f 4 5,"q"⟩ (ty f 6 10)⟩
      else ⟨span f 4 5,.inferred ⟨span f 4 5,"q"⟩⟩]⟩ none
    ⟨span f (6+d) (38+d),[⟨span f (7+d) (20+d),.letDecl ⟨span f (11+d) (12+d),"q"⟩
      (some (ty f (13+d) (17+d))) (some (ref f (18+d) (19+d) "q"))⟩,
      ⟨span f (20+d) (28+d),.letDecl ⟨span f (24+d) (25+d),"q"⟩ none (some (ref f (26+d) (27+d) "q"))⟩,
      ⟨span f (28+d) (37+d),.returnStmt (some (ref f (35+d) (36+d) "q"))⟩]⟩⟩
private def expectedCall (f : Syntax.SourceFile) : Syntax.Expr := ⟨span f 0 4,.call (ref f 0 1 "f") ⟨span f 1 4,[ref f 2 3 "x"]⟩⟩
private def typeSpans : Syntax.TypeExpr → List Syntax.SourceSpan
  | ⟨s,.named ⟨q,⟨⟨n,[]⟩⟩⟩ none⟩ => [s,q,n.span]
  | _ => []
private def parameterSpans : Syntax.LambdaParameter → List Syntax.SourceSpan
  | ⟨s,.inferred n⟩ => [s,n.span]
  | ⟨s,.typed none n t⟩ => [s,n.span]++typeSpans t
  | _ => []
private def spans : Syntax.Expr → List Syntax.SourceSpan
  | ⟨s,.identifier n⟩ => [s,n.span]
  | ⟨s,.call f ⟨a,[x]⟩⟩ => [s]++spans f++[a]++spans x
  | ⟨s,.lambda k ⟨ps,[p]⟩ none ⟨b,[⟨l,.letDecl n (some t) (some i)⟩,
      ⟨l2,.letDecl n2 none (some i2)⟩,⟨r,.returnStmt (some e)⟩]⟩⟩ =>
    [s,k,ps]++parameterSpans p++[b,l,n.span]++typeSpans t++spans i++[l2,n2.span]++spans i2++[r]++spans e
  | _ => []
private def ranges (typed : Bool) : List (Nat × Nat) :=
  let d := if typed then 5 else 0
  [(0,38+d),(0,3),(3,6+d)]++(if typed then [(4,10),(4,5),(6,10),(6,10),(6,10)] else [(4,5),(4,5)])++
    ([(6,38),(7,20),(11,12),(13,17),(13,17),(13,17),(18,19),(18,19),(20,28),(24,25),
      (26,27),(26,27),(28,37),(35,36),(35,36)].map (fun (a,b) => (a+d,b+d)))
private def parsed (text : String) (ast : Syntax.SourceFile → Syntax.Expr) (expectedRanges : List (Nat × Nat)) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"parsed-owner-replay.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "owner lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok actual next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && next.file==file &&
      actual.span==Syntax.SourceSpan.fullFile file && actual==ast file) "whole handwritten AST / EOF / diagnostics"
    check ((spans actual).all (fun s => s.isValidFor file) &&
      (spans actual).map (fun s => (s.startByte,s.endByte))==expectedRanges) "all actual handwritten spans"
    return actual
  | _ => throw (IO.userError "owner parser")
private def expression {o n e st source v final} (original : E o n e st source v final) (depth : Nat) : IO Unit := do
  proof original
  match ran : evaluateClosedSourceExpression? depth o n e st source with
  | some (actual,out) =>
    have same := (evaluateClosedSourceExpression?_sound ran).deterministic original
    proof same
    have transported := ClosedSourceExpressionEvaluates.mapOwners shift shift_injective (evaluateClosedSourceExpression?_sound ran)
    proof (show E (shift o) (LocalNameTable.mapIds (ownerLocalIdMap shift) n) (mapRuntimeCapturedOwners shift e)
      (st.map (RuntimeValue.mapOwners shift)) source (v.mapOwners shift) (final.map (RuntimeValue.mapOwners shift)) by simpa only [same.1,same.2] using transported)
    proof transported
  | none => throw (IO.userError "independent original expression actual endpoint")
private def application {source whole : Syntax.Expr} {parameter : Syntax.Identifier} {block : Syntax.Block}
    (shape : SourceUnaryLambdaShape source parameter block) (av : V) (st : List V) : IO Unit := do
  let creationStore := [core,.unit]
  have creation : E so sn (se av) creationStore source (.sourceClosure source so sn (se av)) creationStore := .creation shape
  proof creation
  match created : evaluateClosedSourceExpression? 1 so sn (se av) creationStore source with
  | some (.sourceClosure actualSource actualOwner actualNames actualCaptured,creationFinal) =>
    have same := (evaluateClosedSourceExpression?_sound created).deterministic creation
    have fields := RuntimeValue.sourceClosure.inj same.1
    have actualShape : SourceUnaryLambdaShape actualSource parameter block := fields.1.symm ▸ shape
    proof fields; proof same.2
    check (actualOwner != co && actualOwner != fo && creationFinal.length != st.length) "separate saved owner / creation and invocation stores"
    have mappedFields : (.sourceClosure actualSource actualOwner actualNames actualCaptured : V).mapOwners shift =
        .sourceClosure actualSource (shift actualOwner) (LocalNameTable.mapIds (ownerLocalIdMap shift) actualNames)
          (mapRuntimeCapturedOwners shift actualCaptured) := RuntimeValue.mapOwners_sourceClosure shift _ _ _ _
    proof mappedFields
    match hw : whole with
    | ⟨cs,.call ⟨fs,.identifier f⟩ ⟨als,[⟨xs,.identifier x⟩]⟩⟩ =>
      if names : f.value="f" ∧ x.value="x" ∧ parameter.value="q" then
        let n := cn; let e := ce (.sourceClosure actualSource actualOwner actualNames actualCaptured) av
        have picked : E co n e st ⟨fs,.identifier f⟩ (.sourceClosure actualSource actualOwner actualNames actualCaptured) st :=
          .reference (names.1 ▸ LocalNameTable.Lookup.head) (.tail (by decide) .head)
        have argumentOriginal : E co n e st ⟨xs,.identifier x⟩ av st :=
          .reference (names.2.1 ▸ LocalNameTable.Lookup.tail (by decide) .head)
            (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
        let fresh := Resolved.freshLocalId actualOwner (actualNames.map Prod.snd)
        let bn := (parameter.value,fresh)::actualNames; let be := (fresh,av)::actualCaptured
        have freshExact : fresh=lid so 100 ∧
            Resolved.freshLocalId actualOwner (bn.map Prod.snd)=lid so 101 := by
          rcases fields with ⟨_,rfl,rfl,rfl⟩
          exact ⟨by decide,by change Resolved.freshLocalId so (lid so 100 :: sn.map Prod.snd)=lid so 101; decide⟩
        proof freshExact
        match hb : block with
        | ⟨bs,[⟨_,.letDecl bound (some _) (some ⟨is,.identifier initializer⟩)⟩,
            ⟨_,.letDecl bound2 none (some ⟨is2,.identifier initializer2⟩)⟩,⟨rs,.returnStmt (some ⟨ys,.identifier key⟩)⟩]⟩ =>
          if equal : initializer.value=parameter.value ∧ initializer2.value=bound.value ∧ key.value=bound2.value then
            have init : E actualOwner bn be st ⟨is,.identifier initializer⟩ av st := .reference (equal.1 ▸ LocalNameTable.Lookup.head) .head
            let fresh2 := Resolved.freshLocalId actualOwner (bn.map Prod.snd)
            let bn2 := (bound.value,fresh2)::bn; let be2 := (fresh2,av)::be
            have init2 : E actualOwner bn2 be2 st ⟨is2,.identifier initializer2⟩ av st :=
              .reference (equal.2.1 ▸ LocalNameTable.Lookup.head) .head
            have fresh3 : Resolved.freshLocalId actualOwner (bn2.map Prod.snd)=lid so 102 := by
              rcases fields with ⟨_,rfl,rfl,rfl⟩
              change Resolved.freshLocalId so (lid so 101 :: lid so 100 :: sn.map Prod.snd)=lid so 102
              decide
            proof fresh3
            have returned : B actualOwner ((bound2.value,Resolved.freshLocalId actualOwner (bn2.map Prod.snd))::bn2)
                ((Resolved.freshLocalId actualOwner (bn2.map Prod.snd),av)::be2) st
                ⟨bs,[⟨rs,.returnStmt (some ⟨ys,.identifier key⟩)⟩]⟩ av st :=
              .expression (.reference (equal.2.2 ▸ LocalNameTable.Lookup.head) .head)
            have originalBody : B actualOwner bn be st block av st := by rw [hb]; exact .binding init (.inferred init2 returned)
            have originalCall : E co n e st whole av st := by rw [hw]; exact .call actualShape picked argumentOriginal originalBody
            proof picked; proof argumentOriginal; proof init; proof init2; proof returned; proof originalBody; proof originalCall
            match cr : evaluateClosedSourceExpression? 1 co n e st ⟨fs,.identifier f⟩ with
            | some (calleeValue,calleeStore) =>
              have actualCallee := evaluateClosedSourceExpression?_sound cr
              have calleeEndpoint := actualCallee.deterministic picked
              proof calleeEndpoint
              match ar : evaluateClosedSourceExpression? 1 co n e calleeStore ⟨xs,.identifier x⟩ with
              | some (argumentValue,argumentStore) =>
                have actualArgument := evaluateClosedSourceExpression?_sound ar
                have alignedArgument : E co n e st ⟨xs,.identifier x⟩ argumentValue argumentStore := calleeEndpoint.2 ▸ actualArgument
                have argumentEndpoint := alignedArgument.deterministic argumentOriginal
                proof argumentEndpoint
                match ran : evaluateClosedSourceBody? 4 actualOwner bn ((fresh,argumentValue)::actualCaptured) argumentStore block with
                | some (actual,out) =>
                  have actualBody := evaluateClosedSourceBody?_sound ran
                  have alignedBody : B actualOwner bn be st block actual out := by
                    simpa only [argumentEndpoint.1,argumentEndpoint.2] using actualBody
                  have endpoint := alignedBody.deterministic originalBody
                  proof endpoint
                  have actualCall := ClosedSourceExpressionEvaluates.call (span:=cs) (argumentsSpan:=als) actualShape
                    (calleeEndpoint.1 ▸ actualCallee) actualArgument actualBody
                  proof actualCall
                  have transported := ClosedSourceBodyEvaluates.mapOwners shift shift_injective actualBody
                  proof transported
                  proof (show B (shift actualOwner) (LocalNameTable.mapIds (ownerLocalIdMap shift) bn)
                    (mapRuntimeCapturedOwners shift be) (st.map (RuntimeValue.mapOwners shift)) block (av.mapOwners shift)
                    (st.map (RuntimeValue.mapOwners shift)) by
                    simpa only [argumentEndpoint.1,argumentEndpoint.2,endpoint.1,endpoint.2] using transported)
                  expression actualCall 5
                | none => throw (IO.userError "actual typed/inferred saved body")
              | none => throw (IO.userError "actual argument at actual callee store")
            | none => throw (IO.userError "actual caller saved callee")
            expression creation 1; expression picked 1; expression argumentOriginal 1
          else throw (IO.userError "actual fresh shadowing spellings")
        | _ => throw (IO.userError "actual typed/inferred saved body shape")
      else throw (IO.userError "actual caller and parameter spellings")
    | _ => throw (IO.userError "actual f(x) shape")
  | _ => throw (IO.userError "actual returned creation closure")
private def savedCall (source whole : Syntax.Expr) (av : V) (st : List V) : IO Unit := do
  match hs : source with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred p⟩]⟩ _ b⟩ =>
    have shape : SourceUnaryLambdaShape source p b := by rw [hs]; exact .inferred
    application (whole:=whole) shape av st
  | ⟨_,.lambda _ ⟨_,[⟨_,.typed none p _⟩]⟩ _ b⟩ =>
    have shape : SourceUnaryLambdaShape source p b := by rw [hs]; exact .typed
    application (whole:=whole) shape av st
  | _ => throw (IO.userError "actual unmarked unary lambda")
end Tests.ParsedClosedSourceOwner
open Solcore Solcore.Frontend Tests.ParsedClosedSourceOwner in
def Tests.frontendParsedClosedSourceOwnerTests : IO Unit := do
  let inferred ← parsed "lam(q){let q:Unit=q;let q=q;return q;}" (expectedLambda false) (ranges false)
  let typed ← parsed "lam(q:Unit){let q:Unit=q;let q=q;return q;}" (expectedLambda true) (ranges true)
  let call ← parsed "f(x)" expectedCall [(0,4),(0,1),(0,1),(1,4),(2,3),(2,3)]
  let mut count := 0
  for source in [inferred,typed] do
    let nested := mixed source co so fo
    have exactValue := mixed_fields source
    have exactStore : [nested,RuntimeValue.cellRef .word 900,core].map (RuntimeValue.mapOwners shift) =
        [mixed source (shift co) (shift so) (shift fo),.cellRef .word 900,core] := by
      simp only [List.map_cons,List.map_nil,nested,exactValue,core,RuntimeValue.ofCore,List.attach_map_val,
        RuntimeValue.mapOwners_coreClosure,RuntimeValue.mapOwners,List.map_cons,List.map_nil]
    proof exactValue; proof exactStore
    for av in [nested,RuntimeValue.pair (.cellRef .word 901) nested] do
      for st in [[nested,.cellRef .word 900,core],[core,nested,.cellRef .word 999,.hostFunction .storageRead]] do
        savedCall source call av st
        count := count+1
  check (count==8) "two actual lambda annotations / two nested arguments / two nonempty stores"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedClosedSourceStoreReplay
/- Literal runtime values and saved lexical fields survive store replacement.
Opaque cells are data, not a guarantee that replacement heaps validate them.
Independent original fixtures and actual endpoints precede the replay laws. -/
set_option autoImplicit false
namespace Tests.ParsedClosedSourceStoreReplay
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner (n : Nat) : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ParsedStoreReplay",by decide⟩],by decide⟩⟩,n⟩
private def so := owner 309
private def co := owner 909
private def sid (n : Nat) : Resolved.LocalId := ⟨so,n⟩
private def cid (n : Nat) : Resolved.LocalId := ⟨co,n⟩
private def sn : LocalNameTable := [("z",sid 2),("q",sid 8),("x",cid 40),("z",sid 99),("q",sid 99)]
private def se (sv core : V) : Resolved.LocalScope V := [(sid 2,sv),(sid 2,.unit),(sid 8,core),(sid 99,.bool false),(sid 100,core)]
private def cn : LocalNameTable := [("f",cid 1),("x",cid 2),("z",cid 3),("f",cid 99),("x",cid 99)]
private def ce (saved av other : V) : Resolved.LocalScope V :=
  [(cid 1,saved),(cid 1,other),(cid 2,av),(cid 2,.unit),(cid 3,other),(cid 99,other)]
private def span (f : Syntax.SourceFile) (a b : Nat) : Syntax.SourceSpan := ⟨f.id,a,b⟩
private def ref (f : Syntax.SourceFile) (a b : Nat) (name : String) : Syntax.Expr := ⟨span f a b,.identifier ⟨span f a b,name⟩⟩
private def expectedLambda (binding : Bool) (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f 0 (if binding then 25 else 17),.lambda (span f 0 3)
    ⟨span f 3 6,[⟨span f 4 5,.inferred ⟨span f 4 5,"q"⟩⟩]⟩ none
    (if binding then ⟨span f 6 25,[⟨span f 7 15,.letDecl ⟨span f 11 12,"q"⟩ none (some (ref f 13 14 "q"))⟩,
      ⟨span f 15 24,.returnStmt (some (ref f 22 23 "q"))⟩]⟩
    else ⟨span f 6 17,[⟨span f 7 16,.returnStmt (some (ref f 14 15 "z"))⟩]⟩)⟩
private def expectedCall (f : Syntax.SourceFile) : Syntax.Expr := ⟨span f 0 4,.call (ref f 0 1 "f") ⟨span f 1 4,[ref f 2 3 "x"]⟩⟩
private def expectedShort (op : Syntax.BinaryOp) (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f 0 6,.binary (ref f 0 1 "a") ⟨span f 2 4,op⟩ (ref f 5 6 "w")⟩
private def spans : Syntax.Expr → List Syntax.SourceSpan
  | ⟨s,.identifier n⟩ => [s,n.span]
  | ⟨s,.call f ⟨a,[x]⟩⟩ => [s]++spans f++[a]++spans x
  | ⟨s,.binary l op r⟩ => [s]++spans l++[op.span]++spans r
  | ⟨s,.lambda k ⟨ps,[⟨p,.inferred n⟩]⟩ none ⟨b,[⟨r,.returnStmt (some e)⟩]⟩⟩ => [s,k,ps,p,n.span,b,r]++spans e
  | ⟨s,.lambda k ⟨ps,[⟨p,.inferred n⟩]⟩ none ⟨b,[⟨l,.letDecl v none (some i)⟩,⟨r,.returnStmt (some e)⟩]⟩⟩ =>
    [s,k,ps,p,n.span,b,l,v.span]++spans i++[r]++spans e
  | _ => []
private def parsed (text : String) (ast : Syntax.SourceFile → Syntax.Expr) (ranges : List (Nat × Nat)) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"parsed-store-replay.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "store replay lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok actual next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && next.file==file &&
      actual.span==Syntax.SourceSpan.fullFile file && actual==ast file) "whole handwritten AST / EOF / zero diagnostics"
    check ((spans actual).all (fun s => s.isValidFor file) &&
      (spans actual).map (fun s => (s.startByte,s.endByte))==ranges) "every actual range"
    return actual
  | _ => throw (IO.userError "store replay parser")
private def expression {o n e st source v final} (original : E o n e st source v final)
    (depth : Nat) (replacements : List (List V)) : IO Unit := do
  proof original
  for budget in [0,depth-1,depth,depth+3] do
    match ran : evaluateClosedSourceExpression? budget o n e st source with
    | none =>
      check (budget<depth) "independent low expression None"
      for replacement in replacements do
        check ((evaluateClosedSourceExpression? budget o n e replacement source).isNone) "same low expression None"
        have law := evaluateClosedSourceExpression?_replay_store budget o n e st replacement source
        proof law
        proof (show evaluateClosedSourceExpression? budget o n e replacement source = none by simpa only [ran,Option.map_none] using law)
    | some (actual,out) =>
      have evaluated := evaluateClosedSourceExpression?_sound ran
      proof (show actual=v ∧ out=final from evaluated.deterministic original); proof evaluated.store_eq
      check (depth≤budget) "independent sharp expression depth"
      for replacement in replacements do
        have replay := evaluated.replay_store replacement
        match other : evaluateClosedSourceExpression? budget o n e replacement source with
        | some (_,_) => proof ((evaluateClosedSourceExpression?_sound other).deterministic replay)
        | none => throw (IO.userError "successful expression store replacement")
        have law := evaluateClosedSourceExpression?_replay_store budget o n e st replacement source
        proof law
        proof (show evaluateClosedSourceExpression? budget o n e replacement source = some (actual,replacement) by
          simpa only [ran,Option.map_some] using law)
private def body {o n e st source v final} (original : B o n e st source v final)
    (depth : Nat) (replacements : List (List V)) : IO Unit := do
  proof original
  for budget in [0,depth-1,depth,depth+3] do
    match ran : evaluateClosedSourceBody? budget o n e st source with
    | none =>
      check (budget<depth) "independent low body None"
      for replacement in replacements do
        check ((evaluateClosedSourceBody? budget o n e replacement source).isNone) "same low body None"
        have law := evaluateClosedSourceBody?_replay_store budget o n e st replacement source
        proof law
        proof (show evaluateClosedSourceBody? budget o n e replacement source = none by simpa only [ran,Option.map_none] using law)
    | some (actual,out) =>
      have evaluated := evaluateClosedSourceBody?_sound ran
      proof (show actual=v ∧ out=final from evaluated.deterministic original); proof evaluated.store_eq
      check (depth≤budget) "independent sharp body depth"
      for replacement in replacements do
        have replay := evaluated.replay_store replacement
        match other : evaluateClosedSourceBody? budget o n e replacement source with
        | some (_,_) => proof ((evaluateClosedSourceBody?_sound other).deterministic replay)
        | none => throw (IO.userError "successful body store replacement")
        have law := evaluateClosedSourceBody?_replay_store budget o n e st replacement source
        proof law
        proof (show evaluateClosedSourceBody? budget o n e replacement source = some (actual,replacement) by
          simpa only [ran,Option.map_some] using law)
private def application {source callee argument : Syntax.Expr} {parameter : Syntax.Identifier} {block : Syntax.Block}
    {o n e st av value savedOwner savedNames savedCaptured} {cs als : Syntax.SourceSpan}
    (shape : SourceUnaryLambdaShape source parameter block)
    (picked : E o n e st callee (.sourceClosure source savedOwner savedNames savedCaptured) st)
    (argumentOriginal : E o n e st argument av st)
    (independent : B savedOwner ((parameter.value,Resolved.freshLocalId savedOwner (savedNames.map Prod.snd))::savedNames)
      ((Resolved.freshLocalId savedOwner (savedNames.map Prod.snd),av)::savedCaptured) st block value st)
    (depth : Nat) (replacements : List (List V)) : IO Unit := do
  have originalCall := ClosedSourceExpressionEvaluates.call (span:=cs) (argumentsSpan:=als) shape picked argumentOriginal independent
  proof independent; proof originalCall
  match ran : evaluateClosedSourceBody? depth savedOwner
      ((parameter.value,Resolved.freshLocalId savedOwner (savedNames.map Prod.snd))::savedNames)
      ((Resolved.freshLocalId savedOwner (savedNames.map Prod.snd),av)::savedCaptured) st block with
  | some (bv,bs) =>
    have actualBody := evaluateClosedSourceBody?_sound ran
    proof (show bv=value ∧ bs=st from actualBody.deterministic independent)
    have actualCall := ClosedSourceExpressionEvaluates.call (span:=cs) (argumentsSpan:=als) shape picked argumentOriginal actualBody
    body independent depth replacements
    expression actualCall (depth+1) replacements
  | none => throw (IO.userError "independent actual saved body")
private def savedCall (source whole : Syntax.Expr) (sv av core other : V) (st : List V)
    (replacements : List (List V)) : IO Unit := do
  match hs : source, hw : whole with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred parameter⟩]⟩ _ block⟩,⟨cs,.call ⟨fs,.identifier f⟩ ⟨als,[⟨xs,.identifier x⟩]⟩⟩ =>
    have shape : SourceUnaryLambdaShape source parameter block := by rw [hs]; exact .inferred
    let creationStore := [other,core,.unit]
    have creation : E so sn (se sv core) creationStore source (.sourceClosure source so sn (se sv core)) creationStore := .creation shape
    proof creation
    match created : evaluateClosedSourceExpression? 1 so sn (se sv core) creationStore source with
    | some (.sourceClosure actualSource actualOwner actualNames actualCaptured,creationFinal) =>
      have same := (evaluateClosedSourceExpression?_sound created).deterministic creation
      have fields := RuntimeValue.sourceClosure.inj same.1
      have actualShape : SourceUnaryLambdaShape actualSource parameter block := fields.1.symm ▸ shape
      proof fields; proof same.2
      check (actualOwner != co && creationFinal.length != st.length) "actual saved owner/creation store distinct from invocation"
      let n := cn; let e := ce (.sourceClosure actualSource actualOwner actualNames actualCaptured) av other
      if names : f.value="f" ∧ x.value="x" ∧ parameter.value="q" then
        have picked : E co n e st ⟨fs,.identifier f⟩ (.sourceClosure actualSource actualOwner actualNames actualCaptured) st :=
          .reference (names.1 ▸ LocalNameTable.Lookup.head) .head
        have argumentOriginal : E co n e st ⟨xs,.identifier x⟩ av st :=
          .reference (names.2.1 ▸ LocalNameTable.Lookup.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head))
        proof picked; proof argumentOriginal
        match xr : evaluateClosedSourceExpression? 1 co n e st ⟨xs,.identifier x⟩ with
        | some (_,_) => proof ((evaluateClosedSourceExpression?_sound xr).deterministic argumentOriginal)
        | none => throw (IO.userError "actual caller x planned payload")
        let fresh := Resolved.freshLocalId actualOwner (actualNames.map Prod.snd)
        let bn := (parameter.value,fresh)::actualNames; let be := (fresh,av)::actualCaptured
        match hb : block with
        | ⟨_,[⟨_,.returnStmt (some ⟨ys,.identifier key⟩)⟩]⟩ =>
          if hk : key.value="z" then
            have child : E actualOwner bn be st ⟨ys,.identifier key⟩ sv st := by
              rcases fields with ⟨_,rfl,rfl,rfl⟩
              apply ClosedSourceExpressionEvaluates.reference (id:=sid 2) _ (Resolved.LocalScope.Lookup.tail (by decide) .head)
              rw [hk]; exact .tail (by simpa only [names.2.2] using (by decide : "q" ≠ "z")) .head
            have originalBody : B actualOwner bn be st block sv st := by rw [hb]; exact .expression child
            application (cs:=cs) (als:=als) actualShape picked argumentOriginal originalBody 2 replacements
          else throw (IO.userError "actual saved free z")
        | ⟨bs,[⟨_,.letDecl bound none (some ⟨is,.identifier initializer⟩)⟩,⟨rs,.returnStmt (some ⟨ys,.identifier key⟩)⟩]⟩ =>
          if equal : initializer.value=parameter.value ∧ key.value=bound.value then
            have init : E actualOwner bn be st ⟨is,.identifier initializer⟩ av st :=
              .reference (equal.1 ▸ LocalNameTable.Lookup.head) .head
            have returned : B actualOwner ((bound.value,Resolved.freshLocalId actualOwner (bn.map Prod.snd))::bn)
                ((Resolved.freshLocalId actualOwner (bn.map Prod.snd),av)::be) st
                ⟨bs,[⟨rs,.returnStmt (some ⟨ys,.identifier key⟩)⟩]⟩ av st :=
              .expression (.reference (equal.2 ▸ LocalNameTable.Lookup.head) .head)
            have originalBody : B actualOwner bn be st block av st := by rw [hb]; exact .inferred init returned
            application (cs:=cs) (als:=als) actualShape picked argumentOriginal originalBody 3 replacements
          else throw (IO.userError "actual initializer before fresh shadow and fresh return")
        | _ => throw (IO.userError "actual saved binding or free body")
        expression creation 1 replacements
      else throw (IO.userError "actual f/x/q spellings")
    | _ => throw (IO.userError "actual closure creation endpoint")
  | _,_ => throw (IO.userError "actual saved lambda and f(x)")
private def failure (o : Resolved.DeclarationId) (n : LocalNameTable) (e : Resolved.LocalScope V)
    (st : List V) (source : Syntax.Expr) (replacements : List (List V)) : IO Unit := do
  for budget in [0,1,2,5] do
    match ran : evaluateClosedSourceExpression? budget o n e st source with
    | none =>
      for replacement in replacements do
        check ((evaluateClosedSourceExpression? budget o n e replacement source).isNone) "store cannot repair this failure"
        have law := evaluateClosedSourceExpression?_replay_store budget o n e st replacement source
        proof law
        proof (show evaluateClosedSourceExpression? budget o n e replacement source = none by simpa only [ran,Option.map_none] using law)
    | some _ => throw (IO.userError "independent actual unsupported expression")
private def shortCircuit (source : Syntax.Expr) (core : V) (st : List V) (replacements : List (List V)) : IO Unit := do
  match hs : source with
  | ⟨ss,.binary ⟨ls,.identifier left⟩ ⟨os,.logicalAnd⟩ ⟨rs,.identifier right⟩⟩ =>
    if names : left.value="a" ∧ right.value="w" then
      let n : LocalNameTable := [("a",cid 4),("a",cid 99)]
      let e (v : V) : Resolved.LocalScope V := [(cid 4,v),(cid 4,core),(cid 99,core)]
      have absent : ∀ v final, ¬ E co n (e (.bool false)) st ⟨rs,.identifier right⟩ v final := by
        intro v final original; cases original with
        | creation impossible => cases impossible
        | reference named _ =>
          have looked := LocalNameTable.lookup?_iff.mpr named
          simp [n,LocalNameTable.lookup?,names.2] at looked
      have leftOriginal : E co n (e (.bool false)) st ⟨ls,.identifier left⟩ (.bool false) st :=
        .reference (names.1 ▸ LocalNameTable.Lookup.head) .head
      have original : E co n (e (.bool false)) st source (.bool false) st := by rw [hs]; exact .andFalse leftOriginal
      have direct : evaluateClosedSourceExpression? 2 co n (e (.bool false)) st source = some (.bool false,st) := by
        simp [hs,evaluateClosedSourceExpression?,n,e,LocalNameTable.lookup?,Resolved.LocalScope.lookup?,names.1]
      proof absent; proof original; proof direct
      expression original 2 replacements
      failure co n (e (.bool false)) st ⟨rs,.identifier right⟩ replacements
      let bad := RuntimeValue.cellRef .word 700
      have badLeft : E co n (e bad) st ⟨ls,.identifier left⟩ bad st := .reference (names.1 ▸ LocalNameTable.Lookup.head) .head
      have impossible : ∀ v final, ¬ E co n (e bad) st source v final := by
        intro v final original; rw [hs] at original; cases original with
        | creation noShape => cases noShape
        | andFalse child => have equal := (child.deterministic badLeft).1; dsimp only [bad] at equal; cases equal
        | andTrue child _ => have equal := (child.deterministic badLeft).1; dsimp only [bad] at equal; cases equal
        | strictWordBinary _ _ meaning => cases meaning
      proof badLeft; proof impossible
      failure co n (e bad) st source replacements
    else throw (IO.userError "actual a/w short circuit names")
  | _ => throw (IO.userError "actual logical and short circuit")
end Tests.ParsedClosedSourceStoreReplay
open Solcore Solcore.Frontend Tests.ParsedClosedSourceStoreReplay in
def Tests.frontendParsedClosedSourceStoreReplayTests : IO Unit := do
  let free ← parsed "lam(q){return z;}" (expectedLambda false) [(0,17),(0,3),(3,6),(4,5),(4,5),(6,17),(7,16),(14,15),(14,15)]
  let bound ← parsed "lam(q){let q=q;return q;}" (expectedLambda true)
    [(0,25),(0,3),(3,6),(4,5),(4,5),(6,25),(7,15),(11,12),(13,14),(13,14),(15,24),(22,23),(22,23)]
  let call ← parsed "f(x)" expectedCall [(0,4),(0,1),(0,1),(1,4),(2,3),(2,3)]
  let short ← parsed "a && w" (expectedShort .logicalAnd) [(0,6),(0,1),(0,1),(2,4),(5,6),(5,6)]
  let core := RuntimeValue.ofCore (.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700])
  let other := RuntimeValue.sourceClosure free (owner 609) [("q",cid 77),("q",cid 88)] [(cid 77,core),(cid 77,.bool false)]
  let replacements : List (List RuntimeValue) := [[],[.unit],[other,core,.cellRef .word 999,.hostFunction .storageWrite]]
  let mut count := 0
  for st in [[],[other,core,.hostFunction .storageWrite,.cellRef .word 900]] do
    for (sv,av) in [(other,RuntimeValue.cellRef .word 700),(core,other),
        (RuntimeValue.pair core other,RuntimeValue.word Core.Word.maximum)] do
      for source in [free,bound] do
        savedCall source call sv av core other st replacements
        count := count+1
    shortCircuit short core st replacements
  check (count==12) "two saved bodies / three mixed payload pairs / two initial stores / three replacements"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedClosedSourceUnary
/- Independent original certificates precede depth runs and full actual image checks. -/
set_option autoImplicit false
namespace Tests.ParsedClosedSourceUnary
open Solcore Solcore.Frontend

private def check (b : Bool) (message : String) : IO Unit := unless b do throw (IO.userError message)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"UnaryParsed", by decide⟩], by decide⟩⟩, 296⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def foreign : Resolved.DeclarationId := {owner with declarationIndex := 901}
private def fid (n : Nat) : Resolved.LocalId := ⟨foreign, n⟩
private def opaqueCore : RuntimeValue := RuntimeValue.ofCore
  (.closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef .word 700])
private def names : LocalNameTable :=
  [("flag",sid 7),("word",sid 31),("unit",sid 8),("pair",sid 9),
    ("core",sid 10),("src",sid 11),("lost",sid 17),("flag",fid 700)]
private def rows (p : RuntimeValue) (b : Bool) (w : Core.Word) : Resolved.LocalScope RuntimeValue :=
  [(sid 99,p),(sid 31,.word w),(sid 7,.bool b),(sid 8,.unit),
    (sid 9,.pair .unit (.word w)),(sid 10,opaqueCore),(sid 11,p),
    (sid 7,.bool (!b)),(fid 700,.word Core.Word.maximum)]
private def stores (p : RuntimeValue) (w : Core.Word) : List (List RuntimeValue) :=
  [[p,opaqueCore,.hostFunction .storageWrite,.cellRef (.function .word .word) 900,
    .pair (.word w) .unit],[opaqueCore,p]]

private def parsed (text : String) : IO (Syntax.SourceFile × Syntax.Expr) := do
  let file : Syntax.SourceFile := ⟨⟨.main,"unary-" ++ text ++ ".sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "unary lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok src next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
      src.span == Syntax.SourceSpan.fullFile file) "complete original source and EOF"
    return (file,src)
  | _ => throw (IO.userError "unary original parser")

private structure Certificate (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (src : Syntax.Expr) where
  value : RuntimeValue
  depth : Nat
  original : ClosedSourceExpressionEvaluates owner names captured store src value store
  image : ∀ actual final, ClosedSourceExpressionEvaluates owner names captured store src actual final ↔
    actual = value ∧ final = store

private theorem endpoint_image {captured store src value}
    (original : ClosedSourceExpressionEvaluates owner names captured store src value store) :
    ∀ actual final, ClosedSourceExpressionEvaluates owner names captured store src actual final ↔
      actual = value ∧ final = store := by
  intro actual final
  constructor
  · exact fun evaluated => evaluated.deterministic original
  · rintro ⟨rfl,rfl⟩; exact original

private def certificate (file : Syntax.SourceFile) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (src : Syntax.Expr) : IO (Certificate captured store src) := do
  check (src.span.isValidFor file) "original source-owned expression span"
  match shape : src with
  | ⟨span,.identifier name⟩ =>
    check (span == name.span && name.span.isValidFor file) "original reference span"
    match named : names.lookup? name.value with
    | none => throw (IO.userError "independent name")
    | some id => match found : captured.lookup? id with
      | none => throw (IO.userError "independent capture")
      | some value =>
        have original : ClosedSourceExpressionEvaluates owner names captured store src value store := by
          rw [shape]
          exact .reference (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)
        return ⟨value,1,original,endpoint_image original⟩
  | ⟨span,.literal literal⟩ =>
    check (span == literal.span && literal.span.isValidFor file) "original numeric literal span"
    match meaning : interpretWordLiteral? literal with
    | none => throw (IO.userError "independent literal meaning")
    | some value =>
      have original : ClosedSourceExpressionEvaluates owner names captured store src (.word value) store := by
        rw [shape]; exact .wordLiteral (interpretWordLiteral?_sound meaning)
      return ⟨.word value,1,original,endpoint_image original⟩
  | ⟨span,.group child⟩ =>
    check (span.contains child.span && span.startByte+1 == child.span.startByte &&
      child.span.endByte+1 == span.endByte &&
      file.content.toByteArray.data[span.startByte]? == some 40 &&
      file.content.toByteArray.data[span.endByte-1]? == some 41) "original group parentheses"
    let h ← certificate file captured store child
    have original : ClosedSourceExpressionEvaluates owner names captured store src h.value store := by
      rw [shape]; exact .group h.original
    return ⟨h.value,h.depth+1,original,by
      intro actual final
      constructor
      · intro evaluated; rw [shape] at evaluated
        cases evaluated with
        | creation impossible => cases impossible
        | group child => exact (h.image _ _).mp child
      · rintro ⟨rfl,rfl⟩; exact original⟩
  | ⟨span,.unary op operand⟩ =>
    check (op.span.isValidFor file && span.contains operand.span && span.contains op.span &&
      op.span.length == 1 && op.span.endByte == operand.span.startByte &&
      span == Syntax.SourceSpan.cover op.span operand.span) "original unary operator/operand ranges"
    let h ← certificate file captured store operand
    match operator : op.value, value : h.value with
    | .logicalNot,.bool b =>
      check (file.content.toByteArray.data[op.span.startByte]? == some 33) "original logical-not byte"
      have child : ClosedSourceExpressionEvaluates owner names captured store operand (.bool b) store :=
        value ▸ h.original
      have original : ClosedSourceExpressionEvaluates owner names captured store src (.bool (!b)) store := by
        rw [shape]; cases op; simp only at operator; cases operator; exact .logicalNot child
      proof original
      proof (evaluateClosedSourceExpression?_logicalNot h.depth owner names captured store span op.span operand)
      return ⟨.bool (!b),h.depth+1,original,by
        intro actual final
        rw [shape]; cases op; simp only at operator; cases operator
        constructor
        · intro evaluated
          obtain ⟨v,ev,same⟩ := closedSourceExpressionEvaluates_logicalNot_iff.mp evaluated
          obtain ⟨sameChild,rfl⟩ := (h.image _ _).mp ev
          rw [value] at sameChild
          cases RuntimeValue.bool.inj sameChild
          exact ⟨same,rfl⟩
        · rintro ⟨rfl,rfl⟩
          exact closedSourceExpressionEvaluates_logicalNot_iff.mpr ⟨b,child,rfl⟩⟩
    | .bitNot,.word w =>
      check (file.content.toByteArray.data[op.span.startByte]? == some 126) "original bit-not byte"
      have child : ClosedSourceExpressionEvaluates owner names captured store operand (.word w) store :=
        value ▸ h.original
      have original : ClosedSourceExpressionEvaluates owner names captured store src (.word w.bitNot) store := by
        rw [shape]; cases op; simp only at operator; cases operator; exact .bitNot child
      proof original
      proof (evaluateClosedSourceExpression?_bitNot h.depth owner names captured store span op.span operand)
      return ⟨.word w.bitNot,h.depth+1,original,by
        intro actual final
        rw [shape]; cases op; simp only at operator; cases operator
        constructor
        · intro evaluated
          obtain ⟨v,ev,same⟩ := closedSourceExpressionEvaluates_bitNot_iff.mp evaluated
          obtain ⟨sameChild,rfl⟩ := (h.image _ _).mp ev
          rw [value] at sameChild
          cases RuntimeValue.word.inj sameChild
          exact ⟨same,rfl⟩
        · rintro ⟨rfl,rfl⟩
          exact closedSourceExpressionEvaluates_bitNot_iff.mpr ⟨w,child,rfl⟩⟩
    | _,_ => throw (IO.userError "independent actual unary operand shape")
  | _ => throw (IO.userError "independent direct unary profile")
termination_by sizeOf src

private def runCase (text : String) (depth : Nat) (p : RuntimeValue) (b : Bool) (w : Core.Word)
    (store : List RuntimeValue) (expected : Core.Value) : IO Unit := do
  let (file,src) ← parsed text
  let captured := rows p b w
  let h ← certificate file captured store src
  proof h.original
  check (h.depth == depth) "handwritten exact path depth"
  match h.value,expected with
  | .bool a,.bool b => check (a == b) "independent Boolean expectation"
  | .word a,.word b => check (a == b) "independent complete Word expectation"
  | _,_ => throw (IO.userError "independent primitive result")
  for budget in [0,depth-1,depth,depth+3] do
    match result : evaluateClosedSourceExpression? budget owner names captured store src with
    | none => check (budget < depth) "unary depth should succeed"
    | some (actual,final) =>
      have evaluated := evaluateClosedSourceExpression?_sound result
      have exactImage := (h.image actual final).mp evaluated
      proof exactImage
      proof ((h.image actual final).mpr exactImage)
      proof ((h.image h.value store).mpr ⟨rfl,rfl⟩)
      check (budget ≥ depth) "unary depth below exact path"

end Tests.ParsedClosedSourceUnary
open Tests.ParsedClosedSourceUnary in
def Tests.frontendParsedClosedSourceUnaryTests : IO Unit := do
  let (_,inert) ← parsed "lam(){return absent;}"
  let p := Solcore.Frontend.RuntimeValue.sourceClosure inert foreign
    [("unused",fid 700)] [(fid 700,.bool true)]
  for b in [false,true] do
    for w in [Solcore.Core.Word.zero,Solcore.Core.Word.maximum,Solcore.Core.Word.ofNatModulo 17] do
      for store in stores p w do
        for (text,depth,expected) in
          [("flag",1,Solcore.Core.Value.bool b),("word",1,.word w),
            ("!flag",2,.bool (!b)),("~word",2,.word w.bitNot),
            ("!!flag",3,.bool b),("~~word",3,.word w),
            ("!(flag)",3,.bool (!b)),("~(word)",3,.word w.bitNot),
            ("!((flag))",4,.bool (!b)),("~((word))",4,.word w.bitNot),
            ("~0",2,.word Solcore.Core.Word.maximum),
            ("~0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",2,
              .word Solcore.Core.Word.zero)] do
          runCase text depth p b w store expected
end

section
-- leanmerge: from Solcore.Test.FrontendParsedClosedSourceUnaryBoundaries
/- Original operand certificates distinguish shape and lookup fixtures before closed runs. -/
set_option autoImplicit false
namespace Tests.ParsedClosedSourceUnaryBoundaries
open Solcore Solcore.Frontend

private def check (b : Bool) (message : String) : IO Unit := unless b do throw (IO.userError message)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"UnaryParsed", by decide⟩], by decide⟩⟩, 296⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def foreign : Resolved.DeclarationId := {owner with declarationIndex := 901}
private def fid (n : Nat) : Resolved.LocalId := ⟨foreign, n⟩
private def opaqueCore : RuntimeValue := RuntimeValue.ofCore
  (.closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef .word 700])
private def names : LocalNameTable :=
  [("flag",sid 7),("word",sid 31),("unit",sid 8),("pair",sid 9),
    ("core",sid 10),("src",sid 11),("lost",sid 17),("flag",fid 700)]
private def rows (p : RuntimeValue) (b : Bool) (w : Core.Word) : Resolved.LocalScope RuntimeValue :=
  [(sid 99,p),(sid 31,.word w),(sid 7,.bool b),(sid 8,.unit),
    (sid 9,.pair .unit (.word w)),(sid 10,opaqueCore),(sid 11,p),
    (sid 7,.bool (!b)),(fid 700,.word Core.Word.maximum)]
private def stores (p : RuntimeValue) (w : Core.Word) : List (List RuntimeValue) :=
  [[p,opaqueCore,.hostFunction .storageWrite,.cellRef (.function .word .word) 900,
    .pair (.word w) .unit],[opaqueCore,p]]

private def parsed (text : String) : IO (Syntax.SourceFile × Syntax.Expr) := do
  let file : Syntax.SourceFile := ⟨⟨.main,"unary-" ++ text ++ ".sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "unary lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok src next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
      src.span == Syntax.SourceSpan.fullFile file) "complete original source and EOF"
    return (file,src)
  | _ => throw (IO.userError "unary original parser")

private def Rejected (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (src : Syntax.Expr) : Prop :=
  ∀ actual final, ¬ ClosedSourceExpressionEvaluates owner names captured store src actual final

private inductive Outcome (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (src : Syntax.Expr) where
  | success (value : RuntimeValue) (depth : Nat)
      (original : ClosedSourceExpressionEvaluates owner names captured store src value store)
      (image : ∀ actual final, ClosedSourceExpressionEvaluates owner names captured store src actual final ↔
        actual = value ∧ final = store)
  | failure (kind operandDepth : Nat) (rejected : Rejected captured store src)

private def primitive? : Syntax.UnaryOp → RuntimeValue → Option RuntimeValue
  | .logicalNot,.bool b => some (.bool (!b))
  | .bitNot,.word w => some (.word w.bitNot)
  | _,_ => none

private theorem endpoint_image {captured store src value}
    (original : ClosedSourceExpressionEvaluates owner names captured store src value store) :
    ∀ actual final, ClosedSourceExpressionEvaluates owner names captured store src actual final ↔
      actual = value ∧ final = store := by
  intro actual final
  constructor
  · exact fun evaluated => evaluated.deterministic original
  · rintro ⟨rfl,rfl⟩; exact original

private theorem primitive_original {captured store operand value result}
    (span operatorSpan : Syntax.SourceSpan) (op : Syntax.UnaryOp)
    (child : ClosedSourceExpressionEvaluates owner names captured store operand value store)
    (applied : primitive? op value = some result) :
    ClosedSourceExpressionEvaluates owner names captured store
      ⟨span,.unary ⟨operatorSpan,op⟩ operand⟩ result store := by
  cases op with
  | logicalNot =>
      cases value <;> simp only [primitive?, reduceCtorEq] at applied
      cases Option.some.inj applied
      exact .logicalNot child
  | bitNot =>
      cases value <;> simp only [primitive?, reduceCtorEq] at applied
      cases Option.some.inj applied
      exact .bitNot child

private theorem primitive_image {captured store operand value result}
    (span operatorSpan : Syntax.SourceSpan) (op : Syntax.UnaryOp)
    (child : ClosedSourceExpressionEvaluates owner names captured store operand value store)
    (applied : primitive? op value = some result) :
    ∀ actual final, ClosedSourceExpressionEvaluates owner names captured store
      ⟨span,.unary ⟨operatorSpan,op⟩ operand⟩ actual final ↔ actual = result ∧ final = store := by
  cases op with
  | logicalNot =>
      cases value <;> simp only [primitive?, reduceCtorEq] at applied
      cases Option.some.inj applied
      intro actual final
      constructor
      · intro evaluated
        obtain ⟨b,ev,same⟩ := closedSourceExpressionEvaluates_logicalNot_iff.mp evaluated
        obtain ⟨sameChild,sameStore⟩ := ev.deterministic child
        cases RuntimeValue.bool.inj sameChild
        exact ⟨same,sameStore⟩
      · rintro ⟨rfl,rfl⟩
        exact closedSourceExpressionEvaluates_logicalNot_iff.mpr ⟨_,child,rfl⟩
  | bitNot =>
      cases value <;> simp only [primitive?, reduceCtorEq] at applied
      cases Option.some.inj applied
      intro actual final
      constructor
      · intro evaluated
        obtain ⟨w,ev,same⟩ := closedSourceExpressionEvaluates_bitNot_iff.mp evaluated
        obtain ⟨sameChild,sameStore⟩ := ev.deterministic child
        cases RuntimeValue.word.inj sameChild
        exact ⟨same,sameStore⟩
      · rintro ⟨rfl,rfl⟩
        exact closedSourceExpressionEvaluates_bitNot_iff.mpr ⟨_,child,rfl⟩

private theorem primitive_rejected {captured store operand value}
    (span operatorSpan : Syntax.SourceSpan) (op : Syntax.UnaryOp)
    (child : ClosedSourceExpressionEvaluates owner names captured store operand value store)
    (applied : primitive? op value = none) :
    Rejected captured store ⟨span,.unary ⟨operatorSpan,op⟩ operand⟩ := by
  intro actual final evaluated
  cases op with
  | logicalNot =>
      obtain ⟨b,ev,_⟩ := closedSourceExpressionEvaluates_logicalNot_iff.mp evaluated
      rw [← (ev.deterministic child).1] at applied
      cases applied
  | bitNot =>
      obtain ⟨w,ev,_⟩ := closedSourceExpressionEvaluates_bitNot_iff.mp evaluated
      rw [← (ev.deterministic child).1] at applied
      cases applied

private theorem child_rejected {captured store operand}
    (span operatorSpan : Syntax.SourceSpan) (op : Syntax.UnaryOp)
    (rejected : Rejected captured store operand) :
    Rejected captured store ⟨span,.unary ⟨operatorSpan,op⟩ operand⟩ := by
  intro actual final evaluated
  cases op with
  | logicalNot =>
      obtain ⟨b,ev,_⟩ := closedSourceExpressionEvaluates_logicalNot_iff.mp evaluated
      exact rejected _ _ ev
  | bitNot =>
      obtain ⟨w,ev,_⟩ := closedSourceExpressionEvaluates_bitNot_iff.mp evaluated
      exact rejected _ _ ev

private def certificate (file : Syntax.SourceFile) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (src : Syntax.Expr) : IO (Outcome captured store src) := do
  check (src.span.isValidFor file) "original expression range"
  match shape : src with
  | ⟨span,.identifier name⟩ =>
      check (span == name.span && name.span.isValidFor file) "original identifier range"
      match named : names.lookup? name.value with
      | none =>
          return .failure 0 0 (by
            intro actual final evaluated
            rw [shape] at evaluated
            cases evaluated with
            | creation impossible => cases impossible
            | reference otherNamed _ =>
                have present := LocalNameTable.lookup?_iff.mpr otherNamed
                rw [named] at present
                cases present)
      | some id => match found : captured.lookup? id with
        | none =>
            return .failure 1 0 (by
              intro actual final evaluated
              rw [shape] at evaluated
              cases evaluated with
              | creation impossible => cases impossible
              | reference otherNamed otherFound =>
                  cases (LocalNameTable.lookup?_iff.mp named).id_unique otherNamed
                  have present := Resolved.LocalScope.lookup?_iff.mpr otherFound
                  rw [found] at present
                  cases present)
        | some value =>
            have original : ClosedSourceExpressionEvaluates owner names captured store src value store := by
              rw [shape]
              exact .reference (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)
            proof original
            return .success value 1 original (endpoint_image original)
  | ⟨span,.unary op operand⟩ =>
      check (op.span.isValidFor file && span.contains operand.span && span.contains op.span &&
        op.span.length == 1 && op.span.endByte == operand.span.startByte &&
        span == Syntax.SourceSpan.cover op.span operand.span) "original unary ranges"
      check (file.content.toByteArray.data[op.span.startByte]? ==
        some (match op.value with | .logicalNot => 33 | .bitNot => 126)) "original operator byte"
      let h ← certificate file captured store operand
      match h with
      | .failure kind depth rejected =>
          return .failure kind depth (by
            rw [shape]
            exact child_rejected span op.span op.value rejected)
      | .success value depth child _ =>
          proof child
          match applied : primitive? op.value value with
          | none =>
              return .failure 2 depth (by
                rw [shape]
                exact primitive_rejected span op.span op.value child applied)
          | some result =>
              have original : ClosedSourceExpressionEvaluates owner names captured store src result store := by
                rw [shape]; exact primitive_original span op.span op.value child applied
              proof original
              match op.value with
              | .logicalNot => proof (evaluateClosedSourceExpression?_logicalNot depth owner names captured store span op.span operand)
              | .bitNot => proof (evaluateClosedSourceExpression?_bitNot depth owner names captured store span op.span operand)
              return .success result (depth+1) original (by
                rw [shape]; exact primitive_image span op.span op.value child applied)
  | _ => throw (IO.userError "unexpected boundary source shape")
termination_by sizeOf src

private def runRejected (text : String) (kind depth : Nat) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) : IO Unit := do
  let (file,src) ← parsed text
  let .failure actualKind actualDepth absent ← certificate file captured store src |
    throw (IO.userError "expected independently rejected original source")
  check (actualKind == kind && actualDepth == depth) "independent rejection fixture and operand depth"
  proof absent
  for budget in [0,1,2,3,8] do
    match result : evaluateClosedSourceExpression? budget owner names captured store src with
    | none => pure ()
    | some (actual,final) =>
        proof (absent actual final (evaluateClosedSourceExpression?_sound result))
        throw (IO.userError "relationally rejected original source completed")

private def runPositive (text : String) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (expected : Core.Value) : IO Unit := do
  let (file,src) ← parsed text
  let .success value depth original image ← certificate file captured store src |
    throw (IO.userError "expected original positive unary control")
  proof original
  check (depth == 2) "positive unary depth"
  match value,expected with
  | .bool a,.bool b => check (a == b) "positive original Bool"
  | .word a,.word b => check (a == b) "positive original Word"
  | _,_ => throw (IO.userError "positive primitive shape")
  for budget in [0,2] do
    match result : evaluateClosedSourceExpression? budget owner names captured store src with
    | none => check (budget == 0) "positive unary success2"
    | some (actual,final) =>
        check (budget == 2) "positive unary zero boundary"
        have exactImage := (image actual final).mp (evaluateClosedSourceExpression?_sound result)
        proof exactImage
        proof ((image actual final).mpr exactImage)
        proof ((image value store).mpr ⟨rfl,rfl⟩)

end Tests.ParsedClosedSourceUnaryBoundaries
open Tests.ParsedClosedSourceUnaryBoundaries in
def Tests.frontendParsedClosedSourceUnaryBoundaryTests : IO Unit := do
  let (_,inert) ← parsed "lam(){return absent;}"
  let p := Solcore.Frontend.RuntimeValue.sourceClosure inert foreign
    [("unused",fid 700)] [(fid 700,.bool true)]
  for b in [false,true] do
    for w in [Solcore.Core.Word.zero,Solcore.Core.Word.maximum,Solcore.Core.Word.ofNatModulo 17] do
      for store in stores p w do
        let captured := rows p b w
        for text in ["!word","~flag","!unit","~unit","!pair","~pair","!core","~core","!src","~src"] do
          runRejected text 2 1 captured store
        for text in ["!~word","~!flag"] do runRejected text 2 2 captured store
        for text in ["!missing","~missing"] do runRejected text 0 0 captured store
        for text in ["!lost","~lost"] do runRejected text 1 0 captured store
        runPositive "!flag" captured store (.bool (!b))
        runPositive "~word" captured store (.word w.bitNot)
end
