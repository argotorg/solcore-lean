import Solcore.Frontend.SourceComputationBody
import Solcore.Frontend.LocalReference
import Solcore.Resolved.LocalScope

/-! Independent reference callbacks exercise all nine successful original body
rules. Mixed captures and stores are unrestricted data; no closed interpreter,
static acceptance, cost, typing or Core projection is asserted. -/
set_option autoImplicit false
namespace Tests.FrontendSourceComputationBody
open Solcore Solcore.Frontend

private inductive Ref (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (environment : Resolved.LocalScope RuntimeValue) :
    List RuntimeValue → Syntax.Expr → RuntimeValue → List RuntimeValue → Prop where
  | reference {store : List RuntimeValue} {span : Syntax.SourceSpan}
      {name : Syntax.Identifier} {id : Resolved.LocalId} {value : RuntimeValue}
      (named : LocalNameTable.Lookup names name.value id)
      (found : Resolved.LocalScope.Lookup environment id value) :
      Ref owner names environment store ⟨span,.identifier name⟩ value store
private theorem refDet {o names environment store source value final other otherStore}
    (first : Ref o names environment store source value final)
    (second : Ref o names environment store source other otherStore) :
    value=other ∧ final=otherStore := by
  cases first with
  | reference named found =>
      cases second with
      | reference otherNamed otherFound =>
          cases named.id_unique otherNamed
          exact ⟨found.value_unique otherFound,rfl⟩
private def ref (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span,.identifier name⟩
private def returned (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Block :=
  ⟨span,[⟨span,.returnStmt (some (ref span name))⟩]⟩
private def spine (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation : Syntax.TypeExpr) : Nat → Syntax.Block
  | 0 => returned span name
  | n+1 => ⟨span,[⟨name.span,.letDecl name (some annotation) (some (ref span name))⟩,
      ⟨name.span,.letDecl name none (some (ref span name))⟩,
      ⟨span,.expression (ref span name) true⟩,
      ⟨span,.block (spine span name annotation n).value⟩]⟩
private theorem spinePath (o : Resolved.DeclarationId) (span : Syntax.SourceSpan)
    (name : Syntax.Identifier) (annotation : Syntax.TypeExpr) (n : Nat)
    (names : LocalNameTable) (environment : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup environment id value) :
    SourceComputationBodyEvaluates Ref o names environment store
      (spine span name annotation n) value store := by
  induction n generalizing names environment id with
  | zero => exact .expression (.reference named found)
  | succ n ih =>
      apply SourceComputationBodyEvaluates.binding (.reference named found)
      apply SourceComputationBodyEvaluates.inferred (.reference .head .head)
      apply SourceComputationBodyEvaluates.discard (.reference .head .head)
      cases n <;> exact .block (ih _ _ _ .head .head)

private def wrap : List Syntax.SourceSpan → Syntax.Pattern → Syntax.Pattern
  | [],pattern => pattern
  | outer::rest,pattern => ⟨outer,.group (wrap rest pattern)⟩
private theorem wrapped {pattern : Syntax.Pattern} {tag : Option Core.Word}
    (meaning : WordMatchPatternClassifies pattern tag) (groups : List Syntax.SourceSpan) :
    WordMatchPatternClassifies (wrap groups pattern) tag := by
  induction groups with | nil => exact meaning | cons _ _ ih => exact .group ih
private def zeroCase (span : Syntax.SourceSpan) (groups : List Syntax.SourceSpan)
    (body : Syntax.Block) : Syntax.MatchCase :=
  ⟨span,⟨wrap groups ⟨span,.literal ⟨span,.decimal "0"⟩⟩,body⟩⟩
private def wildCase (span marker : Syntax.SourceSpan) (groups : List Syntax.SourceSpan)
    (body : Syntax.Block) : Syntax.MatchCase := ⟨span,⟨wrap groups ⟨span,.wildcard marker⟩,body⟩⟩
private theorem zeroMeaning (span : Syntax.SourceSpan) (groups : List Syntax.SourceSpan)
    (body : Syntax.Block) :
    WordMatchPatternClassifies (zeroCase span groups body).value.pattern (some .zero) :=
  wrapped (.literal ⟨⟨span,.decimal "0"⟩,rfl,
    .decimal (by decide) (.cons (.decimal (digit := 0) (by decide) rfl) .nil)⟩) groups
private def misses (span : Syntax.SourceSpan) (groups : Nat → List Syntax.SourceSpan)
    (unused : Syntax.Block) : Nat → List Syntax.MatchCase → List Syntax.MatchCase
  | 0,tail => tail
  | n+1,tail => zeroCase span (groups n) unused :: misses span groups unused n tail
private def one : Core.Word := ⟨1,by decide⟩
private theorem prefixChoice (span marker : Syntax.SourceSpan)
    (groups : Nat → List Syntax.SourceSpan) (wildGroups : List Syntax.SourceSpan)
    (unused selected : Syntax.Block) (suffix : List Syntax.MatchCase)
    (defaultBody : Option Syntax.Block) (n : Nat) :
    RuntimeWordMatchChooses (.word one)
      (misses span groups unused n (wildCase span marker wildGroups selected :: suffix))
      defaultBody selected n := by
  induction n with
  | zero => exact .wildcard (wrapped (.wildcard rfl) wildGroups)
  | succ n ih => exact .miss (zeroMeaning _ _ _) (by decide) ih
private def matched (span : Syntax.SourceSpan) (scrutinee : Syntax.Expr)
    (cases : List Syntax.MatchCase) (defaultBody : Option Syntax.Block) : Syntax.Block :=
  ⟨span,[⟨span,.matchWith ⟨span,⟨scrutinee,[]⟩⟩ ⟨span,⟨cases,defaultBody⟩⟩⟩]⟩

theorem arbitrary_shadow_depth_preserves_actual_mixed_payload
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation : Syntax.TypeExpr) (n : Nat) (names : LocalNameTable)
    (environment : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup environment id value) :
    SourceComputationBodyEvaluates Ref o names environment store
      (spine span name annotation n) value store := spinePath o span name annotation n _ _ _ _ _ named found

theorem actual_body_result_and_store_are_unique
    {o names environment store body value final other otherStore}
    (first : SourceComputationBodyEvaluates Ref o names environment store body value final)
    (second : SourceComputationBodyEvaluates Ref o names environment store body other otherStore) :
    value=other ∧ final=otherStore := SourceComputationBodyEvaluates.deterministic refDet first second

theorem strict_discard_then_bare_return_keeps_arbitrary_raw_store
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (names : LocalNameTable) (environment : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (id : Resolved.LocalId) (actual : RuntimeValue)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup environment id actual) :
    SourceComputationBodyEvaluates Ref o names environment store
      ⟨span,[⟨span,.expression (ref span name) true⟩,⟨span,.returnStmt none⟩]⟩ .unit store :=
  .discard (.reference named found) .bare

theorem actual_bool_selects_only_its_original_branch
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (condition name : Syntax.Identifier)
    (annotation : Syntax.TypeExpr) (n : Nat) (side : Bool) (unused : Syntax.Block)
    (names : LocalNameTable) (environment : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (conditionId id : Resolved.LocalId) (value : RuntimeValue)
    (conditionNamed : LocalNameTable.Lookup names condition.value conditionId)
    (conditionFound : Resolved.LocalScope.Lookup environment conditionId (.bool side))
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup environment id value) :
    SourceComputationBodyEvaluates Ref o names environment store
      ⟨span,[⟨span,.ifThen (ref span condition)
        (if side then spine span name annotation n else unused)
        (some (if side then unused else spine span name annotation n))⟩]⟩ value store := by
  cases side
  · exact .ifFalse (.reference conditionNamed conditionFound) (spinePath _ _ _ _ _ _ _ _ _ _ named found)
  · exact .ifTrue (.reference conditionNamed conditionFound) (spinePath _ _ _ _ _ _ _ _ _ _ named found)

theorem first_literal_hit_ignores_arbitrary_original_suffix
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (groups : List Syntax.SourceSpan)
    (scrutinee name : Syntax.Identifier) (suffix : List Syntax.MatchCase) (defaultBody : Option Syntax.Block)
    (names : LocalNameTable) (environment : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (scrutineeId id : Resolved.LocalId) (value : RuntimeValue)
    (scrutineeNamed : LocalNameTable.Lookup names scrutinee.value scrutineeId)
    (scrutineeFound : Resolved.LocalScope.Lookup environment scrutineeId (.word .zero))
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup environment id value) :
    RuntimeWordMatchChooses (.word .zero) (zeroCase span groups (returned span name)::suffix)
      defaultBody (returned span name) 1 ∧
    WordMatchChooses (.word .zero) (zeroCase span groups (returned span name)::suffix)
      defaultBody (returned span name) 1 ∧
    SourceComputationBodyEvaluates Ref o names environment store
      (matched span (ref span scrutinee) (zeroCase span groups (returned span name)::suffix) defaultBody) value store := by
  have choice : RuntimeWordMatchChooses (.word .zero)
      (zeroCase span groups (returned span name)::suffix) defaultBody (returned span name) 1 :=
    .hit (zeroMeaning _ _ _)
  have original := runtimeWordMatchChooses_ofCore_iff.mp
    (show RuntimeWordMatchChooses (RuntimeValue.ofCore (.word .zero)) _ _ _ _ from
      by simpa only [RuntimeValue.ofCore] using choice)
  exact ⟨choice,original,.wordMatch (.reference scrutineeNamed scrutineeFound)
    choice (.expression (.reference named found))⟩

theorem arbitrary_literal_misses_then_grouped_wildcard
    (o : Resolved.DeclarationId) (span marker : Syntax.SourceSpan)
    (groups : Nat → List Syntax.SourceSpan) (wildGroups : List Syntax.SourceSpan)
    (scrutinee name : Syntax.Identifier) (annotation : Syntax.TypeExpr) (n depth : Nat)
    (unused : Syntax.Block) (suffix : List Syntax.MatchCase) (defaultBody : Option Syntax.Block)
    (names : LocalNameTable) (environment : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (scrutineeId id : Resolved.LocalId) (value : RuntimeValue)
    (scrutineeNamed : LocalNameTable.Lookup names scrutinee.value scrutineeId)
    (scrutineeFound : Resolved.LocalScope.Lookup environment scrutineeId (.word one))
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup environment id value) :
    let selected := spine span name annotation depth
    let cases := misses span groups unused n (wildCase span marker wildGroups selected :: suffix)
    RuntimeWordMatchChooses (.word one) cases defaultBody selected n ∧
    SourceComputationBodyEvaluates Ref o names environment store
      (matched span (ref span scrutinee) cases defaultBody) value store :=
  ⟨prefixChoice _ _ _ _ _ _ _ _ _,.wordMatch (.reference scrutineeNamed scrutineeFound)
    (prefixChoice _ _ _ _ _ _ _ _ _) (spinePath _ _ _ _ _ _ _ _ _ _ named found)⟩

theorem default_only_accepts_every_actual_scrutinee
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (scrutinee name : Syntax.Identifier)
    (names : LocalNameTable) (environment : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (scrutineeId id : Resolved.LocalId) (actual value : RuntimeValue)
    (scrutineeNamed : LocalNameTable.Lookup names scrutinee.value scrutineeId)
    (scrutineeFound : Resolved.LocalScope.Lookup environment scrutineeId actual)
    (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup environment id value) :
    SourceComputationBodyEvaluates Ref o names environment store
      (matched span (ref span scrutinee) [] (some (returned span name))) value store :=
  .wordMatch (.reference scrutineeNamed scrutineeFound) .fallback (.expression (.reference named found))

theorem selected_original_block_and_count_are_jointly_unique
    {actual cases defaultBody selected other tests otherTests}
    (first : RuntimeWordMatchChooses actual cases defaultBody selected tests)
    (second : RuntimeWordMatchChooses actual cases defaultBody other otherTests) :
    selected=other ∧ tests=otherTests := first.deterministic second

theorem duplicate_capture_and_environment_only_fresh_collision_remain_literal
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotation : Syntax.TypeExpr) (n : Nat) (names : LocalNameTable)
    (tail : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (id : Resolved.LocalId) (actual ignored collision : RuntimeValue) :
    let rows := (id,actual)::(id,ignored)::
      (Resolved.freshLocalId o (((name.value,id)::names).map Prod.snd),collision)::tail
    SourceComputationBodyEvaluates Ref o ((name.value,id)::names) rows store
      (spine span name annotation n) actual store :=
  spinePath _ _ _ _ _ _ _ _ _ _ .head .head

theorem the_same_original_conditional_runs_with_both_actual_boolean_rows
    (o : Resolved.DeclarationId) (span : Syntax.SourceSpan) (annotation : Syntax.TypeExpr)
    (n : Nat) (side : Bool) (conditionId valueId : Resolved.LocalId) (different : conditionId≠valueId)
    (names : LocalNameTable) (tail : Resolved.LocalScope RuntimeValue)
    (actual : RuntimeValue) (store : List RuntimeValue) :
    SourceComputationBodyEvaluates Ref o (("c",conditionId)::("x",valueId)::names)
      ((conditionId,.bool side)::(valueId,actual)::tail) store
      ⟨span,[⟨span,.ifThen (ref span ⟨span,"c"⟩)
        (spine span ⟨span,"x"⟩ annotation n)
        (some (spine span ⟨span,"x"⟩ annotation (n+1)))⟩]⟩ actual store := by
  cases side
  · exact .ifFalse (.reference .head .head)
      (spinePath _ _ _ _ _ _ _ _ _ _ (.tail (by change "c" ≠ "x"; decide) .head) (.tail different .head))
  · exact .ifTrue (.reference .head .head)
      (spinePath _ _ _ _ _ _ _ _ _ _ (.tail (by change "c" ≠ "x"; decide) .head) (.tail different .head))

end Tests.FrontendSourceComputationBody
