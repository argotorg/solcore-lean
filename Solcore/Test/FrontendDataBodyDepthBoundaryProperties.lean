import Solcore.Frontend.ClosedSource

/- Original constructor evidence and independent ordered selection come first.
All lexical tails, mixed captures and actual stores remain unrestricted.
Visited literal comparisons are not recursive body-search depth. -/
set_option autoImplicit false
namespace Tests.DataBodyDepthBoundaries
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def ref (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr := ⟨s,.identifier name⟩
private def bare (s : Syntax.SourceSpan) : Syntax.Block := ⟨s,[⟨s,.returnStmt none⟩]⟩
private def output (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Block :=
  ⟨s,[⟨s,.returnStmt (some (ref s name))⟩]⟩
private def arm (s : Syntax.SourceSpan) (p : Syntax.Pattern) (b : Syntax.Block) : Syntax.MatchCase := ⟨s,⟨p,b⟩⟩
private def matching (s : Syntax.SourceSpan) (key : Syntax.Identifier)
    (cases : List Syntax.MatchCase) (fallback : Option Syntax.Block) : Syntax.Block :=
  ⟨s,[⟨s,.matchWith ⟨s,⟨ref s key,[]⟩⟩ ⟨s,⟨cases,fallback⟩⟩⟩]⟩
private def badPattern (s : Syntax.SourceSpan) (stringPattern : Bool) : Syntax.Pattern :=
  if stringPattern then ⟨s,.literal ⟨s,.string "bad"⟩⟩ else ⟨s,.error⟩
private def Failed (o : Resolved.DeclarationId) (n : LocalNameTable)
    (e : Resolved.LocalScope RuntimeValue) (st : List RuntimeValue) (b : Syntax.Block) : Prop :=
  ClosedSourceDataBody b ∧
  evaluateClosedSourceBody? (closedSourceDataBodyDepthBound b) o n e st b = none ∧
  (∀ budget, evaluateClosedSourceBody? budget o n e st b = none) ∧
  ∀ value final, ¬ B o n e st b value final
variable (s : Syntax.SourceSpan) (o : Resolved.DeclarationId) (n : LocalNameTable)
  (e : Resolved.LocalScope RuntimeValue) (st : List RuntimeValue)

private theorem reject (b : Syntax.Block) (gate : ClosedSourceDataBody b)
    (original : ∀ value final, ¬ B o n e st b value final) : Failed o n e st b := by
  have absent := (gate.evaluate_depth_none_iff o n e st (Nat.le_refl _)).mpr original
  exact ⟨gate,absent,(gate.evaluate_depth_none_iff_all_budgets o n e st).mp absent,
    (gate.evaluate_depth_none_iff o n e st (Nat.le_refl _)).mp absent⟩
private theorem missing_ref {s o n e st value final name}
    (missing : LocalNameTable.lookup? n name.value = none) : ¬ E o n e st (ref s name) value final := by
  intro evaluated
  cases evaluated with
  | reference named _ =>
      have accepted := LocalNameTable.lookup?_iff.mpr named
      rw [missing] at accepted; cases accepted
  | creation shape => cases shape

theorem missing_initializers_and_discards (name binder : Syntax.Identifier)
    (annotation : Option Syntax.TypeExpr) (missing : LocalNameTable.lookup? n name.value = none) :
    Failed o n e st ⟨s,[⟨s,.letDecl binder annotation (some (ref s name))⟩,⟨s,.returnStmt none⟩]⟩ ∧
    Failed o n e st ⟨s,[⟨s,.expression (ref s name) true⟩,⟨s,.returnStmt none⟩]⟩ := by
  constructor
  · apply reject o n e st _ (.binding .reference .bare)
    intro value final evaluated
    cases evaluated with
    | binding child _ => exact missing_ref missing child
    | inferred child _ => exact missing_ref missing child
  · apply reject o n e st _ (.discard .reference .bare)
    intro value final evaluated
    cases evaluated with | discard child _ => exact missing_ref missing child

theorem selected_conditional_missing_branch (key name : Syntax.Identifier) (id : Resolved.LocalId)
    (choice : Bool) (named : LocalNameTable.Lookup n key.value id)
    (found : Resolved.LocalScope.Lookup e id (.bool choice))
    (missing : LocalNameTable.lookup? n name.value = none) :
    let source : Syntax.Block := ⟨s,[⟨s,.ifThen (ref s key)
      (if choice then output s name else bare s)
      (some (if choice then bare s else output s name))⟩]⟩
    E o n e st (ref s key) (.bool choice) st ∧ Failed o n e st source := by
  intro source
  have guard : E o n e st (ref s key) (.bool choice) st := .reference named found
  have gate : ClosedSourceDataBody source := by
    cases choice with
    | false => exact .conditional .reference .bare (.expression .reference)
    | true => exact .conditional .reference (.expression .reference) .bare
  refine ⟨guard,reject o n e st source gate ?_⟩
  intro value final evaluated
  dsimp only [source] at evaluated
  cases evaluated with
  | ifTrue tested branch =>
      have same := RuntimeValue.bool.inj (guard.deterministic tested).1
      subst choice
      cases branch with | expression child => exact missing_ref missing child
  | ifFalse tested branch =>
      have same := RuntimeValue.bool.inj (guard.deterministic tested).1
      subst choice
      cases branch with | expression child => exact missing_ref missing child

theorem first_duplicate_non_bool_guard_never_falls_back
    (first later : Resolved.LocalId) (bad : RuntimeValue) (notBool : ∀ b, bad ≠ .bool b) :
    let names := ("c",first)::("c",later)::n
    let captured := (first,bad)::(first,.bool true)::(later,.bool false)::e
    let key : Syntax.Identifier := ⟨s,"c"⟩
    E o names captured st (ref s key) bad st ∧
    Failed o names captured st ⟨s,[⟨s,.ifThen (ref s key) (bare s) (some (bare s))⟩]⟩ := by
  dsimp only
  have head : E o (("c",first)::("c",later)::n)
      ((first,bad)::(first,.bool true)::(later,.bool false)::e) st (ref s ⟨s,"c"⟩) bad st := .reference .head .head
  refine ⟨head,reject o _ _ st _ (.conditional .reference .bare .bare) ?_⟩
  intro value final evaluated
  cases evaluated with
  | ifTrue tested _ => exact notBool true (head.deterministic tested).1
  | ifFalse tested _ => exact notBool false (head.deterministic tested).1

private theorem reject_selection (key : Syntax.Identifier) (actual : RuntimeValue)
    (cases : List Syntax.MatchCase) (fallback : Option Syntax.Block)
    (gate : ClosedSourceDataBody (matching s key cases fallback))
    (original : E o n e st (ref s key) actual st)
    (absent : chooseRuntimeWordMatch? actual cases fallback = none) :
    Failed o n e st (matching s key cases fallback) := by
  apply reject o n e st _ gate
  intro value final evaluated
  cases evaluated with
  | wordMatch tested choice _ =>
      obtain ⟨rfl,rfl⟩ := tested.deterministic original
      have accepted := chooseRuntimeWordMatch?_iff.mpr choice
      rw [absent] at accepted; cases accepted
private theorem bad_unclassified (flag : Bool) : interpretWordMatchPattern? (badPattern s flag) = none := by
  cases flag <;> simp [badPattern,interpretWordMatchPattern?,interpretWordLiteral?,numericLiteralValue?]

theorem invalid_pattern_and_empty_cases_do_not_escape_to_default
    (key : Syntax.Identifier) (id : Resolved.LocalId) (actual : RuntimeValue) (stringPattern : Bool)
    (named : LocalNameTable.Lookup n key.value id) (found : Resolved.LocalScope.Lookup e id actual) :
    E o n e st (ref s key) actual st ∧
    Failed o n e st (matching s key [arm s (badPattern s stringPattern) (bare s)] (some (bare s))) ∧
    Failed o n e st (matching s key [] none) := by
  have original : E o n e st (ref s key) actual st := .reference named found
  refine ⟨original,?_,?_⟩
  · apply reject_selection s o n e st key actual _ _ _ original
      (by simp only [chooseRuntimeWordMatch?,arm,bad_unclassified])
    refine .wordMatch .reference ?_ ?_
    · intro a h; rcases List.mem_singleton.mp h with rfl; exact .bare
    · intro b h; simp only [Option.toList_some,List.mem_singleton] at h; subst b; exact .bare
  · exact reject_selection s o n e st key actual [] none
      (.wordMatch .reference (by intro a h; cases h) (by intro b h; cases h)) original rfl

theorem a_literal_miss_reaches_invalid_pattern_before_default
    (key : Syntax.Identifier) (id : Resolved.LocalId) (word literal : Core.Word)
    (pattern : Syntax.Pattern) (meaning : WordMatchPatternClassifies pattern (some literal))
    (different : word ≠ literal) (stringPattern : Bool)
    (named : LocalNameTable.Lookup n key.value id) (found : Resolved.LocalScope.Lookup e id (.word word)) :
    E o n e st (ref s key) (.word word) st ∧
    Failed o n e st (matching s key
      [arm s pattern (bare s),arm s (badPattern s stringPattern) (bare s)] (some (bare s))) := by
  have original : E o n e st (ref s key) (.word word) st := .reference named found
  refine ⟨original,reject_selection s o n e st key (.word word) _ _ ?_ original ?_⟩
  · refine .wordMatch .reference ?_ ?_
    · intro a h; simp only [List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with rfl | rfl <;> exact .bare
    · intro b h; simp only [Option.toList_some,List.mem_singleton] at h; subst b; exact .bare
  · simp only [chooseRuntimeWordMatch?,arm,interpretWordMatchPattern?_iff.mpr meaning,
      different,↓reduceIte,bad_unclassified,Option.map_none]

private def deepStatement (s : Syntax.SourceSpan) : Nat → Syntax.Statement
  | 0 => ⟨s,.returnStmt (some ⟨s,.literal ⟨s,.string "bad"⟩⟩)⟩
  | k+1 => ⟨s,.block [deepStatement s k]⟩
private def deep (s : Syntax.SourceSpan) (k : Nat) : Syntax.Block := ⟨s,[deepStatement s k]⟩
private theorem deep_gate (k : Nat) : ClosedSourceDataBody (deep s k) := by
  induction k with | zero => exact .expression .literal | succ _ ih => exact .block ih
private theorem deep_bound (k : Nat) : closedSourceDataBodyDepthBound (deep s k) = k+2 := by
  induction k with
  | zero => simp [deep,deepStatement,closedSourceDataBodyDepthBound,closedSourceDataDepthBound]
  | succ k ih => simpa only [deep,deepStatement,closedSourceDataBodyDepthBound,Nat.add_assoc] using congrArg (·+1) ih
private theorem deep_original_absent (k : Nat) : ∀ value final, ¬ B o n e st (deep s k) value final := by
  induction k with
  | zero =>
      intro value final evaluated
      cases evaluated with
      | expression child =>
          cases child with | wordLiteral meaning => cases meaning | creation shape => cases shape
  | succ k ih =>
      intro value final evaluated
      cases evaluated with | block child => exact ih _ _ child

theorem early_match_skips_deep_bad_arms_with_nonminimal_bound
    (key : Syntax.Identifier) (id : Resolved.LocalId) (actual : RuntimeValue)
    (firstPattern : Syntax.Pattern) (tag : Option Core.Word)
    (meaning : WordMatchPatternClassifies firstPattern tag)
    (compatible : ∀ word, tag=some word → actual = .word word)
    (named : LocalNameTable.Lookup n key.value id) (found : Resolved.LocalScope.Lookup e id actual)
    (k extra : Nat) :
    let skipped := deep s (k+1)
    let cases := [arm s firstPattern (bare s),arm s (badPattern s true) skipped]
    let source := matching s key cases (some skipped)
    let comparisons := if tag.isSome then 1 else 0
    RuntimeWordMatchChooses actual cases (some skipped) (bare s) comparisons ∧
    chooseRuntimeWordMatch? actual cases (some skipped) = some (bare s,comparisons) ∧
    ClosedSourceDataBody source ∧ closedSourceDataBodyDepthBound source = k+4 ∧
    B o n e st source .unit st ∧
    (∀ value final, ¬ B o n e st skipped value final) ∧
    evaluateClosedSourceBody? 2 o n e st source = some (.unit,st) ∧
    evaluateClosedSourceBody? (closedSourceDataBodyDepthBound source-1) o n e st source = some (.unit,st) ∧
    evaluateClosedSourceBody? (closedSourceDataBodyDepthBound source+extra) o n e st source = some (.unit,st) ∧
    (∀ value final budget, closedSourceDataBodyDepthBound source ≤ budget →
      (evaluateClosedSourceBody? budget o n e st source = some (value,final) ↔ value=.unit ∧ final=st)) := by
  intro skipped cases source comparisons
  have tested : E o n e st (ref s key) actual st := .reference named found
  have choice : RuntimeWordMatchChooses actual cases (some skipped) (bare s) comparisons := by
    cases tag with
    | none => exact .wildcard meaning
    | some word => rw [compatible word rfl]; exact .hit meaning
  have original : B o n e st source .unit st := .wordMatch tested choice .bare
  have skippedGate : ClosedSourceDataBody skipped := deep_gate s _
  have gate : ClosedSourceDataBody source := by
    refine .wordMatch .reference ?_ ?_
    · intro a h; simp only [cases,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl
      · exact .bare
      · exact skippedGate
    · intro b h; simp only [Option.toList_some,List.mem_singleton] at h; subst b; exact skippedGate
  have bound : closedSourceDataBodyDepthBound source = k+4 := by
    simp only [source,matching,closedSourceDataBodyDepthBound,ref,closedSourceDataDepthBound,
      cases,closedSourceDataMatchDepthBound,arm,bare,skipped,deep_bound]
    omega
  have early : evaluateClosedSourceBody? 2 o n e st source = some (.unit,st) := by
    have selected := chooseRuntimeWordMatch?_iff.mpr choice
    simp only [source,matching,evaluateClosedSourceBody?,ref,evaluateClosedSourceExpression?,
      LocalNameTable.lookup?_iff.mpr named,Resolved.LocalScope.lookup?_iff.mpr found,
      bind,pure,Option.bind_some,selected,bare]
  refine ⟨choice,chooseRuntimeWordMatch?_iff.mpr choice,gate,bound,original,
    deep_original_absent s o n e st _,early,evaluateClosedSourceBody?_monotone (by omega) early,
    gate.evaluates_at_depthBound original (by omega),?_⟩
  intro value final budget enough
  rw [gate.evaluate_at_depthBound_iff enough]
  exact ⟨fun other => other.deterministic original,by rintro ⟨rfl,rfl⟩; exact original⟩

end Tests.DataBodyDepthBoundaries
