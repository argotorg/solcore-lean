import Solcore.Frontend.Fragments.Internal.ClosedSource
import Solcore.Test.Frontend.ExpectedDataImages
import Solcore.Test.Frontend.ClosedStrictWords
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.Fragments.Internal.LambdaDepth

/-!
# Data depth and self-application tests

Data depth boundaries with their symbolic proofs and parsed bridge, the boundaries of data bodies, and
self-application.
-/

section
-- leanmerge: from Solcore.Test.FrontendDataBodyDepthBoundaryProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendDataDepthBoundaryProperties
/- Original rejection and child witnesses precede the finite-depth decision laws.
Mixed stores and duplicate lexical/runtime rows are unrestricted throughout.
Zero assigned to unsupported syntax is not a bound for successful source calls. -/
set_option autoImplicit false
namespace Tests.DataDepthBoundaries
open Solcore Solcore.Frontend

private def ref (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨s,.identifier name⟩
private def bin (s opSpan : Syntax.SourceSpan) (op : Syntax.BinaryOp)
    (left right : Syntax.Expr) : Syntax.Expr := ⟨s,.binary left ⟨opSpan,op⟩ right⟩
private def Failed (o : Resolved.DeclarationId) (n : LocalNameTable)
    (e : Resolved.LocalScope RuntimeValue) (st : List RuntimeValue) (x : Syntax.Expr) : Prop :=
  evaluateClosedSourceExpression? (closedSourceDataDepthBound x) o n e st x = none ∧
  (∀ budget, evaluateClosedSourceExpression? budget o n e st x = none) ∧
  ∀ value final, ¬ ClosedSourceExpressionEvaluates o n e st x value final

variable (owner : Resolved.DeclarationId) (names : LocalNameTable)
  (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)

private theorem reject (x : Syntax.Expr) (gate : ClosedSourceDataExpression x)
    (original : ∀ value final, ¬ ClosedSourceExpressionEvaluates owner names captured store x value final) :
    Failed owner names captured store x := by
  have absence := (gate.evaluate_depth_none_iff owner names captured store (Nat.le_refl _)).mpr original
  exact ⟨absence,(gate.evaluate_depth_none_iff_all_budgets owner names captured store).mp absence,
    (gate.evaluate_depth_none_iff owner names captured store (Nat.le_refl _)).mp absence⟩

theorem missing_name_or_capture_at_every_depth (s : Syntax.SourceSpan) (name : Syntax.Identifier)
    (missing : LocalNameTable.lookup? names name.value = none ∨
      ∃ id, LocalNameTable.Lookup names name.value id ∧ Resolved.LocalScope.lookup? captured id = none) :
    ClosedSourceDataExpression (ref s name) ∧ closedSourceDataDepthBound (ref s name) = 1 ∧
    Failed owner names captured store (ref s name) := by
  have original : ∀ value final, ¬ ClosedSourceExpressionEvaluates owner names captured store (ref s name) value final := by
    intro value final evaluated
    cases evaluated with
    | reference named found =>
        rcases missing with absent | ⟨id,correct,absent⟩
        · have accepted := LocalNameTable.lookup?_iff.mpr named
          rw [absent] at accepted; cases accepted
        · cases named.id_unique correct
          have accepted := Resolved.LocalScope.lookup?_iff.mpr found
          rw [absent] at accepted; cases accepted
    | creation shape => cases shape
  exact ⟨.reference,by simp [ref,closedSourceDataDepthBound],reject owner names captured store _ .reference original⟩

theorem missing_first_capture_never_uses_a_later_duplicate
    (s : Syntax.SourceSpan) (first later : Resolved.LocalId) (different : later ≠ first)
    (word : Core.Word) (missing : Resolved.LocalScope.lookup? captured first = none) :
    let n := ("x",first)::("x",later)::names
    let e := (later,.word word)::captured
    ClosedSourceDataExpression (ref s ⟨s,"x"⟩) ∧
    closedSourceDataDepthBound (ref s ⟨s,"x"⟩) = 1 ∧
    Failed owner n e store (ref s ⟨s,"x"⟩) := by
  dsimp only
  have absent : Resolved.LocalScope.lookup? ((later,RuntimeValue.word word)::captured) first = none := by
    simp only [Resolved.LocalScope.lookup?,if_neg different,missing]
  exact missing_name_or_capture_at_every_depth owner _ _ store s ⟨s,"x"⟩
    (.inr ⟨first,.head,absent⟩)

theorem strings_at_every_depth (s : Syntax.SourceSpan) (text : String) :
    ClosedSourceDataExpression ⟨s,.literal ⟨s,.string text⟩⟩ ∧
    closedSourceDataDepthBound ⟨s,.literal ⟨s,.string text⟩⟩ = 1 ∧
    Failed owner names captured store ⟨s,.literal ⟨s,.string text⟩⟩ := by
  have original : ∀ value final, ¬ ClosedSourceExpressionEvaluates owner names captured store
      ⟨s,.literal ⟨s,.string text⟩⟩ value final := by
    intro value final evaluated
    cases evaluated with
    | wordLiteral meaning => cases meaning
    | creation shape => cases shape
  exact ⟨.literal,by simp [closedSourceDataDepthBound],reject owner names captured store _ .literal original⟩

theorem overflow_at_every_depth (s : Syntax.SourceSpan) (literal : Syntax.CoreLiteral)
    (natural : Nat) (meaning : NumericLiteralDenotes literal.value natural)
    (overflow : Core.wordModulus ≤ natural) :
    ClosedSourceDataExpression ⟨s,.literal literal⟩ ∧
    closedSourceDataDepthBound ⟨s,.literal literal⟩ = 1 ∧
    Failed owner names captured store ⟨s,.literal literal⟩ := by
  have original : ∀ value final, ¬ ClosedSourceExpressionEvaluates owner names captured store
      ⟨s,.literal literal⟩ value final := by
    intro value final evaluated
    cases evaluated with
    | @wordLiteral _ _ _ _ _ _ word wordMeaning =>
        have same := NumericLiteralDenotes.value_unique meaning wordMeaning
        have small := word.isLt
        omega
    | creation shape => cases shape
  exact ⟨.literal,by simp [closedSourceDataDepthBound],reject owner names captured store _ .literal original⟩

theorem actual_modulus_spelling_at_every_depth (s : Syntax.SourceSpan) :
    let literal : Syntax.CoreLiteral :=
      ⟨s,.hexadecimal "0x10000000000000000000000000000000000000000000000000000000000000000"⟩
    NumericLiteralDenotes literal.value Core.wordModulus ∧
    ClosedSourceDataExpression ⟨s,.literal literal⟩ ∧
    closedSourceDataDepthBound ⟨s,.literal literal⟩ = 1 ∧
    Failed owner names captured store ⟨s,.literal literal⟩ := by
  dsimp only
  have natural : NumericLiteralDenotes
      (.hexadecimal "0x10000000000000000000000000000000000000000000000000000000000000000")
      Core.wordModulus := numericLiteralValue?_sound (by decide)
  exact ⟨natural,overflow_at_every_depth owner names captured store s _ _ natural (Nat.le_refl _)⟩

theorem non_word_on_either_side_at_every_depth
    (s opSpan goodSpan badSpan : Syntax.SourceSpan) (op : Syntax.BinaryOp)
    (notAnd : op ≠ .logicalAnd) (notOr : op ≠ .logicalOr)
    (goodName badName : Syntax.Identifier) (goodId badId : Resolved.LocalId)
    (word : Core.Word) (bad : RuntimeValue) (notWord : ∀ w, bad ≠ .word w)
    (goodNamed : LocalNameTable.Lookup names goodName.value goodId)
    (badNamed : LocalNameTable.Lookup names badName.value badId)
    (goodFound : Resolved.LocalScope.Lookup captured goodId (.word word))
    (badFound : Resolved.LocalScope.Lookup captured badId bad) :
    let left := bin s opSpan op (ref badSpan badName) (ref goodSpan goodName)
    let right := bin s opSpan op (ref goodSpan goodName) (ref badSpan badName)
    ClosedSourceExpressionEvaluates owner names captured store (ref goodSpan goodName) (.word word) store ∧
    ClosedSourceExpressionEvaluates owner names captured store (ref badSpan badName) bad store ∧
    ClosedSourceDataExpression left ∧ ClosedSourceDataExpression right ∧
    closedSourceDataDepthBound left = 2 ∧ closedSourceDataDepthBound right = 2 ∧
    Failed owner names captured store left ∧ Failed owner names captured store right := by
  dsimp only
  obtain ⟨lg,rg,good,badRun,original⟩ := StrictWordDataBoundary.admitted_non_word_operands_still_never_succeed
    owner names captured store s opSpan goodSpan badSpan op notAnd notOr
    goodName badName goodId badId word bad notWord goodNamed badNamed goodFound badFound
  exact ⟨good,badRun,lg,rg,by simp [bin,ref,closedSourceDataDepthBound],by simp [bin,ref,closedSourceDataDepthBound],
    reject owner names captured store _ lg (fun v st => (original v st).1),
    reject owner names captured store _ rg (fun v st => (original v st).2)⟩

theorem duplicate_first_non_word_hides_later_word
    (s : Syntax.SourceSpan) (first later : Resolved.LocalId) (word : Core.Word)
    (bad : RuntimeValue) (notWord : ∀ w, bad ≠ .word w) :
    let n := ("x",first)::("x",later)::names
    let e := (first,bad)::(first,.word word)::(later,.word word)::captured
    let x := ref s ⟨s,"x"⟩
    ClosedSourceExpressionEvaluates owner n e store x bad store ∧
    ClosedSourceDataExpression (bin s s .multiply x x) ∧
    Failed owner n e store (bin s s .multiply x x) := by
  dsimp only
  have head : ClosedSourceExpressionEvaluates owner (("x",first)::("x",later)::names)
      ((first,bad)::(first,.word word)::(later,.word word)::captured) store (ref s ⟨s,"x"⟩) bad store :=
    .reference .head .head
  have gate : ClosedSourceDataExpression (bin s s .multiply (ref s ⟨s,"x"⟩) (ref s ⟨s,"x"⟩)) :=
    .strictWordBinary .reference .reference (by decide) (by decide)
  refine ⟨head,gate,reject owner _ _ store _ gate ?_⟩
  intro actual final evaluated
  obtain ⟨lw,_,_,_,_,left,_,_⟩ :=
    (closedSourceExpressionEvaluates_strictWordBinary_iff (by decide) (by decide)).mp evaluated
  exact notWord lw (head.deterministic left).1

theorem zero_still_needs_both_operands_at_every_depth
    (s opSpan zeroSpan missingSpan : Syntax.SourceSpan) (op : Syntax.BinaryOp)
    (notAnd : op ≠ .logicalAnd) (notOr : op ≠ .logicalOr)
    (zeroName missingName : Syntax.Identifier) (zeroId : Resolved.LocalId)
    (zeroNamed : LocalNameTable.Lookup names zeroName.value zeroId)
    (zeroFound : Resolved.LocalScope.Lookup captured zeroId (.word Core.Word.zero))
    (missing : LocalNameTable.lookup? names missingName.value = none ∨
      ∃ id, LocalNameTable.Lookup names missingName.value id ∧ Resolved.LocalScope.lookup? captured id = none) :
    let left := bin s opSpan op (ref zeroSpan zeroName) (ref missingSpan missingName)
    let right := bin s opSpan op (ref missingSpan missingName) (ref zeroSpan zeroName)
    ClosedSourceExpressionEvaluates owner names captured store (ref zeroSpan zeroName) (.word Core.Word.zero) store ∧
    ClosedSourceDataExpression left ∧ ClosedSourceDataExpression right ∧
    closedSourceDataDepthBound left = 2 ∧ closedSourceDataDepthBound right = 2 ∧
    Failed owner names captured store left ∧ Failed owner names captured store right := by
  dsimp only
  obtain ⟨lg,rg,zero,original⟩ := StrictWordDataBoundary.admitted_zero_never_skips_a_missing_operand
    owner names captured store s opSpan zeroSpan missingSpan op notAnd notOr
    zeroName missingName zeroId zeroNamed zeroFound missing
  exact ⟨zero,lg,rg,by simp [bin,ref,closedSourceDataDepthBound],by simp [bin,ref,closedSourceDataDepthBound],
    reject owner names captured store _ lg (fun v st => (original v st).1),
    reject owner names captured store _ rg (fun v st => (original v st).2)⟩

private def body (s : Syntax.SourceSpan) : Syntax.Block :=
  ⟨s,[⟨s,.returnStmt (some (ref s ⟨s,"p"⟩))⟩]⟩
private def identity (s : Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s,.lambda s ⟨s,[⟨s,.inferred ⟨s,"p"⟩⟩]⟩ none (body s)⟩
private def applied (s : Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s,.call (identity s) ⟨s,[⟨s,.tuple ⟨s,[]⟩⟩]⟩⟩

theorem zero_for_unsupported_shapes_does_not_decide_success (s : Syntax.SourceSpan) :
    let closure := RuntimeValue.sourceClosure (identity s) owner names captured
    closedSourceDataDepthBound (identity s) = 0 ∧ closedSourceDataDepthBound (applied s) = 0 ∧
    (¬ ClosedSourceDataExpression (identity s)) ∧ (¬ ClosedSourceDataExpression (applied s)) ∧
    ClosedSourceExpressionEvaluates owner names captured store (identity s) closure store ∧
    ClosedSourceExpressionEvaluates owner names captured store (applied s) .unit store ∧
    evaluateClosedSourceExpression? (closedSourceDataDepthBound (identity s)) owner names captured store (identity s) = none ∧
    evaluateClosedSourceExpression? (closedSourceDataDepthBound (applied s)) owner names captured store (applied s) = none ∧
    evaluateClosedSourceExpression? 1 owner names captured store (identity s) = some (closure,store) ∧
    evaluateClosedSourceExpression? 3 owner names captured store (applied s) = some (.unit,store) := by
  dsimp only
  have created : ClosedSourceExpressionEvaluates owner names captured store (identity s)
      (.sourceClosure (identity s) owner names captured) store := .creation .inferred
  have argument : ClosedSourceExpressionEvaluates owner names captured store ⟨s,.tuple ⟨s,[]⟩⟩ .unit store := .unit
  have beta : ClosedSourceBodyEvaluates owner
      (("p",Resolved.freshLocalId owner (names.map Prod.snd))::names)
      ((Resolved.freshLocalId owner (names.map Prod.snd),.unit)::captured) store (body s) .unit store :=
    .expression (.reference .head .head)
  have called : ClosedSourceExpressionEvaluates owner names captured store (applied s) .unit store :=
    .call .inferred created argument beta
  refine ⟨by simp [identity,closedSourceDataDepthBound],by simp [applied,closedSourceDataDepthBound],
    (by intro g; cases g),(by intro g; cases g),created,called,
    by simp [identity,closedSourceDataDepthBound,evaluateClosedSourceExpression?],
    by simp [applied,closedSourceDataDepthBound,evaluateClosedSourceExpression?],?_,?_⟩
  · simp only [identity,evaluateClosedSourceExpression?,sourceUnaryLambdaShape?,bind,Option.bind_some,pure]
  · simp [applied,identity,body,ref,evaluateClosedSourceExpression?,evaluateClosedSourceBody?,
      sourceUnaryLambdaShape?,LocalNameTable.lookup?,Resolved.LocalScope.lookup?]

end Tests.DataDepthBoundaries
end

section
-- leanmerge: from Solcore.Test.FrontendDataDepthSymbolicProperties
/- Independent original witnesses precede every new bounded-search law.
Arbitrary mixed values, first-match rows, source ranges and whole stores stay literal. -/
set_option autoImplicit false
namespace Tests.DataDepthSymbolic
open Solcore Solcore.Frontend

private def groups (span : Syntax.SourceSpan) : Nat → Syntax.Expr → Syntax.Expr
  | 0, source => source
  | n + 1, source => ⟨span, .group (groups span n source)⟩
private def reference (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span, .identifier name⟩
private def tupleSource (span tupleSpan : Syntax.SourceSpan) (child : Syntax.Expr) (n : Nat) : Syntax.Expr :=
  ⟨span, .tuple ⟨tupleSpan, List.replicate (n + 2) child⟩⟩
private def tupleValue (value : RuntimeValue) : Nat → RuntimeValue
  | 0 => .pair value value
  | n + 1 => .pair value (tupleValue value n)

private theorem groups_bound (span : Syntax.SourceSpan) (n : Nat) (source : Syntax.Expr) :
    closedSourceDataDepthBound (groups span n source) = closedSourceDataDepthBound source + n := by
  induction n with
  | zero => simp only [groups, Nat.add_zero]
  | succ n ih => simp only [groups, closedSourceDataDepthBound, ih]; omega

private theorem groups_syntax {source : Syntax.Expr} (admitted : ClosedSourceDataExpression source)
    (span : Syntax.SourceSpan) (n : Nat) : ClosedSourceDataExpression (groups span n source) := by
  induction n with
  | zero => exact admitted
  | succ _ ih => exact .group ih

private theorem groups_original {owner names captured initialStore finalStore source value}
    (original : ClosedSourceExpressionEvaluates owner names captured initialStore source value finalStore)
    (span : Syntax.SourceSpan) (n : Nat) :
    ClosedSourceExpressionEvaluates owner names captured initialStore (groups span n source) value finalStore := by
  induction n with
  | zero => exact original
  | succ _ ih => exact .group ih

private theorem groups_before (span : Syntax.SourceSpan) (n budget : Nat) (source : Syntax.Expr)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (small : budget ≤ n) :
    evaluateClosedSourceExpression? budget owner names captured store (groups span n source) = none := by
  induction n generalizing budget with
  | zero =>
      have same : budget = 0 := by omega
      subst budget
      simp only [evaluateClosedSourceExpression?]
  | succ n ih =>
      cases budget with
      | zero => simp only [evaluateClosedSourceExpression?]
      | succ budget => simpa only [groups, evaluateClosedSourceExpression?] using ih budget (by omega)

private theorem tuple_bound (span tupleSpan : Syntax.SourceSpan) (child : Syntax.Expr) (n : Nat) :
    closedSourceDataDepthBound (tupleSource span tupleSpan child n) =
      closedSourceDataDepthBound child + n + 1 := by
  induction n with
  | zero => simp only [tupleSource, List.replicate_succ, List.replicate_zero,
      closedSourceDataDepthBound, Nat.max_self, Nat.add_zero]
  | succ n ih =>
      change closedSourceDataDepthBound
        ⟨span, .tuple ⟨tupleSpan, child :: child :: child :: List.replicate n child⟩⟩ = _
      rw [closedSourceDataDepthBound]
      change max (closedSourceDataDepthBound child)
        (closedSourceDataDepthBound (tupleSource span tupleSpan child n)) + 1 = _
      rw [ih]; omega

private theorem tuple_original {owner names captured store child value}
    (original : ClosedSourceExpressionEvaluates owner names captured store child value store)
    (span tupleSpan : Syntax.SourceSpan) (n : Nat) :
    ClosedSourceExpressionEvaluates owner names captured store
      (tupleSource span tupleSpan child n) (tupleValue value n) store := by
  induction n with
  | zero => exact .pair original original
  | succ n ih => exact .many original ih

private theorem tuple_syntax {child : Syntax.Expr} (admitted : ClosedSourceDataExpression child)
    (span tupleSpan : Syntax.SourceSpan) (n : Nat) :
    ClosedSourceDataExpression (tupleSource span tupleSpan child n) := by
  induction n with
  | zero => exact .pair admitted admitted
  | succ _ ih => exact .many admitted ih

private theorem tuple_before (span tupleSpan groupSpan : Syntax.SourceSpan) (n k budget : Nat)
    (source : Syntax.Expr) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (small : budget ≤ n + k + 1) :
    evaluateClosedSourceExpression? budget owner names captured store
      (tupleSource span tupleSpan (groups groupSpan k source) n) = none := by
  induction n generalizing budget store with
  | zero =>
      cases budget with
      | zero => simp only [evaluateClosedSourceExpression?]
      | succ budget =>
          have absent := groups_before groupSpan k budget source owner names captured store (by omega)
          simp only [tupleSource, List.replicate_succ, List.replicate_zero,
            evaluateClosedSourceExpression?, absent, bind, Option.bind_none]
  | succ n ih =>
      cases budget with
      | zero => simp only [evaluateClosedSourceExpression?]
      | succ budget =>
          cases head : evaluateClosedSourceExpression? budget owner names captured store
              (groups groupSpan k source) with
          | none => simp only [tupleSource, List.replicate_succ,
              evaluateClosedSourceExpression?, head, bind, Option.bind_none]
          | some endpoint =>
              obtain ⟨headValue, middleStore⟩ := endpoint
              have tail := ih budget middleStore (by omega)
              simp only [tupleSource, List.replicate_succ] at tail
              simp only [tupleSource, List.replicate_succ,
                evaluateClosedSourceExpression?, head, bind, Option.bind_some, tail, Option.bind_none]

/-- Every group depth and original tuple arity has a sharp source-depth boundary. -/
theorem groups_and_original_many_tuples (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (spans : Fin 4 → Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (value : RuntimeValue) (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id value) (n k extra : Nat) :
    let leaf := groups (spans 0) k (reference (spans 1) name)
    let source := tupleSource (spans 2) (spans 3) leaf n
    ClosedSourceExpressionEvaluates owner names captured store leaf value store ∧
    ClosedSourceExpressionEvaluates owner names captured store source (tupleValue value n) store ∧
    closedSourceDataDepthBound leaf = k + 1 ∧ closedSourceDataDepthBound source = n + k + 2 ∧
    evaluateClosedSourceExpression? k owner names captured store leaf = none ∧
    evaluateClosedSourceExpression? (n + k + 1) owner names captured store source = none ∧
    evaluateClosedSourceExpression? (k + 1) owner names captured store leaf = some (value, store) ∧
    evaluateClosedSourceExpression? (n + k + 2) owner names captured store source = some (tupleValue value n, store) ∧
    evaluateClosedSourceExpression? (n + k + 2 + extra) owner names captured store source =
      some (tupleValue value n, store) := by
  dsimp only
  have original : ClosedSourceExpressionEvaluates owner names captured store
      (groups (spans 0) k (reference (spans 1) name)) value store :=
    groups_original (.reference named found) (spans 0) k
  have whole := tuple_original original (spans 2) (spans 3) n
  have leafGate := groups_syntax (ClosedSourceDataExpression.reference (span := spans 1) (name := name)) (spans 0) k
  have gate := tuple_syntax leafGate (spans 2) (spans 3) n
  have leafBound : closedSourceDataDepthBound (groups (spans 0) k (reference (spans 1) name)) = k + 1 := by
    rw [groups_bound]; simp only [reference, closedSourceDataDepthBound]; omega
  have wholeBound : closedSourceDataDepthBound
      (tupleSource (spans 2) (spans 3) (groups (spans 0) k (reference (spans 1) name)) n) = n + k + 2 := by
    rw [tuple_bound, leafBound]; omega
  simp only [reference] at leafBound wholeBound
  refine ⟨original, whole, leafBound, wholeBound, groups_before _ _ _ _ _ _ _ _ (Nat.le_refl _),
    tuple_before _ _ _ _ _ _ _ _ _ _ _ (Nat.le_refl _),
    leafGate.evaluates_at_depthBound original (by omega),
    gate.evaluates_at_depthBound whole (by omega), gate.evaluates_at_depthBound whole (by omega)⟩

private def outcomes (left right : Core.Word) : List (Syntax.BinaryOp × Core.Value) :=
  [(.add, .word (left.add right)), (.subtract, .word (left.sub right)),
   (.multiply, .word (left.mul right)), (.divide, .word (left.udiv right)),
   (.modulo, .word (left.umod right)), (.bitAnd, .word (left.bitAnd right)),
   (.bitOr, .word (left.bitOr right)), (.bitXor, .word (left.bitXor right)),
   (.greater, .bool (decide (left > right))), (.less, .bool (decide (left < right))),
   (.equal, .bool (left == right)), (.notEqual, .bool (!(left == right))),
   (.lessEqual, .bool (!(decide (left > right)))), (.greaterEqual, .bool (!(decide (left < right))))]

/-- All fourteen independent old original witnesses consume the new bound and actual-output iff. -/
theorem all_fourteen_strict_at_bound (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (spans : Fin 4 → Syntax.SourceSpan) (leftName rightName : Syntax.Identifier)
    (leftId rightId : Resolved.LocalId) (leftWord rightWord : Core.Word)
    (leftNamed : LocalNameTable.Lookup names leftName.value leftId)
    (rightNamed : LocalNameTable.Lookup names rightName.value rightId)
    (leftFound : Resolved.LocalScope.Lookup captured leftId (.word leftWord))
    (rightFound : Resolved.LocalScope.Lookup captured rightId (.word rightWord)) :
    ∀ operator result, (operator, result) ∈ outcomes leftWord rightWord →
    let source : Syntax.Expr := ⟨spans 0, .binary (reference (spans 2) leftName) ⟨spans 1, operator⟩
      (reference (spans 3) rightName)⟩
    ClosedSourceExpressionEvaluates owner names captured store source (RuntimeValue.ofCore result) store ∧
    closedSourceDataDepthBound source = 2 ∧
    (∀ extra, evaluateClosedSourceExpression? (2 + extra) owner names captured store source =
      some (RuntimeValue.ofCore result, store)) ∧
    (∀ actual final extra, evaluateClosedSourceExpression? (2 + extra) owner names captured store source =
      some (actual, final) ↔ actual = RuntimeValue.ofCore result ∧ final = store) := by
  intro operator result member source
  obtain ⟨original, exactResult, gate⟩ := ClosedStrictWordBinarySymbolic.all_fourteen_original_and_exact_actual_results
    owner names captured store spans leftName rightName leftId rightId leftWord rightWord
    leftNamed rightNamed leftFound rightFound operator result member
  have bound : closedSourceDataDepthBound source = 2 := by
    simp only [source, reference, closedSourceDataDepthBound, Nat.max_self]
  refine ⟨original, bound, ?_, ?_⟩
  · intro extra; exact gate.evaluates_at_depthBound original (by change closedSourceDataDepthBound source ≤ _; omega)
  · intro actual final extra
    exact (gate.evaluate_at_depthBound_iff (by change closedSourceDataDepthBound source ≤ _; omega)).trans
      (exactResult actual final)

private def short (span operatorSpan : Syntax.SourceSpan) (useOr : Bool) (left right : Syntax.Expr) : Syntax.Expr :=
  ⟨span, .binary left ⟨operatorSpan, if useOr then .logicalOr else .logicalAnd⟩ right⟩

/-- Selected right values can be arbitrary mixed payloads, with every actual endpoint retained. -/
theorem selected_short_circuit_mixed_values (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (spans : Fin 4 → Syntax.SourceSpan) (leftName rightName : Syntax.Identifier)
    (leftId rightId : Resolved.LocalId) (useOr : Bool) (value : RuntimeValue)
    (leftNamed : LocalNameTable.Lookup names leftName.value leftId)
    (rightNamed : LocalNameTable.Lookup names rightName.value rightId)
    (leftFound : Resolved.LocalScope.Lookup captured leftId (.bool (!useOr)))
    (rightFound : Resolved.LocalScope.Lookup captured rightId value) :
    let source := short (spans 0) (spans 1) useOr (reference (spans 2) leftName) (reference (spans 3) rightName)
    ClosedSourceExpressionEvaluates owner names captured store source value store ∧
    (∀ actual final extra, evaluateClosedSourceExpression? (2 + extra) owner names captured store source =
      some (actual, final) ↔ actual = value ∧ final = store) := by
  intro source
  have left : ClosedSourceExpressionEvaluates owner names captured store
      (reference (spans 2) leftName) (.bool (!useOr)) store := .reference leftNamed leftFound
  have right : ClosedSourceExpressionEvaluates owner names captured store
      (reference (spans 3) rightName) value store := .reference rightNamed rightFound
  have original : ClosedSourceExpressionEvaluates owner names captured store source value store := by
    cases useOr with
    | false => exact .andTrue left right
    | true => exact .orFalse left right
  have gate : ClosedSourceDataExpression source := by
    cases useOr with
    | false => exact .logicalAnd .reference .reference
    | true => exact .logicalOr .reference .reference
  have bound : closedSourceDataDepthBound source = 2 := by
    simp only [source, short, reference, closedSourceDataDepthBound, Nat.max_self]
  refine ⟨original, ?_⟩
  intro actual final extra
  rw [gate.evaluate_at_depthBound_iff (by omega : closedSourceDataDepthBound source ≤ 2 + extra)]
  exact ⟨fun result => result.deterministic original, fun ⟨rfl, rfl⟩ => original⟩

/-- Arbitrarily deep unvisited string data increases the bound, not the necessary depth. -/
theorem skipped_deep_data_bound_is_not_minimal (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (spans : Fin 5 → Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (useOr : Bool) (spelling : String) (n extra : Nat)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id (.bool useOr)) :
    let ignored := groups (spans 3) (n + 1) ⟨spans 4, .literal ⟨spans 4, .string spelling⟩⟩
    let source := short (spans 0) (spans 1) useOr (reference (spans 2) name) ignored
    ClosedSourceDataExpression source ∧ closedSourceDataDepthBound source = n + 3 ∧
    ClosedSourceExpressionEvaluates owner names captured store source (.bool useOr) store ∧
    evaluateClosedSourceExpression? 2 owner names captured store source = some (.bool useOr, store) ∧
    evaluateClosedSourceExpression? (closedSourceDataDepthBound source - 1)
      owner names captured store source = some (.bool useOr, store) ∧
    evaluateClosedSourceExpression? (closedSourceDataDepthBound source + extra)
      owner names captured store source = some (.bool useOr, store) := by
  intro ignored source
  have left : ClosedSourceExpressionEvaluates owner names captured store
      (reference (spans 2) name) (.bool useOr) store := .reference named found
  have original : ClosedSourceExpressionEvaluates owner names captured store source (.bool useOr) store := by
    cases useOr with
    | false => exact .andFalse left
    | true => exact .orTrue left
  have ignoredGate : ClosedSourceDataExpression ignored := groups_syntax .literal _ _
  have gate : ClosedSourceDataExpression source := by
    cases useOr with
    | false => exact .logicalAnd .reference ignoredGate
    | true => exact .logicalOr .reference ignoredGate
  have bound : closedSourceDataDepthBound source = n + 3 := by
    dsimp only [source, short]; rw [closedSourceDataDepthBound]
    simp only [reference, closedSourceDataDepthBound, ignored, groups_bound]; omega
  have early : evaluateClosedSourceExpression? 2 owner names captured store source = some (.bool useOr, store) := by
    cases useOr <;> simp only [source, short, reference, Bool.false_eq_true, ↓reduceIte,
      evaluateClosedSourceExpression?, LocalNameTable.lookup?_iff.mpr named,
      Resolved.LocalScope.lookup?_iff.mpr found, bind, Option.bind_some, pure]
  exact ⟨gate, bound, original, early, evaluateClosedSourceExpression?_monotone (by omega) early,
    gate.evaluates_at_depthBound original (by omega)⟩

end Tests.DataDepthSymbolic
end

section
-- leanmerge: from Solcore.Test.FrontendParsedDataDepthBridge
/- Two actual parsed trees exercise original right-associated many tails and a
deep unselected missing branch. Independent raw constructor witnesses come first.
Depth is a sufficient source-search bound, not a minimum or a Core transition cost.
Duplicate lexical/captured rows, arbitrary mixed payloads and entire stores remain. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Tests.ParsedDataDepthBridge
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev E := ClosedSourceExpressionEvaluates
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ParsedDataDepth",by decide⟩],by decide⟩⟩,302⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=903},700⟩
private def names : LocalNameTable :=
  [("x",sid 7),("c",sid 3),("y",sid 8),("z",foreign),("x",sid 99),("c",sid 99)]
private def rows (guard p q r : V) (tail : Resolved.LocalScope V) :=
  [(sid 8,q),(sid 7,p),(sid 3,guard),(foreign,r),(sid 7,.unit),
    (sid 3,.word Core.Word.maximum)] ++ tail
private def span (f : Syntax.SourceFile) (a b : Nat) : Syntax.SourceSpan := ⟨f.id,a,b⟩
private def ref (f : Syntax.SourceFile) (a b : Nat) (n : String) : Syntax.Expr :=
  ⟨span f a b,.identifier ⟨span f a b,n⟩⟩
private def tupleAST (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f 0 10,.tuple ⟨span f 0 10,[ref f 1 2 "x",⟨span f 3 5,.tuple ⟨span f 3 5,[]⟩⟩,
    ref f 6 7 "y",ref f 8 9 "z"]⟩⟩
private def conditionalAST (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f 0 21,.conditional (ref f 0 1 "c") (span f 2 3) (ref f 4 5 "x") (span f 6 7)
    ⟨span f 8 21,.group ⟨span f 9 20,.group ⟨span f 10 19,.group (ref f 11 18 "missing")⟩⟩⟩⟩
private def actualSpans : Syntax.Expr → List Syntax.SourceSpan
  | ⟨s,.tuple ⟨t,[⟨x,.identifier ⟨xn,_⟩⟩,⟨u,.tuple ⟨ut,[]⟩⟩,
      ⟨y,.identifier ⟨yn,_⟩⟩,⟨z,.identifier ⟨zn,_⟩⟩]⟩⟩ => [s,t,x,xn,u,ut,y,yn,z,zn]
  | ⟨s,.conditional ⟨c,.identifier ⟨cn,_⟩⟩ qu ⟨x,.identifier ⟨xn,_⟩⟩ co
      ⟨a,.group ⟨b,.group ⟨d,.group ⟨m,.identifier ⟨mn,_⟩⟩⟩⟩⟩⟩ => [s,c,cn,qu,x,xn,co,a,b,d,m,mn]
  | _ => []
private def parsed (text : String) (expected : Syntax.SourceFile → Syntax.Expr)
    (ranges : List (Nat × Nat)) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"parsed-data-depth.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "data depth lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok src next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && next.file==file &&
      src.span==Syntax.SourceSpan.fullFile file && src==expected file) "whole handwritten AST / EOF / zero diagnostics"
    check ((actualSpans src).all (fun s => s.isValidFor file) &&
      (actualSpans src).map (fun s => (s.startByte,s.endByte))==ranges) "all actual node/name/delimiter/operator spans"
    return src
  | _ => throw (IO.userError "data depth parser")
private structure Cert (captured : Resolved.LocalScope V) (store : List V) (src : Syntax.Expr) (value : V) : Type where
  gate : ClosedSourceDataExpression src
  original : E owner names captured store src value store
private def reference (captured : Resolved.LocalScope V) (store : List V) (src : Syntax.Expr)
    (spelling : String) (id : Resolved.LocalId) (value : V)
    (named : LocalNameTable.Lookup names spelling id) (found : Resolved.LocalScope.Lookup captured id value) :
    IO (Cert captured store src value) := do
  match shape : src with
  | ⟨_,.identifier name⟩ =>
    if h : name.value=spelling then
      return by rw [shape]; exact ⟨.reference,.reference (h ▸ named) found⟩
    else throw (IO.userError "actual identifier spelling")
  | _ => throw (IO.userError "actual reference")
private def tupleWitness (src : Syntax.Expr) (guard p q r : V)
    (tail : Resolved.LocalScope V) (store : List V) :
    IO (Cert (rows guard p q r tail) store src (.pair p (.pair .unit (.pair q r)))) := do
  let captured := rows guard p q r tail
  match shape : src with
  | ⟨_,.tuple ⟨_,[x,⟨_,.tuple ⟨_,[]⟩⟩,y,z]⟩⟩ =>
    let hx ← reference captured store x "x" (sid 7) p .head (.tail (by decide) .head)
    let hy ← reference captured store y "y" (sid 8) q
      (.tail (by decide) (.tail (by decide) .head)) .head
    let hz ← reference captured store z "z" foreign r
      (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
    return by rw [shape]; exact ⟨.many hx.gate (.many .unit (.pair hy.gate hz.gate)),
      .many hx.original (.many .unit (.pair hy.original hz.original))⟩
  | _ => throw (IO.userError "original flat four-tuple and right-associated tail")
private theorem endpoints {captured store src value}
    (original : E owner names captured store src value store) (a : V) (st : List V) :
    E owner names captured store src a st ↔ a=value ∧ st=store :=
  ⟨fun other => other.deterministic original,by rintro ⟨rfl,rfl⟩; exact original⟩
private def successful {captured store src value} (h : Cert captured store src value)
    (selectedDepth expectedBound : Nat) : IO Unit := do
  proof h.original
  let bound := closedSourceDataDepthBound src
  check (bound==expectedBound) "actual source-only depth counts right tuple tails and both branches"
  have atBound := h.gate.evaluates_at_depthBound h.original (Nat.le_refl bound)
  have allHigh : ∀ n, bound≤n → evaluateClosedSourceExpression? n owner names captured store src =
      some (value,store) := fun _ enough => h.gate.evaluates_at_depthBound h.original enough
  proof atBound; proof allHigh
  for budget in [0,selectedDepth-1,selectedDepth,bound-1,bound,bound+3] do
    match run : evaluateClosedSourceExpression? budget owner names captured store src with
    | none => check (budget<selectedDepth) "only lower selected-path depth fails for witnessed success"
    | some (actual,finalStore) =>
      have original := evaluateClosedSourceExpression?_sound run
      have equal := (endpoints h.original actual finalStore).mp original
      proof equal; proof ((endpoints h.original actual finalStore).mpr equal)
      check (selectedDepth≤budget) "complete actual value and final store proved without a mixed-value comparison"
      if enough : bound≤budget then
        proof ((h.gate.evaluate_at_depthBound_iff enough).mp run)
        proof ((h.gate.evaluate_at_depthBound_iff enough).mpr original)
        proof (h.gate.evaluate_depth_stable owner names captured store enough)
      if below : budget<bound then
        proof (show ∃ n, n<bound ∧ evaluateClosedSourceExpression? n owner names captured store src =
          some (actual,finalStore) from ⟨budget,below,run⟩)
  for extra in [0,1,7] do
    have stable := h.gate.evaluate_depth_stable owner names captured store (Nat.le_add_right bound extra)
    proof stable
    match high : evaluateClosedSourceExpression? (bound+extra) owner names captured store src with
    | none => False.elim (by
        have accepted := allHigh (bound+extra) (Nat.le_add_right bound extra)
        rw [high] at accepted; cases accepted)
    | some (actual,finalStore) =>
      proof (show evaluateClosedSourceExpression? bound owner names captured store src =
        some (actual,finalStore) from stable.symm.trans high)
private def rejected {captured store src} (gate : ClosedSourceDataExpression src)
    (directNone : evaluateClosedSourceExpression? (closedSourceDataDepthBound src)
      owner names captured store src = none) : IO Unit := do
  proof directNone
  have absent := (gate.evaluate_depth_none_iff owner names captured store (Nat.le_refl _)).mp directNone
  have allBudgets := (gate.evaluate_depth_none_iff_all_budgets owner names captured store).mp directNone
  proof absent; proof allBudgets
  proof ((gate.evaluate_depth_none_iff owner names captured store (Nat.le_refl _)).mpr absent)
  proof ((gate.evaluate_depth_none_iff_all_budgets owner names captured store).mpr allBudgets)
  let bound := closedSourceDataDepthBound src
  for budget in [0,1,bound-1,bound,bound+7] do
    proof (allBudgets budget)
    check ((evaluateClosedSourceExpression? budget owner names captured store src).isNone) "selected failure at every tested budget"
  have stable := gate.evaluate_depth_stable owner names captured store (Nat.le_add_right bound 7)
  proof stable
  check ((evaluateClosedSourceExpression? (bound+7) owner names captured store src).isNone &&
    (evaluateClosedSourceExpression? bound owner names captured store src).isNone) "proved whole Option stability also preserves none"
private def conditionalCase (src : Syntax.Expr) (p q r : V)
    (tail : Resolved.LocalScope V) (store : List V) : IO Unit := do
  match shape : src with
  | ⟨_,.conditional c _ x _ ⟨_,.group ⟨_,.group ⟨_,.group ⟨_,.identifier ⟨_,"missing"⟩⟩⟩⟩⟩⟩ =>
    let captured := rows (.bool true) p q r tail
    let hc ← reference captured store c "c" (sid 3) (.bool true)
      (.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head))
    let hx ← reference captured store x "x" (sid 7) p .head (.tail (by decide) .head)
    have cert : Cert captured store src p := by
      rw [shape]; exact ⟨.conditional hc.gate hx.gate (.group (.group (.group .reference))),
        .conditionalTrue hc.original hx.original⟩
    successful cert 2 5
    match cShape : c, xShape : x with
    | ⟨_,.identifier ⟨_,"c"⟩⟩, ⟨_,.identifier ⟨_,"x"⟩⟩ =>
      have missing : evaluateClosedSourceExpression? (closedSourceDataDepthBound src)
          owner names (rows (.bool false) p q r tail) store src = none := by
        rw [shape,cShape,xShape]
        simp [closedSourceDataDepthBound,evaluateClosedSourceExpression?,names,rows,
          LocalNameTable.lookup?,Resolved.LocalScope.lookup?,sid,owner,foreign]
      have wrong : evaluateClosedSourceExpression? (closedSourceDataDepthBound src)
          owner names (rows (.word Core.Word.maximum) p q r tail) store src = none := by
        rw [shape,cShape,xShape]
        simp [closedSourceDataDepthBound,evaluateClosedSourceExpression?,names,rows,
          LocalNameTable.lookup?,Resolved.LocalScope.lookup?,sid,owner,foreign]
      rejected cert.gate missing
      rejected cert.gate wrong
    | _,_ => throw (IO.userError "actual Bool guard and selected payload identifiers")
  | _ => throw (IO.userError "original conditional and deep missing branch")
end Tests.ParsedDataDepthBridge
open Solcore Solcore.Frontend Tests.ParsedDataDepthBridge in
def Tests.frontendParsedDataDepthBridgeTests : IO Unit := do
  let tuple ← parsed "(x,(),y,z)" tupleAST
    [(0,10),(0,10),(1,2),(1,2),(3,5),(3,5),(6,7),(6,7),(8,9),(8,9)]
  let conditional ← parsed "c ? x : (((missing)))" conditionalAST
    [(0,21),(0,1),(0,1),(2,3),(4,5),(4,5),(6,7),(8,21),(9,20),(10,19),(11,18),(11,18)]
  let inert := tuple
  let saved := RuntimeValue.sourceClosure inert foreign.owner [("x",foreign),("x",sid 7)]
    [(foreign,.unit),(foreign,.word Core.Word.maximum)]
  let inertCore := RuntimeValue.ofCore (.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700])
  let mut count := 0
  for p in [saved,RuntimeValue.pair (.word Core.Word.maximum) saved] do
    for tail in [[],[(sid 7,inertCore),(sid 3,.unit),(foreign,saved)]] do
      for store in [[],[saved,inertCore,RuntimeValue.hostFunction .storageWrite,RuntimeValue.cellRef (.function .word .word) 900]] do
        let witness ← tupleWitness tuple (.bool false) p inertCore saved tail store
        successful witness 4 4
        conditionalCase conditional p inertCore saved tail store
        count := count+4
  check (count==32) "two spellings / eight mixed contexts / success and both selected failure lanes"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedSelfApplication
/- Separate actual source occurrences create finite closures with literal saved fields.
Successful child runs precede exact self-reentry non-return laws. Identity and
false short-circuit controls succeed; None alone is not a fault/divergence classifier. -/
set_option autoImplicit false
namespace Tests.ParsedSelfApplication
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner (n : Nat) : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ParsedSelf",by decide⟩],by decide⟩⟩,n⟩
private def so := owner 310
private def co := owner 910
private def sid (n : Nat) : Resolved.LocalId := ⟨so,n⟩
private def cid (n : Nat) : Resolved.LocalId := ⟨co,n⟩
private def sn : LocalNameTable := [("q",sid 8),("r",sid 9),("q",sid 99),("r",sid 99),("x",cid 70)]
private def se (core other : V) : Resolved.LocalScope V :=
  [(sid 8,core),(sid 8,other),(sid 9,other),(sid 99,.unit),(sid 100,core),(cid 70,.cellRef .word 700)]
private def cn : LocalNameTable := [("f",cid 1),("x",cid 2),("a",cid 3),("f",cid 99),("x",cid 99)]
private def ce (saved other : V) : Resolved.LocalScope V :=
  [(cid 1,saved),(cid 1,other),(cid 2,saved),(cid 2,other),(cid 3,.bool false),(cid 99,other)]
private def span (f : Syntax.SourceFile) (a b : Nat) : Syntax.SourceSpan := ⟨f.id,a,b⟩
private def ref (f : Syntax.SourceFile) (a b : Nat) (n : String) : Syntax.Expr := ⟨span f a b,.identifier ⟨span f a b,n⟩⟩
private def expectedLambda (typed loop : Bool) (k : Nat) (name : String) (f : Syntax.SourceFile) : Syntax.Expr :=
  let t := if typed then 5 else 0
  let b := k+6+t
  let stop := b+(if loop then 14 else 11)
  let parameter : Syntax.LambdaParameter := if typed then
    ⟨span f (k+4) (k+10),.typed none ⟨span f (k+4) (k+5),name⟩
      ⟨span f (k+6) (k+10),.named ⟨span f (k+6) (k+10),⟨⟨⟨span f (k+6) (k+10),"Word"⟩,[]⟩⟩⟩ none⟩⟩
    else ⟨span f (k+4) (k+5),.inferred ⟨span f (k+4) (k+5),name⟩⟩
  let child := if loop then ⟨span f (b+8) (b+12),.call (ref f (b+8) (b+9) name)
    ⟨span f (b+9) (b+12),[ref f (b+10) (b+11) name]⟩⟩ else ref f (b+8) (b+9) name
  ⟨span f k stop,.lambda (span f k (k+3)) ⟨span f (k+3) (k+6+t),[parameter]⟩ none
    ⟨span f b stop,[⟨span f (b+1) (stop-1),.returnStmt (some child)⟩]⟩⟩
private def expectedWhole (lt rt loop : Bool) (f : Syntax.SourceFile) : Syntax.Expr :=
  let k := (if loop then 21 else 18)+(if lt then 5 else 0)
  let stop := k+21+(if rt then 5 else 0)
  ⟨span f 0 stop,.call (expectedLambda lt loop 0 "q" f)
    ⟨span f (k-1) stop,[expectedLambda rt true k "r" f]⟩⟩
private def expectedCall (k : Nat) (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f k (k+4),.call (ref f k (k+1) "f") ⟨span f (k+1) (k+4),[ref f (k+2) (k+3) "x"]⟩⟩
private def expectedShort (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f 0 9,.binary (ref f 0 1 "a") ⟨span f 2 4,.logicalAnd⟩ (expectedCall 5 f)⟩
private def parameterSpans : Syntax.LambdaParameter → List Syntax.SourceSpan
  | ⟨s,.inferred n⟩ => [s,n.span]
  | ⟨s,.typed none n ⟨t,.named ⟨q,⟨⟨i,[]⟩⟩⟩ none⟩⟩ => [s,n.span,t,q,i.span]
  | _ => []
private def spans : Syntax.Expr → List Syntax.SourceSpan
  | ⟨s,.identifier n⟩ => [s,n.span]
  | ⟨s,.call f ⟨a,[x]⟩⟩ => [s]++spans f++[a]++spans x
  | ⟨s,.binary l op r⟩ => [s]++spans l++[op.span]++spans r
  | ⟨s,.lambda k ⟨ps,[p]⟩ none ⟨b,[⟨r,.returnStmt (some e)⟩]⟩⟩ => [s,k,ps]++parameterSpans p++[b,r]++spans e
  | _ => []
private def lambdaRanges (typed loop : Bool) (k : Nat) : List (Nat × Nat) :=
  let t := if typed then 5 else 0
  let b := k+6+t
  let stop := b+(if loop then 14 else 11)
  [(k,stop),(k,k+3),(k+3,k+6+t),(k+4,k+5+t),(k+4,k+5)]++
    (if typed then [(k+6,k+10),(k+6,k+10),(k+6,k+10)] else [])++[(b,stop),(b+1,stop-1)]++
    (if loop then [(b+8,b+12),(b+8,b+9),(b+8,b+9),(b+9,b+12),(b+10,b+11),(b+10,b+11)]
      else [(b+8,b+9),(b+8,b+9)])
private def parsed (text : String) (ast : Syntax.SourceFile → Syntax.Expr) (ranges : List (Nat × Nat)) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"parsed-self.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "self lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok actual next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && next.file==file &&
      actual.span==Syntax.SourceSpan.fullFile file && actual==ast file) "whole handwritten AST / EOF / zero diagnostics"
    check ((spans actual).all (fun s => s.isValidFor file) &&
      (spans actual).map (fun s => (s.startByte,s.endByte))==ranges) "every actual source occurrence/name/type span"
    return actual
  | _ => throw (IO.userError "self parser")
private structure LC (source : Syntax.Expr) where
  name : Syntax.Identifier
  body : Syntax.Block
  shape : SourceUnaryLambdaShape source name body
private def lambda (source : Syntax.Expr) : IO (LC source) := do
  match h : source with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred name⟩]⟩ _ body⟩ => return ⟨name,body,by rw [h]; exact .inferred⟩
  | ⟨_,.lambda _ ⟨_,[⟨_,.typed none name _⟩]⟩ _ body⟩ => return ⟨name,body,by rw [h]; exact .typed⟩
  | _ => throw (IO.userError "actual unary shape")
private def selfBody (name : Syntax.Identifier) (body : Syntax.Block) : IO (PLift (SourceSelfApplicationBody body name)) := do
  match h : body with
  | ⟨_,[⟨_,.returnStmt (some ⟨_,.call ⟨_,.identifier f⟩ ⟨_,[⟨_,.identifier x⟩]⟩⟩)⟩]⟩ =>
    if same : f.value=name.value ∧ x.value=name.value then return ⟨by rw [h]; exact .returning same.1 same.2⟩
    else throw (IO.userError "actual self reference spellings")
  | _ => throw (IO.userError "actual self body")
private structure Created (o : Resolved.DeclarationId) (n : LocalNameTable) (e : Resolved.LocalScope V)
    (st : List V) (source : Syntax.Expr) where
  saved : Syntax.Expr
  savedOwner : Resolved.DeclarationId
  savedNames : LocalNameTable
  savedCaptured : Resolved.LocalScope V
  out : List V
  fields : RuntimeValue.sourceClosure saved savedOwner savedNames savedCaptured = .sourceClosure source o n e
  unchanged : out=st
  original : E o n e st source (.sourceClosure saved savedOwner savedNames savedCaptured) out
  run : evaluateClosedSourceExpression? 1 o n e st source = some (.sourceClosure saved savedOwner savedNames savedCaptured,out)
private def creation {o n e st source} (cert : LC source) : IO (Created o n e st source) := do
  have independent : E o n e st source (.sourceClosure source o n e) st := .creation cert.shape
  proof independent
  match ran : evaluateClosedSourceExpression? 1 o n e st source with
  | some (.sourceClosure actual ao an ae,out) =>
    have original := evaluateClosedSourceExpression?_sound ran
    have same := original.deterministic independent
    proof same
    return ⟨actual,ao,an,ae,out,same.1,same.2,original,ran⟩
  | _ => throw (IO.userError "actual independent creation")
private def nonreturn {o n e st source}
    (absent : ∀ value final, ¬ E o n e st source value final)
    (exhausted : ∀ budget, evaluateClosedSourceExpression? budget o n e st source = none) : IO Unit := do
  proof absent; proof exhausted
  for budget in [0,1,2,3,8,17] do
    match ran : evaluateClosedSourceExpression? budget o n e st source with
    | none => proof (exhausted budget)
    | some (_,_) => False.elim (absent _ _ (evaluateClosedSourceExpression?_sound ran))
private def direct (source : Syntax.Expr) (loop : Bool) (core other : V) (st : List V) : IO Unit := do
  match hw : source with
  | ⟨cs,.call left ⟨als,[right]⟩⟩ =>
    let lc ← lambda left; let rc ← lambda right
    let lm ← creation (o:=co) (n:=sn) (e:=se core other) (st:=st) lc
    let rm ← creation (o:=co) (n:=sn) (e:=se core other) (st:=lm.out) rc
    proof lm.original; proof rm.original; proof lm.fields; proof rm.fields; proof rm.unchanged; proof lm.run; proof rm.run
    check (left.span != right.span && lc.name.value != rc.name.value && lm.saved != rm.saved) "separate actual lambda occurrences"
    if loop then
      let ls ← selfBody lc.name lc.body; let rs ← selfBody rc.name rc.body
      nonreturn (o:=co) (n:=sn) (e:=se core other) (st:=st) (source:=source)
        (by rw [hw]; exact directSelfApplication_no_original lc.shape ls.down rc.shape rs.down co sn (se core other) st cs als)
        (by rw [hw]; exact directSelfApplication_none lc.shape ls.down rc.shape rs.down co sn (se core other) st cs als)
    else
      let actual ← lambda lm.saved
      match hb : actual.body with
      | ⟨_,[⟨_,.returnStmt (some ⟨ys,.identifier key⟩)⟩]⟩ =>
        if same : key.value=actual.name.value then
          let value := RuntimeValue.sourceClosure rm.saved rm.savedOwner rm.savedNames rm.savedCaptured
          let fresh := Resolved.freshLocalId lm.savedOwner (lm.savedNames.map Prod.snd)
          have independent : B lm.savedOwner ((actual.name.value,fresh)::lm.savedNames)
              ((fresh,value)::lm.savedCaptured) rm.out actual.body value rm.out := by
            rw [hb]; exact .expression (.reference (same ▸ LocalNameTable.Lookup.head) .head)
          have notSelf : ¬ SourceSelfApplicationBody actual.body actual.name := by rw [hb]; intro impossible; cases impossible
          have original : E co sn (se core other) st source value rm.out := by
            rw [hw]; exact .call actual.shape lm.original rm.original independent
          proof notSelf; proof independent; proof original
          match br : evaluateClosedSourceBody? 2 lm.savedOwner ((actual.name.value,fresh)::lm.savedNames)
              ((fresh,value)::lm.savedCaptured) rm.out actual.body with
          | some (bv,bs) =>
            have actualBody := evaluateClosedSourceBody?_sound br
            proof (show bv=value ∧ bs=rm.out from actualBody.deterministic independent)
            have actualCall : E co sn (se core other) st source bv bs := by
              rw [hw]; exact .call actual.shape lm.original rm.original actualBody
            proof actualCall
            for budget in [0,2,3,6] do
              match ran : evaluateClosedSourceExpression? budget co sn (se core other) st source with
              | none => check (budget<3) "identity low depth"
              | some (_,_) => proof ((evaluateClosedSourceExpression?_sound ran).deterministic actualCall)
          | none => throw (IO.userError "actual identity body returns complete loop closure")
        else throw (IO.userError "actual identity parameter")
      | _ => throw (IO.userError "actual identity return")
  | _ => throw (IO.userError "actual whole direct call")
private def savedLaws {saved : Syntax.Expr} (cert : LC saved) (self : SourceSelfApplicationBody cert.body cert.name)
    (ao : Resolved.DeclarationId) (an : LocalNameTable) (ae : Resolved.LocalScope V)
    (other : V) (st : List V) (source : Syntax.Expr) : IO Unit := do
  match hw : source with
  | ⟨cs,.call ⟨fs,.identifier f⟩ ⟨als,[⟨xs,.identifier x⟩]⟩⟩ =>
    if same : f.value="f" ∧ x.value="x" then
      let value := RuntimeValue.sourceClosure saved ao an ae
      let e := ce value other
      have fn : LocalNameTable.Lookup cn f.value (cid 1) := same.1 ▸ .head
      have xn : LocalNameTable.Lookup cn x.value (cid 2) := same.2 ▸ .tail (by decide) .head
      have fv : Resolved.LocalScope.Lookup e (cid 1) value := .head
      have xv : Resolved.LocalScope.Lookup e (cid 2) value := .tail (by decide) (.tail (by decide) .head)
      have picked : E co cn e st ⟨fs,.identifier f⟩ value st := .reference fn fv
      proof picked
      match fr : evaluateClosedSourceExpression? 1 co cn e st ⟨fs,.identifier f⟩ with
      | some (actual,cst) =>
        proof fr; proof (show actual=value ∧ cst=st from (evaluateClosedSourceExpression?_sound fr).deterministic picked)
        have argument : E co cn e cst ⟨xs,.identifier x⟩ value cst := .reference xn xv
        proof argument
        match xr : evaluateClosedSourceExpression? 1 co cn e cst ⟨xs,.identifier x⟩ with
        | some (av,ast) =>
          proof xr; proof (show av=value ∧ ast=cst from (evaluateClosedSourceExpression?_sound xr).deterministic argument)
        | none => throw (IO.userError "actual self argument success")
        proof (show actual=value from ((evaluateClosedSourceExpression?_sound fr).deterministic picked).1)
      | none => throw (IO.userError "actual self callee success")
      nonreturn (o:=co) (n:=cn) (e:=e) (st:=st) (source:=source)
        (by rw [hw]; exact savedSelfApplication_no_original cert.shape self ao an ae co cn e st cs als fs xs f x (cid 1) (cid 2) fn fv xn xv)
        (by rw [hw]; exact savedSelfApplication_none cert.shape self ao an ae co cn e st cs als fs xs f x (cid 1) (cid 2) fn fv xn xv)
    else throw (IO.userError "actual saved f/x")
  | _ => throw (IO.userError "actual saved invocation")
private def saved (source call short : Syntax.Expr) (core other : V) (st : List V) : IO Unit := do
  let cert ← lambda source
  let made ← creation (o:=so) (n:=sn) (e:=se core other) (st:=[other,core,.unit]) cert
  let actual ← lambda made.saved
  let self ← selfBody actual.name actual.body
  proof made.fields; proof made.original; proof made.unchanged; proof made.run
  check (made.savedOwner != co && made.out.length != st.length) "actual creation vs invocation owner/store"
  savedLaws actual self.down made.savedOwner made.savedNames made.savedCaptured other st call
  match hs : short with
  | ⟨_,.binary ⟨ls,.identifier a⟩ ⟨_,.logicalAnd⟩ right⟩ =>
    savedLaws actual self.down made.savedOwner made.savedNames made.savedCaptured other st right
    if key : a.value="a" then
      let value := RuntimeValue.sourceClosure made.saved made.savedOwner made.savedNames made.savedCaptured
      let e := ce value other
      have left : E co cn e st ⟨ls,.identifier a⟩ (.bool false) st :=
        .reference (key ▸ LocalNameTable.Lookup.tail (by decide) (.tail (by decide) .head))
          (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
      have original : E co cn e st short (.bool false) st := by rw [hs]; exact .andFalse left
      have direct : evaluateClosedSourceExpression? 2 co cn e st short = some (.bool false,st) := by
        simp [hs,evaluateClosedSourceExpression?,cn,e,ce,LocalNameTable.lookup?,Resolved.LocalScope.lookup?,key,cid]
      proof left; proof original; proof direct
      for budget in [0,1,2,5] do
        match ran : evaluateClosedSourceExpression? budget co cn e st short with
        | none => check (budget<2) "short circuit low depth"
        | some (_,_) => proof ((evaluateClosedSourceExpression?_sound ran).deterministic original)
    else throw (IO.userError "actual false guard")
  | _ => throw (IO.userError "actual short circuit")
end Tests.ParsedSelfApplication
open Solcore Solcore.Frontend Tests.ParsedSelfApplication in
def Tests.frontendParsedSelfApplicationTests : IO Unit := do
  let call ← parsed "f(x)" (expectedCall 0) [(0,4),(0,1),(0,1),(1,4),(2,3),(2,3)]
  let short ← parsed "a && f(x)" expectedShort [(0,9),(0,1),(0,1),(2,4),(5,9),(5,6),(5,6),(6,9),(7,8),(7,8)]
  let core := RuntimeValue.ofCore (.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700])
  let other := RuntimeValue.sourceClosure call (owner 610) [("q",cid 77),("q",cid 88)] [(cid 77,core),(cid 77,.unit)]
  let mut count := 0
  for lt in [false,true] do
    for rt in [false,true] do
      for loop in [true,false] do
        let l := "lam(q"++(if lt then ":Word" else "")++"){return "++(if loop then "q(q)" else "q")++";}"
        let r := "lam(r"++(if rt then ":Word" else "")++"){return r(r);}"
        let k := (if loop then 21 else 18)+(if lt then 5 else 0)
        let stop := k+21+(if rt then 5 else 0)
        let whole ← parsed (l++"("++r++")") (expectedWhole lt rt loop)
          ([(0,stop)]++lambdaRanges lt loop 0++[(k-1,stop)]++lambdaRanges rt true k)
        for st in [[],[other,core,.hostFunction .storageWrite,.cellRef .word 900]] do
          direct whole loop core other st
          let ⟨_,.call _ ⟨_,[right]⟩⟩ := whole | throw (IO.userError "whole argument extraction")
          saved right call short core other st
          count := count+1
  check (count==16) "four typed/inferred pairs / self and identity / two mixed stores"
end

section
-- leanmerge: from Solcore.Test.FrontendSelfApplicationBoundaryProperties
/- The body gate excludes self-calling return syntax by constructor inversion.
Only strict wrappers occur below: grouping and either side of a binary tuple.
No unselected child is required. Other children and all stores stay arbitrary. -/
set_option autoImplicit false
namespace Tests.SelfApplicationBoundaries
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates

/-- The saved-body data gate required by prior bounded-input laws excludes this
self-application syntax independently of its semantic non-return theorem. -/
theorem self_calling_body_is_outside_data
    {body : Syntax.Block} {name : Syntax.Identifier} (self : SourceSelfApplicationBody body name) :
    ¬ ClosedSourceDataBody body := by
  cases self
  intro admitted
  cases admitted with
  | expression child => cases child

private inductive Frame where
  | group (span : Syntax.SourceSpan)
  | left (span tupleSpan : Syntax.SourceSpan) (other : Syntax.Expr)
  | right (span tupleSpan : Syntax.SourceSpan) (other : Syntax.Expr)
private def wrap (frames : List Frame) (hole : Syntax.Expr) : Syntax.Expr :=
  match frames with
  | [] => hole
  | .group s :: rest => ⟨s,.group (wrap rest hole)⟩
  | .left s t other :: rest => ⟨s,.tuple ⟨t,[wrap rest hole,other]⟩⟩
  | .right s t other :: rest => ⟨s,.tuple ⟨t,[other,wrap rest hole]⟩⟩

private theorem strict_wrappers_none {owner names captured hole}
    (child : ∀ budget store, evaluateClosedSourceExpression? budget owner names captured store hole = none)
    (frames : List Frame) :
    ∀ budget store, evaluateClosedSourceExpression? budget owner names captured store (wrap frames hole) = none := by
  induction frames with
  | nil => exact child
  | cons frame frames ih =>
    intro budget store
    cases budget with
    | zero => simp [evaluateClosedSourceExpression?]
    | succ n =>
      cases frame with
      | group s => simp only [wrap,evaluateClosedSourceExpression?,ih]
      | left s t other => simp only [wrap,evaluateClosedSourceExpression?,ih,bind,Option.bind_none]
      | right s t other =>
        simp only [wrap,evaluateClosedSourceExpression?]
        cases evaluateClosedSourceExpression? n owner names captured store other with
        | none => simp only [bind,Option.bind_none]
        | some endpoint => simp only [ih,bind,Option.bind_some,Option.bind_none]

private theorem strict_wrappers_no_original {owner names captured hole}
    (child : ∀ store value final, ¬ E owner names captured store hole value final)
    (frames : List Frame) :
    ∀ store value final, ¬ E owner names captured store (wrap frames hole) value final := by
  induction frames with
  | nil => exact child
  | cons frame frames ih =>
    intro store value final original
    cases frame with
    | group s =>
      cases original with
      | creation impossible => cases impossible
      | group evaluated => exact ih _ _ _ evaluated
    | left s t other =>
      cases original with
      | creation impossible => cases impossible
      | pair left right => exact ih _ _ _ left
    | right s t other =>
      cases original with
      | creation impossible => cases impossible
      | pair left right => exact ih _ _ _ right

/-- Grouping and strict tuple contexts cannot turn this exact self-application
into a successful finite endpoint; intermediate stores are never guessed. -/
theorem strict_wrappers_preserve_self_non_return
    {left right : Syntax.Expr} {leftName rightName : Syntax.Identifier} {leftBody rightBody : Syntax.Block}
    (leftShape : SourceUnaryLambdaShape left leftName leftBody) (leftSelf : SourceSelfApplicationBody leftBody leftName)
    (rightShape : SourceUnaryLambdaShape right rightName rightBody) (rightSelf : SourceSelfApplicationBody rightBody rightName)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (callSpan argumentsSpan : Syntax.SourceSpan) (frames : List Frame) (store : List RuntimeValue) :
    let whole : Syntax.Expr := ⟨callSpan,.call left ⟨argumentsSpan,[right]⟩⟩
    (∀ budget, evaluateClosedSourceExpression? budget owner names captured store (wrap frames whole) = none) ∧
    (∀ value final, ¬ E owner names captured store (wrap frames whole) value final) := by
  intro whole
  have childNone : ∀ budget store, evaluateClosedSourceExpression? budget owner names captured store whole = none :=
    fun budget store => directSelfApplication_none leftShape leftSelf rightShape rightSelf owner names captured store callSpan argumentsSpan budget
  have childAbsent : ∀ store value final, ¬ E owner names captured store whole value final :=
    fun store value final => directSelfApplication_no_original leftShape leftSelf rightShape rightSelf
      owner names captured store callSpan argumentsSpan value final
  exact ⟨fun budget => strict_wrappers_none childNone frames budget store,
    fun value final => strict_wrappers_no_original childAbsent frames store value final⟩

private def owner (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"SelfBoundary",by decide⟩],by decide⟩⟩,n⟩
private def co := owner 910
private def foreignOwner := owner 310
private def id (n : Nat) : Resolved.LocalId := ⟨co,n⟩
private def span (n : Nat) : Syntax.SourceSpan := ⟨⟨.main,"self-boundary.sol"⟩,n,n+1⟩
private def name (n : Nat) (text : String) : Syntax.Identifier := ⟨span n,text⟩
private def selfBody (n : Nat) (text : String) : Syntax.Block :=
  ⟨span n,[⟨span (n+1),.returnStmt (some ⟨span (n+2),.call
    ⟨span (n+3),.identifier (name (n+4) text)⟩
    ⟨span (n+5),[⟨span (n+6),.identifier (name (n+7) text)⟩]⟩⟩)⟩]⟩
private def source (n : Nat) (text : String) : Syntax.Expr :=
  ⟨span (n+8),.lambda (span (n+9)) ⟨span (n+10),[⟨span (n+11),.inferred (name (n+12) text)⟩]⟩
    none (selfBody n text)⟩
private def opaqueValue : RuntimeValue := .pair (.cellRef .word 700)
  (.coreClosure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 900])
private def names : LocalNameTable := [("p",id 1),("p",id 99),("x",id 2),("x",id 2)]
private def captured : Resolved.LocalScope RuntimeValue :=
  [(id 1,opaqueValue),(id 1,.unit),(id 2,.sourceClosure (source 40 "foreign") foreignOwner [] []),(id 99,.bool false)]
private def store : List RuntimeValue := [opaqueValue,.cellRef .word 900,.hostFunction .storageWrite]
private def other : Syntax.Expr := ⟨span 90,.identifier (name 91 "x")⟩
private def frames : List Frame := [.group (span 80),.right (span 81) (span 82) other,
  .group (span 83),.left (span 84) (span 85) ⟨span 86,.literal ⟨span 87,.string "unreachable"⟩⟩]

example : co ≠ foreignOwner ∧ store ≠ [] := by decide
example : ¬ ClosedSourceDataBody (selfBody 0 "p") :=
  self_calling_body_is_outside_data (name:=name 12 "p") (.returning rfl rfl)
example : E co names captured store other (.sourceClosure (source 40 "foreign") foreignOwner [] []) store :=
  .reference (.tail (by decide) (.tail (by decide) .head))
    (.tail (by decide) (.tail (by decide) .head))
example (replacement : List RuntimeValue) :
    let whole : Syntax.Expr := ⟨span 70,.call (source 0 "p") ⟨span 71,[source 20 "r"]⟩⟩
    (∀ budget, evaluateClosedSourceExpression? budget co names captured replacement (wrap frames whole) = none) ∧
    (∀ value final, ¬ E co names captured replacement (wrap frames whole) value final) := by
  exact strict_wrappers_preserve_self_non_return
    (left:=source 0 "p") (right:=source 20 "r") (leftName:=name 12 "p") SourceUnaryLambdaShape.inferred (.returning rfl rfl)
    (rightName:=name 32 "r") SourceUnaryLambdaShape.inferred (.returning rfl rfl)
    co names captured (span 70) (span 71) frames replacement
end Tests.SelfApplicationBoundaries
end

section
-- leanmerge: from Solcore.Test.FrontendSelfApplicationSymbolicProperties
/- Original creations and successful input references precede non-return laws.
Typed parameters remain inert syntax; no typing or live host/cell claim is made. -/
set_option autoImplicit false
namespace Tests.SelfApplicationSymbolic
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def ref (s : Syntax.SourceSpan) (p : Syntax.Identifier) : Syntax.Expr := ⟨s,.identifier p⟩
private def app (s t : Syntax.SourceSpan) (f x : Syntax.Expr) : Syntax.Expr := ⟨s,.call f ⟨t,[x]⟩⟩
private def loopBody (s t : Syntax.SourceSpan) (p : Syntax.Identifier) : Syntax.Block :=
  ⟨s,[⟨s,.returnStmt (some (app s t (ref s p) (ref t p)))⟩]⟩
private def identityBody (s t : Syntax.SourceSpan) (p : Syntax.Identifier) : Syntax.Block :=
  ⟨s,[⟨s,.returnStmt (some (ref t p))⟩]⟩
private def lambda (s : Syntax.SourceSpan) (p : Syntax.Identifier)
    (pa ra : Option Syntax.TypeExpr) (body : Syntax.Block) : Syntax.Expr :=
  ⟨s,.lambda s ⟨s,[⟨s,match pa with | none => .inferred p | some a => .typed none p a⟩]⟩ ra body⟩
private theorem shape (s : Syntax.SourceSpan) (p : Syntax.Identifier)
    (pa ra : Option Syntax.TypeExpr) (body : Syntax.Block) :
    SourceUnaryLambdaShape (lambda s p pa ra body) p body := by
  cases pa <;> constructor
private def freshNames (owner : Resolved.DeclarationId) (names : LocalNameTable) (p : Syntax.Identifier) :=
  (p.value,Resolved.freshLocalId owner (names.map Prod.snd))::names
private def freshCaptured (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (value : RuntimeValue) :=
  (Resolved.freshLocalId owner (names.map Prod.snd),value)::captured
private theorem created_run {source p body} (sh : SourceUnaryLambdaShape source p body)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (n : Nat) :
    evaluateClosedSourceExpression? (n+1) owner names captured store source =
      some (.sourceClosure source owner names captured,store) := by
  cases sh <;> simp only [evaluateClosedSourceExpression?,sourceUnaryLambdaShape?,bind,Option.bind_some,pure]

/-- Saved self-inputs succeed independently, including arbitrary finite mixed lexical rows. -/
theorem saved_self_application_has_successful_inputs
    (s t : Syntax.SourceSpan) (p f x : Syntax.Identifier) (pa ra : Option Syntax.TypeExpr)
    (co so : Resolved.DeclarationId) (cn sn : LocalNameTable) (cc sc : Resolved.LocalScope RuntimeValue)
    (creationStore store : List RuntimeValue) (fid xid : Resolved.LocalId)
    (fn : LocalNameTable.Lookup cn f.value fid)
    (fv : Resolved.LocalScope.Lookup cc fid (.sourceClosure (lambda s p pa ra (loopBody s t p)) so sn sc))
    (xn : LocalNameTable.Lookup cn x.value xid)
    (xv : Resolved.LocalScope.Lookup cc xid (.sourceClosure (lambda s p pa ra (loopBody s t p)) so sn sc)) :
    let source := lambda s p pa ra (loopBody s t p)
    let saved := RuntimeValue.sourceClosure source so sn sc
    E so sn sc creationStore source saved creationStore ∧
    E co cn cc store (ref s f) saved store ∧ E co cn cc store (ref t x) saved store ∧
    (∀ n, evaluateClosedSourceExpression? (n+1) co cn cc store (ref s f) = some (saved,store) ∧
      evaluateClosedSourceExpression? (n+1) co cn cc store (ref t x) = some (saved,store)) ∧
    (∀ n, evaluateClosedSourceBody? (n+3) so (freshNames so sn p) (freshCaptured so sn sc saved) store (loopBody s t p) =
      evaluateClosedSourceBody? (n+1) so (freshNames so sn p) (freshCaptured so sn sc saved) store (loopBody s t p)) ∧
    (∀ budget, evaluateClosedSourceBody? budget so (freshNames so sn p) (freshCaptured so sn sc saved) store (loopBody s t p) = none) ∧
    (∀ value final, ¬ B so (freshNames so sn p) (freshCaptured so sn sc saved) store (loopBody s t p) value final) ∧
    (∀ budget, evaluateClosedSourceExpression? budget co cn cc store (app s t (ref s f) (ref t x)) = none) ∧
    (∀ value final, ¬ E co cn cc store (app s t (ref s f) (ref t x)) value final) := by
  let source := lambda s p pa ra (loopBody s t p)
  have sh : SourceUnaryLambdaShape source p (loopBody s t p) := shape s p pa ra _
  have created : E so sn sc creationStore source (.sourceClosure source so sn sc) creationStore := .creation sh
  have picked : E co cn cc store (ref s f) (.sourceClosure source so sn sc) store := .reference fn fv
  have supplied : E co cn cc store (ref t x) (.sourceClosure source so sn sc) store := .reference xn xv
  have children (n : Nat) :
      evaluateClosedSourceExpression? (n+1) co cn cc store (ref s f) = some (.sourceClosure source so sn sc,store) ∧
      evaluateClosedSourceExpression? (n+1) co cn cc store (ref t x) = some (.sourceClosure source so sn sc,store) := by
    constructor <;> simp only [ref,evaluateClosedSourceExpression?,LocalNameTable.lookup?_iff.mpr fn,
      LocalNameTable.lookup?_iff.mpr xn,Resolved.LocalScope.lookup?_iff.mpr fv,
      Resolved.LocalScope.lookup?_iff.mpr xv,bind,Option.bind_some,pure,source]
  have self : SourceSelfApplicationBody (loopBody s t p) p := .returning rfl rfl
  refine ⟨created,picked,supplied,children,?_,?_,?_,?_,?_⟩
  · exact selfApplicationBody_depth_reentry sh self so sn sc store
  · exact selfApplicationBody_none sh self so sn sc store
  · exact selfApplicationBody_no_original sh self so sn sc store
  · exact savedSelfApplication_none sh self so sn sc co cn cc store s t s t f x fid xid fn fv xn xv
  · exact savedSelfApplication_no_original sh self so sn sc co cn cc store s t s t f x fid xid fn fv xn xv

/-- Distinct source occurrences and parameter spellings require no closure identity assumption. -/
theorem separately_created_self_callers_do_not_return
    (s t u v : Syntax.SourceSpan) (p q : Syntax.Identifier) (lpa lra rpa rra : Option Syntax.TypeExpr)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) :
    let left := lambda s p lpa lra (loopBody s t p)
    let right := lambda u q rpa rra (loopBody u v q)
    let saved := RuntimeValue.sourceClosure right owner names captured
    E owner names captured store left (.sourceClosure left owner names captured) store ∧
    E owner names captured store right saved store ∧
    (∀ n, evaluateClosedSourceExpression? (n+1) owner names captured store left = some (.sourceClosure left owner names captured,store) ∧
      evaluateClosedSourceExpression? (n+1) owner names captured store right = some (saved,store)) ∧
    E owner (freshNames owner names p) (freshCaptured owner names captured saved) store (ref s p) saved store ∧
    E owner (freshNames owner names p) (freshCaptured owner names captured saved) store (ref t p) saved store ∧
    (∀ n, evaluateClosedSourceBody? (n+3) owner (freshNames owner names p) (freshCaptured owner names captured saved) store (loopBody s t p) =
      evaluateClosedSourceBody? (n+1) owner (freshNames owner names q) (freshCaptured owner names captured saved) store (loopBody u v q)) ∧
    (∀ budget, evaluateClosedSourceBody? budget owner (freshNames owner names p) (freshCaptured owner names captured saved) store (loopBody s t p) = none) ∧
    (∀ budget, evaluateClosedSourceExpression? budget owner names captured store (app s t left right) = none) ∧
    (∀ value final, ¬ E owner names captured store (app s t left right) value final) := by
  let left := lambda s p lpa lra (loopBody s t p)
  let right := lambda u q rpa rra (loopBody u v q)
  have ls : SourceUnaryLambdaShape left p (loopBody s t p) := shape s p lpa lra _
  have rs : SourceUnaryLambdaShape right q (loopBody u v q) := shape u q rpa rra _
  have madeLeft : E owner names captured store left (.sourceClosure left owner names captured) store := .creation ls
  have madeRight : E owner names captured store right (.sourceClosure right owner names captured) store := .creation rs
  have children (n : Nat) := And.intro (created_run ls owner names captured store n) (created_run rs owner names captured store n)
  have picked : E owner (freshNames owner names p) (freshCaptured owner names captured (.sourceClosure right owner names captured))
      store (ref s p) (.sourceClosure right owner names captured) store := .reference .head .head
  have supplied : E owner (freshNames owner names p) (freshCaptured owner names captured (.sourceClosure right owner names captured))
      store (ref t p) (.sourceClosure right owner names captured) store := .reference .head .head
  have li : SourceSelfApplicationBody (loopBody s t p) p := .returning rfl rfl
  have ri : SourceSelfApplicationBody (loopBody u v q) q := .returning rfl rfl
  refine ⟨madeLeft,madeRight,children,picked,supplied,?_,?_,?_,?_⟩
  · exact selfApplicationBody_calls_bound_closure rs li owner owner names names captured captured store
  · exact selfApplicationBody_boundSelf_none rs ri li owner owner names names captured captured store
  · exact directSelfApplication_none ls li rs ri owner names captured store s t
  · exact directSelfApplication_no_original ls li rs ri owner names captured store s t

/-- Returning the looping closure is successful; skipping its self-call also succeeds. -/
theorem identity_and_short_circuit_contrast
    (s t : Syntax.SourceSpan) (p q flag : Syntax.Identifier) (pa ra : Option Syntax.TypeExpr)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (flagId : Resolved.LocalId)
    (named : LocalNameTable.Lookup names flag.value flagId)
    (found : Resolved.LocalScope.Lookup captured flagId (.bool false)) :
    let identity := lambda s p pa ra (identityBody s t p)
    let loop := lambda t q pa ra (loopBody t s q)
    let saved := RuntimeValue.sourceClosure loop owner names captured
    let nonreturn := app s t loop loop
    let skipped : Syntax.Expr := ⟨s,.binary (ref s flag) ⟨t,.logicalAnd⟩ nonreturn⟩
    ¬ SourceSelfApplicationBody (identityBody s t p) p ∧
    E owner names captured store (app s t identity loop) saved store ∧
    evaluateClosedSourceExpression? 2 owner names captured store (app s t identity loop) = none ∧
    evaluateClosedSourceExpression? 3 owner names captured store (app s t identity loop) = some (saved,store) ∧
    E owner names captured store skipped (.bool false) store ∧
    evaluateClosedSourceExpression? 1 owner names captured store skipped = none ∧
    evaluateClosedSourceExpression? 2 owner names captured store skipped = some (.bool false,store) ∧
    (∀ budget, evaluateClosedSourceExpression? budget owner names captured store nonreturn = none) := by
  let identity := lambda s p pa ra (identityBody s t p)
  let loop := lambda t q pa ra (loopBody t s q)
  have is : SourceUnaryLambdaShape identity p (identityBody s t p) := shape s p pa ra _
  have ls : SourceUnaryLambdaShape loop q (loopBody t s q) := shape t q pa ra _
  have madeIdentity : E owner names captured store identity (.sourceClosure identity owner names captured) store := .creation is
  have madeLoop : E owner names captured store loop (.sourceClosure loop owner names captured) store := .creation ls
  have returned : B owner (freshNames owner names p)
      (freshCaptured owner names captured (.sourceClosure loop owner names captured)) store
      (identityBody s t p) (.sourceClosure loop owner names captured) store := .expression (.reference .head .head)
  have identityOriginal : E owner names captured store (app s t identity loop) (.sourceClosure loop owner names captured) store :=
    .call is madeIdentity madeLoop returned
  have left : E owner names captured store (ref s flag) (.bool false) store := .reference named found
  have skipped : E owner names captured store ⟨s,.binary (ref s flag) ⟨t,.logicalAnd⟩ (app s t loop loop)⟩ (.bool false) store :=
    .andFalse left
  have identityRuns : evaluateClosedSourceExpression? 2 owner names captured store (app s t identity loop) = none ∧
      evaluateClosedSourceExpression? 3 owner names captured store (app s t identity loop) = some (.sourceClosure loop owner names captured,store) := by
    cases pa <;> simp [app,identity,loop,lambda,identityBody,ref,evaluateClosedSourceExpression?,evaluateClosedSourceBody?,
      sourceUnaryLambdaShape?,LocalNameTable.lookup?,Resolved.LocalScope.lookup?]
  have skippedRuns :
      evaluateClosedSourceExpression? 1 owner names captured store ⟨s,.binary (ref s flag) ⟨t,.logicalAnd⟩ (app s t loop loop)⟩ = none ∧
      evaluateClosedSourceExpression? 2 owner names captured store ⟨s,.binary (ref s flag) ⟨t,.logicalAnd⟩ (app s t loop loop)⟩ = some (.bool false,store) := by
    simp [ref,evaluateClosedSourceExpression?,LocalNameTable.lookup?_iff.mpr named,Resolved.LocalScope.lookup?_iff.mpr found]
  have notSelf : ¬ SourceSelfApplicationBody (identityBody s t p) p := by intro impossible; cases impossible
  have self : SourceSelfApplicationBody (loopBody t s q) q := .returning rfl rfl
  exact ⟨notSelf,identityOriginal,identityRuns.1,identityRuns.2,skipped,skippedRuns.1,skippedRuns.2,
    directSelfApplication_none ls self ls self owner names captured store s t⟩

end Tests.SelfApplicationSymbolic
end
