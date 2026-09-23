import Solcore.Frontend.ClosedSource

/- Original conditional and ordered-choice witnesses precede depth contracts.
Mixed captures and complete stores remain arbitrary; no uniqueness or typing
premise is introduced. Visited match comparisons are not source-search depth. -/
set_option autoImplicit false
namespace Tests.DataBodyDepthControlFlow
open Solcore Solcore.Frontend

private def reference (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span,.identifier name⟩
private def bare (bodySpan returnSpan : Syntax.SourceSpan) : Syntax.Block :=
  ⟨bodySpan,[⟨returnSpan,.returnStmt none⟩]⟩
private def returning (bodySpan returnSpan expressionSpan : Syntax.SourceSpan)
    (name : Syntax.Identifier) : Syntax.Block :=
  ⟨bodySpan,[⟨returnSpan,.returnStmt (some (reference expressionSpan name))⟩]⟩
private def conditional (spans : Fin 8 → Syntax.SourceSpan)
    (guard payload : Syntax.Identifier) : Syntax.Block :=
  ⟨spans 0,[⟨spans 1,.ifThen (reference (spans 2) guard)
    (returning (spans 3) (spans 4) (spans 5) payload)
    (some (bare (spans 6) (spans 7)))⟩]⟩

/-- The unselected expression return makes H=3 conservative on the false path;
the true path needs all three levels even for an arbitrary mixed payload. -/
theorem conditional_mixed_endpoint_and_conservative_depth
    (spans : Fin 8 → Syntax.SourceSpan) (guard payload : Syntax.Identifier)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (guardId payloadId : Resolved.LocalId) (choice : Bool) (value : RuntimeValue)
    (namedGuard : LocalNameTable.Lookup names guard.value guardId)
    (foundGuard : Resolved.LocalScope.Lookup captured guardId (.bool choice))
    (namedPayload : LocalNameTable.Lookup names payload.value payloadId)
    (foundPayload : Resolved.LocalScope.Lookup captured payloadId value) (extra : Nat) :
    let body := conditional spans guard payload
    let result := if choice then value else .unit
    ClosedSourceDataBody body ∧ closedSourceDataBodyDepthBound body = 3 ∧
    ClosedSourceBodyEvaluates owner names captured store body result store ∧
    evaluateClosedSourceBody? 1 owner names captured store body = none ∧
    evaluateClosedSourceBody? 2 owner names captured store body =
      (if choice then none else some (.unit,store)) ∧
    (choice = true → ∀ budget, budget < 3 →
      evaluateClosedSourceBody? budget owner names captured store body = none) ∧
    evaluateClosedSourceBody? (3 + extra) owner names captured store body = some (result,store) ∧
    evaluateClosedSourceBody? (3 + extra) owner names captured store body =
      evaluateClosedSourceBody? (closedSourceDataBodyDepthBound body) owner names captured store body ∧
    (∀ actual final, evaluateClosedSourceBody? (3 + extra) owner names captured store body =
      some (actual,final) ↔ actual = result ∧ final = store) := by
  intro body result
  have original : ClosedSourceBodyEvaluates owner names captured store body result store := by
    cases choice with
    | false => exact .ifFalse (.reference namedGuard foundGuard) .bare
    | true => exact .ifTrue (.reference namedGuard foundGuard) (.expression (.reference namedPayload foundPayload))
  have gate : ClosedSourceDataBody body := .conditional .reference (.expression .reference) .bare
  have depth : closedSourceDataBodyDepthBound body = 3 := by
    simp only [body,conditional,returning,bare,reference,closedSourceDataBodyDepthBound,closedSourceDataDepthBound]
    omega
  have atOne : evaluateClosedSourceBody? 1 owner names captured store body = none := by
    simp only [body,conditional,evaluateClosedSourceBody?,evaluateClosedSourceExpression?,bind,Option.bind_none]
  have atTwo : evaluateClosedSourceBody? 2 owner names captured store body =
      (if choice then none else some (.unit,store)) := by
    cases choice <;> simp only [body,conditional,reference,returning,bare,
      evaluateClosedSourceBody?,evaluateClosedSourceExpression?,LocalNameTable.lookup?_iff.mpr namedGuard,
      Resolved.LocalScope.lookup?_iff.mpr foundGuard,bind,pure,Option.bind_some,Bool.false_eq_true,↓reduceIte]
  have necessary : choice = true → ∀ budget, budget < 3 →
      evaluateClosedSourceBody? budget owner names captured store body = none := by
    intro chosen budget small
    cases budget with
    | zero => simp only [evaluateClosedSourceBody?]
    | succ budget =>
        cases budget with
        | zero => exact atOne
        | succ budget =>
            have zero : budget = 0 := by omega
            subst budget
            simpa only [chosen,↓reduceIte] using atTwo
  have enough : closedSourceDataBodyDepthBound body ≤ 3 + extra := by omega
  refine ⟨gate,depth,original,atOne,atTwo,necessary,gate.evaluates_at_depthBound original enough,
    gate.evaluate_depth_stable owner names captured store enough,?_⟩
  intro actual final
  rw [gate.evaluate_at_depthBound_iff enough]
  exact ⟨fun evaluated => evaluated.deterministic original,by rintro ⟨rfl,rfl⟩; exact original⟩

private def one : Core.Word := ⟨1,by decide⟩
private def zeroCase (spans : Fin 8 → Syntax.SourceSpan) : Syntax.MatchCase :=
  ⟨spans 4,⟨⟨spans 5,.literal ⟨spans 5,.decimal "0"⟩⟩,bare (spans 6) (spans 7)⟩⟩
private def missedCases (spans : Fin 8 → Syntax.SourceSpan) : Nat → List Syntax.MatchCase
  | 0 => []
  | n + 1 => zeroCase spans :: missedCases spans n
private def matching (spans : Fin 8 → Syntax.SourceSpan) (n : Nat) : Syntax.Block :=
  ⟨spans 0,[⟨spans 1,.matchWith
    ⟨spans 2,⟨⟨spans 2,.literal ⟨spans 2,.decimal "1"⟩⟩,[]⟩⟩
    ⟨spans 3,⟨missedCases spans n,some (bare (spans 6) (spans 7))⟩⟩⟩]⟩

private theorem one_meaning (span : Syntax.SourceSpan) :
    WordLiteralDenotes ⟨span,.decimal "1"⟩ one :=
  .decimal (by decide) (.cons (.decimal (digit := 1) (by decide) rfl) .nil)
private theorem zero_pattern (spans : Fin 8 → Syntax.SourceSpan) :
    WordMatchPatternClassifies (zeroCase spans).value.pattern (some Core.Word.zero) :=
  .literal ⟨⟨spans 5,.decimal "0"⟩,rfl,
    .decimal (by decide) (.cons (.decimal (digit := 0) (by decide) rfl) .nil)⟩

private theorem original_choice (spans : Fin 8 → Syntax.SourceSpan) (n : Nat) :
    RuntimeWordMatchChooses (.word one) (missedCases spans n)
      (some (bare (spans 6) (spans 7))) (bare (spans 6) (spans 7)) n := by
  induction n with
  | zero => exact .fallback
  | succ n ih => exact .miss (zero_pattern spans) (by decide) ih

private theorem all_branches (spans : Fin 8 → Syntax.SourceSpan) (n : Nat) :
    ∀ arm ∈ missedCases spans n, ClosedSourceDataBody arm.value.body := by
  induction n with
  | zero => intro arm member; cases member
  | succ n ih =>
      intro arm member
      simp only [missedCases,List.mem_cons] at member
      rcases member with same | member
      · cases same; exact .bare
      · exact ih arm member

private theorem branches_depth (spans : Fin 8 → Syntax.SourceSpan) (n : Nat) :
    closedSourceDataMatchDepthBound (missedCases spans n)
      (some (bare (spans 6) (spans 7))) = 1 := by
  induction n with
  | zero => simp only [missedCases,closedSourceDataMatchDepthBound,bare,closedSourceDataBodyDepthBound]
  | succ n ih =>
      rw [missedCases,closedSourceDataMatchDepthBound,ih]
      simp only [zeroCase,bare,closedSourceDataBodyDepthBound,Nat.max_self]

/-- All n visited literal comparisons are retained by the original ordered
choice, while the entire body has depth two independently of n. -/
theorem arbitrary_misses_keep_comparison_count_separate_from_depth
    (spans : Fin 8 → Syntax.SourceSpan) (n extra : Nat)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) :
    let body := matching spans n
    let fallback := bare (spans 6) (spans 7)
    RuntimeWordMatchChooses (.word one) (missedCases spans n) (some fallback) fallback n ∧
    chooseRuntimeWordMatch? (.word one) (missedCases spans n) (some fallback) = some (fallback,n) ∧
    (∀ selected tests, RuntimeWordMatchChooses (.word one) (missedCases spans n)
      (some fallback) selected tests ↔ selected = fallback ∧ tests = n) ∧
    ClosedSourceDataBody body ∧ closedSourceDataBodyDepthBound body = 2 ∧
    ClosedSourceBodyEvaluates owner names captured store body .unit store ∧
    evaluateClosedSourceBody? 1 owner names captured store body = none ∧
    evaluateClosedSourceBody? (2 + extra) owner names captured store body = some (.unit,store) ∧
    evaluateClosedSourceBody? (2 + extra) owner names captured store body =
      evaluateClosedSourceBody? (closedSourceDataBodyDepthBound body) owner names captured store body ∧
    (∀ actual final, evaluateClosedSourceBody? (2 + extra) owner names captured store body =
      some (actual,final) ↔ actual = .unit ∧ final = store) := by
  intro body fallback
  have choice := original_choice spans n
  have original : ClosedSourceBodyEvaluates owner names captured store body .unit store :=
    .wordMatch (.wordLiteral (one_meaning (spans 2))) choice .bare
  have gate : ClosedSourceDataBody body := .wordMatch .literal (all_branches spans n)
    (by intro source member; simp only [Option.toList_some,List.mem_singleton] at member; subst source; exact .bare)
  have depth : closedSourceDataBodyDepthBound body = 2 := by
    simp only [body,matching,closedSourceDataBodyDepthBound,closedSourceDataDepthBound,branches_depth]
    omega
  have atOne : evaluateClosedSourceBody? 1 owner names captured store body = none := by
    simp only [body,matching,evaluateClosedSourceBody?,evaluateClosedSourceExpression?,bind,Option.bind_none]
  have enough : closedSourceDataBodyDepthBound body ≤ 2 + extra := by omega
  refine ⟨choice,chooseRuntimeWordMatch?_iff.mpr choice,?_,gate,depth,original,atOne,
    gate.evaluates_at_depthBound original enough,
    gate.evaluate_depth_stable owner names captured store enough,?_⟩
  · intro selected tests
    exact ⟨fun selectedChoice => selectedChoice.deterministic choice,by rintro ⟨rfl,rfl⟩; exact choice⟩
  · intro actual final
    rw [gate.evaluate_at_depthBound_iff enough]
    exact ⟨fun evaluated => evaluated.deterministic original,by rintro ⟨rfl,rfl⟩; exact original⟩

end Tests.DataBodyDepthControlFlow
