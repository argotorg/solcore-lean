import Solcore.Frontend.ClosedSource
import Solcore.Frontend.Computation
import Solcore.Frontend.LocalExpressionEvaluation
import Solcore.Frontend.RuntimeValue

/- Independent original rule/selector evidence; no image law or bounded runner is imported. -/
set_option autoImplicit false
namespace Tests.ClosedSourceDataBodyBoundaries
open Solcore Solcore.Frontend

private def up (environment : Resolved.Environment) :=
  environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2))
private def ref (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span, .identifier name⟩
private def bare (span : Syntax.SourceSpan) : Syntax.Block := ⟨span, [⟨span, .returnStmt none⟩]⟩
private def output (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Block :=
  ⟨span, [⟨span, .returnStmt (some (ref span name))⟩]⟩
private def arm (span : Syntax.SourceSpan) (pattern : Syntax.Pattern) (body : Syntax.Block) : Syntax.MatchCase :=
  ⟨span, ⟨pattern, body⟩⟩
private def matching (span : Syntax.SourceSpan) (key : Syntax.Identifier)
    (cases : List Syntax.MatchCase) (fallback : Option Syntax.Block) : Syntax.Block :=
  ⟨span, [⟨span, .matchWith ⟨span, ⟨ref span key, []⟩⟩ ⟨span, ⟨cases, fallback⟩⟩⟩]⟩
private def wildcard (span : Syntax.SourceSpan) : Syntax.Pattern := ⟨span, .wildcard span⟩
private def malformed (span : Syntax.SourceSpan) (text : String) : Syntax.Pattern :=
  ⟨span, .literal ⟨span, .string text⟩⟩
private def unary (span : Syntax.SourceSpan) : Syntax.Expr :=
  ⟨span, .lambda span ⟨span, [⟨span, .inferred ⟨span, "parameter"⟩⟩]⟩ none (bare span)⟩
private def returningClosure (span : Syntax.SourceSpan) : Syntax.Block :=
  ⟨span, [⟨span, .returnStmt (some (unary span))⟩]⟩
private def conditional (span : Syntax.SourceSpan) (key : Syntax.Identifier) (choice : Bool) : Syntax.Block :=
  ⟨span, [⟨span, .ifThen (ref span key)
    (if choice then bare span else returningClosure span)
    (some (if choice then returningClosure span else bare span))⟩]⟩
private def discardingClosure (span : Syntax.SourceSpan) : Syntax.Block :=
  ⟨span, [⟨span, .expression (unary span) true⟩, ⟨span, .returnStmt none⟩]⟩
private def overlap (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (environment : Resolved.Environment) (store : Core.Store) (body : Syntax.Block) (value : Core.Value) : Prop :=
  ClosedSourceBodyEvaluates owner names (up environment) (store.map RuntimeValue.ofCore)
    body (RuntimeValue.ofCore value) (store.map RuntimeValue.ofCore) ∧
  ComputationReturnTreeEvaluates LocalExpressionEvaluates owner names environment store body value store

private theorem mapped {environment : Resolved.Environment} {id : Resolved.LocalId} {value : Core.Value}
    (found : Resolved.LocalScope.Lookup environment id value) :
    Resolved.LocalScope.Lookup (up environment) id (RuntimeValue.ofCore value) := by
  induction found with
  | head => exact .head
  | tail different _ ih => exact .tail different ih

private theorem original_match {span owner names environment store key target keyId targetId actual value cases fallback tests}
    (keyName : LocalNameTable.Lookup names key.value keyId)
    (keyValue : Resolved.LocalScope.Lookup environment keyId actual)
    (targetName : LocalNameTable.Lookup names target.value targetId)
    (targetValue : Resolved.LocalScope.Lookup environment targetId value)
    (oldChoice : WordMatchChooses actual cases fallback (output span target) tests)
    (mixedChoice : RuntimeWordMatchChooses (RuntimeValue.ofCore actual)
      cases fallback (output span target) tests) :
    overlap owner names environment store (matching span key cases fallback) value := by
  exact ⟨.wordMatch (.reference keyName (mapped keyValue)) mixedChoice
      (.expression (.reference targetName (mapped targetValue))),
    .wordMatch (.identifier keyName keyValue) oldChoice (.expression (.identifier targetName targetValue))⟩

variable (span : Syntax.SourceSpan) (owner : Resolved.DeclarationId)
  (names : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
  (key target : Syntax.Identifier) (keyId targetId : Resolved.LocalId) (value : Core.Value)

/-- The original first literal hit, including its count, drives both body derivations. -/
theorem wordMatch_literal_hit_original (word : Core.Word) (pattern : Syntax.Pattern)
    (meaning : WordMatchPatternClassifies pattern (some word))
    (later : List Syntax.MatchCase) (fallback : Option Syntax.Block)
    (keyName : LocalNameTable.Lookup names key.value keyId)
    (keyValue : Resolved.LocalScope.Lookup environment keyId (.word word))
    (targetName : LocalNameTable.Lookup names target.value targetId)
    (targetValue : Resolved.LocalScope.Lookup environment targetId value) :
    let cases := arm span pattern (output span target) :: later
    WordMatchChooses (.word word) cases fallback (output span target) 1 ∧
    RuntimeWordMatchChooses (RuntimeValue.ofCore (.word word)) cases fallback (output span target) 1 ∧
    overlap owner names environment store (matching span key cases fallback) value := by
  have oldChoice : WordMatchChooses (.word word)
      (arm span pattern (output span target) :: later) fallback (output span target) 1 := .hit meaning
  have mixedChoice : RuntimeWordMatchChooses (RuntimeValue.ofCore (.word word))
      (arm span pattern (output span target) :: later) fallback (output span target) 1 := by
    simpa only [arm, RuntimeValue.ofCore] using
      RuntimeWordMatchChooses.hit (first := arm span pattern (output span target)) (rest := later) meaning
  exact ⟨oldChoice, mixedChoice, original_match keyName keyValue targetName targetValue oldChoice mixedChoice⟩

/-- Two visited literal misses retain original order and count before the wildcard. -/
theorem wordMatch_two_literal_misses_original (word first second : Core.Word)
    (firstPattern secondPattern : Syntax.Pattern) (firstBody secondBody : Syntax.Block)
    (firstMeaning : WordMatchPatternClassifies firstPattern (some first))
    (secondMeaning : WordMatchPatternClassifies secondPattern (some second))
    (missFirst : word ≠ first) (missSecond : word ≠ second)
    (keyName : LocalNameTable.Lookup names key.value keyId)
    (keyValue : Resolved.LocalScope.Lookup environment keyId (.word word))
    (targetName : LocalNameTable.Lookup names target.value targetId)
    (targetValue : Resolved.LocalScope.Lookup environment targetId value) :
    let cases := [arm span firstPattern firstBody, arm span secondPattern secondBody,
      arm span (wildcard span) (output span target)]
    WordMatchChooses (.word word) cases none (output span target) 2 ∧
    RuntimeWordMatchChooses (RuntimeValue.ofCore (.word word)) cases none (output span target) 2 ∧
    overlap owner names environment store (matching span key cases none) value := by
  let cases := [arm span firstPattern firstBody, arm span secondPattern secondBody,
    arm span (wildcard span) (output span target)]
  have oldChoice : WordMatchChooses (.word word) cases none (output span target) 2 :=
    .miss firstMeaning missFirst (.miss secondMeaning missSecond (.wildcard (.wildcard rfl)))
  have mixedChoice : RuntimeWordMatchChooses (RuntimeValue.ofCore (.word word))
      cases none (output span target) 2 := by
    simp only [RuntimeValue.ofCore]
    exact .miss firstMeaning missFirst (.miss secondMeaning missSecond (.wildcard (.wildcard rfl)))
  exact ⟨oldChoice, mixedChoice, original_match keyName keyValue targetName targetValue oldChoice mixedChoice⟩

/-- Wildcard/default accept every opaque Core value, without a Word or typing premise. -/
theorem wordMatch_wildcard_and_default_keep_opaque_value (actual : Core.Value)
    (keyName : LocalNameTable.Lookup names key.value keyId)
    (keyValue : Resolved.LocalScope.Lookup environment keyId actual)
    (targetName : LocalNameTable.Lookup names target.value targetId)
    (targetValue : Resolved.LocalScope.Lookup environment targetId value) :
    let cases := [arm span (wildcard span) (output span target)]
    WordMatchChooses actual cases none (output span target) 0 ∧
    WordMatchChooses actual [] (some (output span target)) (output span target) 0 ∧
    overlap owner names environment store (matching span key cases none) value ∧
    overlap owner names environment store (matching span key [] (some (output span target))) value := by
  have oldWildcard : WordMatchChooses actual [arm span (wildcard span) (output span target)]
      none (output span target) 0 := .wildcard (.wildcard rfl)
  have mixedWildcard : RuntimeWordMatchChooses (RuntimeValue.ofCore actual)
      [arm span (wildcard span) (output span target)] none (output span target) 0 := .wildcard (.wildcard rfl)
  exact ⟨oldWildcard, .fallback,
    original_match keyName keyValue targetName targetValue oldWildcard mixedWildcard,
    original_match keyName keyValue targetName targetValue .fallback .fallback⟩

private theorem closure_body_outside (span : Syntax.SourceSpan) :
    ¬ ClosedSourceDataBody (returningClosure span) := by
  intro gate
  cases gate with
  | expression child => cases child

/-- Either actual Bool skips a swapped original non-data body while both raw paths succeed. -/
theorem unselected_nongated_body_has_raw_overlap (choice : Bool)
    (keyName : LocalNameTable.Lookup names key.value keyId)
    (keyValue : Resolved.LocalScope.Lookup environment keyId (.bool choice)) :
    ¬ ClosedSourceDataBody (conditional span key choice) ∧
    overlap owner names environment store (conditional span key choice) .unit := by
  have guard : ClosedSourceExpressionEvaluates owner names (up environment)
      (store.map RuntimeValue.ofCore) (ref span key) (.bool choice) (store.map RuntimeValue.ofCore) := by
    simpa only [ref, RuntimeValue.ofCore] using ClosedSourceExpressionEvaluates.reference keyName (mapped keyValue)
  have outside : ¬ ClosedSourceDataBody (conditional span key choice) := by
    cases choice with
    | false => intro gate; cases gate with
      | conditional _ yes _ => exact closure_body_outside span yes
    | true => intro gate; cases gate with
      | conditional _ _ no => exact closure_body_outside span no
  refine ⟨outside, ?_, ?_⟩
  · simp only [RuntimeValue.ofCore]
    cases choice with
    | false => exact .ifFalse guard .bare
    | true => exact .ifTrue guard .bare
  · cases choice with
    | false => exact .ifFalse (.identifier keyName keyValue) .bare
    | true => exact .ifTrue (.identifier keyName keyValue) .bare

private theorem malformed_unclassified (span : Syntax.SourceSpan) (text : String) (tag : Option Core.Word) :
    ¬ WordMatchPatternClassifies (malformed span text) tag := by
  intro meaning
  cases meaning with
  | literal denotation =>
      obtain ⟨literal, same, meaning⟩ := denotation
      cases same
      cases meaning
  | wildcard shape => cases shape

/-- All body syntax can be admitted even when an unvisited original pattern is unsupported. -/
theorem invalid_unvisited_pattern_keeps_body_gate (actual : Core.Value) (text : String)
    (keyName : LocalNameTable.Lookup names key.value keyId)
    (keyValue : Resolved.LocalScope.Lookup environment keyId actual)
    (targetName : LocalNameTable.Lookup names target.value targetId)
    (targetValue : Resolved.LocalScope.Lookup environment targetId value) :
    let bad := arm span (malformed span text) (bare span)
    let cases := [arm span (wildcard span) (output span target), bad]
    ClosedSourceDataBody (matching span key cases none) ∧
    overlap owner names environment store (matching span key cases none) value ∧
    (∀ selected tests, ¬ WordMatchChooses actual [bad] none selected tests) := by
  let bad := arm span (malformed span text) (bare span)
  let cases := [arm span (wildcard span) (output span target), bad]
  refine ⟨?_, original_match keyName keyValue targetName targetValue
    (.wildcard (.wildcard rfl)) (.wildcard (.wildcard rfl)), ?_⟩
  · refine .wordMatch .reference ?_ ?_
    · intro candidate member
      rcases List.mem_cons.mp member with rfl | member
      · exact .expression .reference
      · rcases List.mem_cons.mp member with rfl | member
        · exact .bare
        · cases member
    · intro source member; cases member
  · intro selected tests choice
    cases choice with
    | wildcard meaning => exact malformed_unclassified span text _ meaning
    | hit meaning => exact malformed_unclassified span text _ meaning
    | miss meaning _ _ => exact malformed_unclassified span text _ meaning

/-- Discard can hide a source-only intermediate value behind an embedded Unit endpoint. -/
theorem discarded_source_closure_refutes_endpoint_only_image :
    ClosedSourceExpressionEvaluates owner names (up environment) (store.map RuntimeValue.ofCore)
      (unary span) (.sourceClosure (unary span) owner names (up environment)) (store.map RuntimeValue.ofCore) ∧
    (¬ ∃ old, RuntimeValue.sourceClosure (unary span) owner names (up environment) = RuntimeValue.ofCore old) ∧
    ClosedSourceBodyEvaluates owner names (up environment) (store.map RuntimeValue.ofCore)
      (discardingClosure span) (RuntimeValue.ofCore .unit) (store.map RuntimeValue.ofCore) ∧
    (∀ old final, ¬ ComputationReturnTreeEvaluates LocalExpressionEvaluates owner names environment
      store (discardingClosure span) old final) ∧
    ¬ ClosedSourceDataBody (discardingClosure span) := by
  refine ⟨.creation .inferred, ?_, ?_, ?_, ?_⟩
  · rintro ⟨old, same⟩
    have impossible := congrArg RuntimeValue.toCore? same
    simp only [RuntimeValue.toCore?, RuntimeValue.toCore?_ofCore, reduceCtorEq] at impossible
  · simp only [RuntimeValue.ofCore]
    exact .discard (.creation .inferred) .bare
  · intro old final evaluated
    cases evaluated with
    | discard child _ => cases child
  · intro gate
    cases gate with
    | discard child _ => cases child

end Tests.ClosedSourceDataBodyBoundaries
