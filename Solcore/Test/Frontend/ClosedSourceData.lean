import Solcore.Frontend.ClosedSource
import Solcore.Frontend.Computation
import Solcore.Frontend.LocalExpressionEvaluation
import Solcore.Frontend.RuntimeValue
import Solcore.Frontend.LocalExpressionExecutionProperties
import Solcore.Frontend.TypedLetReturnTree
import Solcore.Core.LocalFragment
import Solcore.Frontend.LocalExpression
import Solcore.Frontend.LocalReference
import Solcore.Resolved.LocalScope
import Solcore.Core.UnaryPrimitives
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Frontend.LocalExpressionTyping

/-!
# Closed source data tests

Closed source data images: data bodies and matches, short circuits, unary and logical forms, and body
depth.
-/

section
-- leanmerge: from Solcore.Test.FrontendClosedSourceBodyDepthProperties
/- Original if, ordered literal misses and discard prefixes; comparisons are not depth. -/
set_option autoImplicit false
namespace Tests.ClosedSourceBodyDepth
open Solcore Solcore.Frontend

private def returned (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Block :=
  ⟨span, [⟨span, .returnStmt (some ⟨span, .identifier name⟩)⟩]⟩

private def arms (span : Syntax.SourceSpan) (miss : Syntax.CoreLiteral)
    (ignored selected : Syntax.Block) (suffix : List Syntax.MatchCase) : Nat → List Syntax.MatchCase
  | 0 => ⟨span, ⟨⟨span, .wildcard span⟩, selected⟩⟩ :: suffix
  | count + 1 => ⟨span, ⟨⟨span, .literal miss⟩, ignored⟩⟩ :: arms span miss ignored selected suffix count

private def matched (span : Syntax.SourceSpan) (literal miss : Syntax.CoreLiteral)
    (ignored selected : Syntax.Block) (suffix : List Syntax.MatchCase)
    (fallback : Option Syntax.Block) (count : Nat) : Syntax.Block :=
  ⟨span, [⟨span, .matchWith ⟨span, ⟨⟨span, .literal literal⟩, []⟩⟩
    ⟨span, ⟨arms span miss ignored selected suffix count, fallback⟩⟩⟩]⟩

private def branched (span : Syntax.SourceSpan) (guard : Syntax.Identifier)
    (choice : Bool) (selected ignored : Syntax.Block) : Syntax.Block :=
  ⟨span, [⟨span, .ifThen ⟨span, .identifier guard⟩
    (if choice then selected else ignored) (some (if choice then ignored else selected))⟩]⟩

private def prefixed (span : Syntax.SourceSpan) (statements : List Syntax.Statement) : Nat → Syntax.Block
  | 0 => ⟨span, statements⟩
  | count + 1 => ⟨span, ⟨span, .expression ⟨span, .tuple ⟨span, []⟩⟩ true⟩ ::
      (prefixed span statements count).value⟩

private theorem prefixed_rebuild (span : Syntax.SourceSpan) (statements : List Syntax.Statement) (count : Nat) :
    ⟨span, (prefixed span statements count).value⟩ = prefixed span statements count := by
  cases count <;> rfl

private theorem selection_original (span : Syntax.SourceSpan) (miss : Syntax.CoreLiteral)
    (ignored selected : Syntax.Block) (suffix : List Syntax.MatchCase)
    (fallback : Option Syntax.Block) (word other : Core.Word)
    (meaning : WordLiteralDenotes miss other) (different : word ≠ other) (count : Nat) :
    RuntimeWordMatchChooses (.word word) (arms span miss ignored selected suffix count)
      fallback selected count := by
  induction count with
  | zero => exact .wildcard (.wildcard rfl)
  | succ count ih => exact .miss (.literal ⟨miss, rfl, meaning⟩) different ih

private theorem selection_direct (span : Syntax.SourceSpan) (miss : Syntax.CoreLiteral)
    (ignored selected : Syntax.Block) (suffix : List Syntax.MatchCase)
    (fallback : Option Syntax.Block) (word other : Core.Word)
    (meaning : WordLiteralDenotes miss other) (different : word ≠ other) (count : Nat) :
    chooseRuntimeWordMatch? (.word word) (arms span miss ignored selected suffix count)
      fallback = some (selected, count) := by
  induction count with
  | zero => simp only [arms, chooseRuntimeWordMatch?, interpretWordMatchPattern?]
  | succ count ih =>
      simp only [arms, chooseRuntimeWordMatch?, interpretWordMatchPattern?,
        interpretWordLiteral?_complete meaning, Option.map_some, different, ↓reduceIte, ih]

section Family
variable (span : Syntax.SourceSpan) (guard name : Syntax.Identifier) (choice : Bool)
  (literal miss : Syntax.CoreLiteral) (ignored : Syntax.Block) (suffix : List Syntax.MatchCase)
  (fallback : Option Syntax.Block) (count prefixes : Nat)
  (owner : Resolved.DeclarationId) (names : LocalNameTable)
  (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
  (guardId valueId : Resolved.LocalId) (value : RuntimeValue) (word other : Core.Word)
  (guardNamed : LocalNameTable.Lookup names guard.value guardId)
  (guardFound : Resolved.LocalScope.Lookup captured guardId (.bool choice))
  (valueNamed : LocalNameTable.Lookup names name.value valueId)
  (valueFound : Resolved.LocalScope.Lookup captured valueId value)
  (literalMeaning : WordLiteralDenotes literal word) (missMeaning : WordLiteralDenotes miss other)
  (different : word ≠ other)

include guardNamed guardFound valueNamed valueFound literalMeaning missMeaning different

local notation "source" => prefixed span
  (Syntax.Located.value (branched span guard choice
    (matched span literal miss ignored (returned span name) suffix fallback count) ignored))
  prefixes

/-- Original constructors alone preserve arbitrary inputs, ignored syntax and the exact literal comparison count. -/
theorem bodyDepth_original :
    ClosedSourceBodyEvaluates owner names captured store source value store ∧
    RuntimeWordMatchChooses (.word word) (arms span miss ignored (returned span name) suffix count)
      fallback (returned span name) count := by
  refine ⟨?_, selection_original span miss ignored _ suffix fallback word other missMeaning different count⟩
  have selected : ClosedSourceBodyEvaluates owner names captured store (returned span name) value store :=
    .expression (.reference valueNamed valueFound)
  have matchedBody : ClosedSourceBodyEvaluates owner names captured store
      (matched span literal miss ignored (returned span name) suffix fallback count) value store :=
    .wordMatch (.wordLiteral literalMeaning)
      (selection_original span miss ignored _ suffix fallback word other missMeaning different count) selected
  have branch : ClosedSourceBodyEvaluates owner names captured store
      (branched span guard choice (matched span literal miss ignored (returned span name) suffix fallback count) ignored)
      value store := by
    cases choice with
    | false => exact .ifFalse (.reference guardNamed guardFound) matchedBody
    | true => exact .ifTrue (.reference guardNamed guardFound) matchedBody
  induction prefixes with
  | zero => exact branch
  | succ prefixes ih =>
      apply ClosedSourceBodyEvaluates.discard ClosedSourceExpressionEvaluates.unit
      simpa only [prefixed_rebuild] using ih

/-- Separate runner recursion gives the whole Option result; literal comparisons do not add depth. -/
theorem bodyDepth_exact (budget : Nat) :
    evaluateClosedSourceBody? budget owner names captured store source =
      if prefixes + 4 ≤ budget then some (value, store) else none := by
  have selection := selection_direct span miss ignored (returned span name) suffix fallback word other missMeaning different count
  simp only [returned] at selection
  have namedGuard := LocalNameTable.lookup?_iff.mpr guardNamed
  have foundGuard := Resolved.LocalScope.lookup?_iff.mpr guardFound
  have namedValue := LocalNameTable.lookup?_iff.mpr valueNamed
  have foundValue := Resolved.LocalScope.lookup?_iff.mpr valueFound
  have literalValue := interpretWordLiteral?_complete literalMeaning
  induction prefixes generalizing budget with
  | zero =>
      cases budget with
      | zero => simp [evaluateClosedSourceBody?]
      | succ budget =>
          cases budget with
          | zero => simp [prefixed, branched, evaluateClosedSourceBody?, evaluateClosedSourceExpression?]
          | succ budget =>
              cases budget with
              | zero =>
                  cases choice <;> simp [prefixed, branched, matched, evaluateClosedSourceBody?,
                    evaluateClosedSourceExpression?, namedGuard, foundGuard]
              | succ budget =>
                  cases budget with
                  | zero =>
                      cases choice <;> simp [prefixed, branched, matched, returned, evaluateClosedSourceBody?,
                        evaluateClosedSourceExpression?, namedGuard, foundGuard, literalValue, selection]
                  | succ budget =>
                      cases choice <;> simp [prefixed, branched, matched, returned, evaluateClosedSourceBody?,
                        evaluateClosedSourceExpression?, namedGuard, foundGuard, namedValue, foundValue,
                        literalValue, selection]
  | succ prefixes ih =>
      cases budget with
      | zero => simp [evaluateClosedSourceBody?]
      | succ budget =>
          cases budget with
          | zero => simp [prefixed, evaluateClosedSourceBody?, evaluateClosedSourceExpression?]
          | succ budget =>
              rw [prefixed]
              simp only [evaluateClosedSourceBody?, evaluateClosedSourceExpression?, bind, Option.bind]
              rw [prefixed_rebuild, ih]
              have order : (prefixes + 4 ≤ budget + 1) = (prefixes + 1 + 4 ≤ budget + 1 + 1) :=
                propext (by omega)
              simp only [order]

/-- Actual cutoff success and predecessor failure feed the general upward/downward laws. -/
theorem bodyDepth_transport :
    (∀ larger, prefixes + 4 ≤ larger →
      evaluateClosedSourceBody? larger owner names captured store source = some (value, store)) ∧
    (∀ smaller, smaller ≤ prefixes + 3 →
      evaluateClosedSourceBody? smaller owner names captured store source = none) ∧
    evaluateClosedSourceBody? 0 owner names captured store source = none := by
  have exactRun := bodyDepth_exact span guard name choice literal miss ignored suffix fallback count prefixes
    owner names captured store guardId valueId value word other guardNamed guardFound valueNamed valueFound
    literalMeaning missMeaning different
  have accepted : evaluateClosedSourceBody? (prefixes + 4) owner names captured store source =
      some (value, store) := by simpa only [Nat.le_refl, if_true] using exactRun (prefixes + 4)
  have rejected : evaluateClosedSourceBody? (prefixes + 3) owner names captured store source = none := by
    simpa only [show ¬ prefixes + 4 ≤ prefixes + 3 by omega, if_false] using exactRun (prefixes + 3)
  exact ⟨fun _ order => evaluateClosedSourceBody?_monotone order accepted,
    (fun _ order => evaluateClosedSourceBody?_none_of_le order rejected),
    evaluateClosedSourceBody?_none_of_le (Nat.zero_le _) rejected⟩

/-- The finite original derivation's general threshold agrees with the independently computed boundary. -/
theorem bodyDepth_threshold :
    ∃ required : Nat, 0 < required ∧ required = prefixes + 4 ∧ ∀ budget,
      evaluateClosedSourceBody? budget owner names captured store source =
        if required ≤ budget then some (value, store) else none := by
  have original := bodyDepth_original span guard name choice literal miss ignored suffix fallback count prefixes
    owner names captured store guardId valueId value word other guardNamed guardFound valueNamed valueFound
    literalMeaning missMeaning different
  obtain ⟨required, positive, cutoff⟩ := original.1.exact_depth_threshold
  have exactRun := bodyDepth_exact span guard name choice literal miss ignored suffix fallback count prefixes
    owner names captured store guardId valueId value word other guardNamed guardFound valueNamed valueFound
    literalMeaning missMeaning different
  have upper : required ≤ prefixes + 4 := by
    by_cases bound : required ≤ prefixes + 4
    · exact bound
    · have impossible := cutoff (prefixes + 4)
      rw [if_neg bound, exactRun] at impossible
      simp only [Nat.le_refl, if_true, reduceCtorEq] at impossible
  have lower : prefixes + 3 < required := by
    by_cases bound : prefixes + 3 < required
    · exact bound
    · have impossible := cutoff (prefixes + 3)
      rw [if_pos (show required ≤ prefixes + 3 by omega), exactRun] at impossible
      simp only [show ¬ prefixes + 4 ≤ prefixes + 3 by omega, if_false, reduceCtorEq] at impossible
  exact ⟨required, positive, by omega, cutoff⟩

end Family
end Tests.ClosedSourceBodyDepth
end

section
-- leanmerge: from Solcore.Test.FrontendClosedSourceDataBodyBoundaryProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendClosedSourceDataBodyImageProperties
/- Original repeated shadowing preserves the pre-binding value and complete raw store. -/
set_option autoImplicit false
namespace Tests.ClosedSourceDataBodyImages
open Solcore Solcore.Frontend

private def statements (spans : Nat → Syntax.SourceSpan) (name : Syntax.Identifier) :
    List (Option Syntax.TypeExpr) → List Syntax.Statement
  | [] => [⟨spans 1, .returnStmt (some ⟨spans 2, .identifier name⟩)⟩]
  | annotation :: rest =>
      ⟨spans 3, .letDecl name annotation (some ⟨spans 4, .identifier name⟩)⟩ ::
        statements spans name rest

private def source (spans : Nat → Syntax.SourceSpan) (name : Syntax.Identifier)
    (annotations : List (Option Syntax.TypeExpr)) : Syntax.Block :=
  ⟨spans 0, statements spans name annotations⟩

private theorem mapped_lookup {environment : Resolved.Environment} {id : Resolved.LocalId}
    {value : Core.Value} (found : Resolved.LocalScope.Lookup environment id value) :
    Resolved.LocalScope.Lookup
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      id (RuntimeValue.ofCore value) := by
  induction found with
  | head => exact .head
  | tail different _ ih => exact .tail different ih

section Family
variable (spans : Nat → Syntax.SourceSpan) (name : Syntax.Identifier)
  (annotations : List (Option Syntax.TypeExpr)) (owner : Resolved.DeclarationId)
  (names : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
  (id : Resolved.LocalId) (value : Core.Value)
  (named : LocalNameTable.Lookup names name.value id)
  (found : Resolved.LocalScope.Lookup environment id value)

local notation "original" => source spans name annotations

include named found

/-- Original constructors precede every image law; annotations do not constrain raw success. -/
theorem independent_original_prefixes :
    ClosedSourceDataBody original ∧
    ClosedSourceBodyEvaluates owner names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (store.map RuntimeValue.ofCore) original (RuntimeValue.ofCore value)
      (store.map RuntimeValue.ofCore) ∧
    ComputationReturnTreeEvaluates LocalExpressionEvaluates owner names environment
      store original value store := by
  induction annotations generalizing names environment id with
  | nil =>
      exact ⟨.expression .reference,
        .expression (.reference named (mapped_lookup found)),
        .expression (.identifier named found)⟩
  | cons annotation rest ih =>
      have tail := ih
        ((name.value, Resolved.freshLocalId owner (names.map Prod.snd)) :: names)
        ((Resolved.freshLocalId owner (names.map Prod.snd), value) :: environment)
        (Resolved.freshLocalId owner (names.map Prod.snd)) .head .head
      refine ⟨.binding .reference tail.1, ?_⟩
      cases annotation with
      | none =>
          exact ⟨.inferred (.reference named (mapped_lookup found))
            (by simpa only [source, List.map_cons] using tail.2.1),
            .inferred (.identifier named found) tail.2.2⟩
      | some annotation =>
          exact ⟨.binding (.reference named (mapped_lookup found))
            (by simpa only [source, List.map_cons] using tail.2.1),
            .binding (.identifier named found) tail.2.2⟩

private theorem old_endpoint {actualValue : Core.Value} {actualFinal : Core.Store}
    (actual : ComputationReturnTreeEvaluates LocalExpressionEvaluates owner names environment
      store original actualValue actualFinal) :
    actualValue = value ∧ actualFinal = store := by
  induction annotations generalizing names environment id store with
  | nil =>
      cases actual with
      | expression child => exact child.deterministic (.identifier named found)
  | cons annotation rest ih =>
      cases annotation with
      | none =>
          cases actual with
          | inferred initializer tail =>
              obtain ⟨rfl, rfl⟩ := initializer.deterministic (.identifier named found)
              exact ih _ _ _ _ .head .head tail
      | some annotation =>
          cases actual with
          | binding initializer tail =>
              obtain ⟨rfl, rfl⟩ := initializer.deterministic (.identifier named found)
              exact ih _ _ _ _ .head .head tail

/-- Every actual raw result agrees with the independent pre-shadowing endpoint. -/
theorem all_actual_local_images {actualValue : RuntimeValue} {actualFinal : List RuntimeValue} :
    ClosedSourceBodyEvaluates owner names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (store.map RuntimeValue.ofCore) original actualValue actualFinal ↔
    actualValue = RuntimeValue.ofCore value ∧ actualFinal = store.map RuntimeValue.ofCore := by
  have paths := independent_original_prefixes spans name annotations owner names environment
    store id value named found
  constructor
  · intro actual
    obtain ⟨result, finalStore, same, finalSame, old⟩ := paths.1.local_evaluates_iff.mp actual
    obtain ⟨rfl, rfl⟩ := old_endpoint spans name annotations owner names environment
      store id value named found old
    exact ⟨same, finalSame⟩
  · rintro ⟨rfl, rfl⟩
    exact paths.1.local_evaluates_iff.mpr ⟨value, store, rfl, rfl, paths.2.2⟩

end Family

section Checked
variable (spans : Nat → Syntax.SourceSpan) (name : Syntax.Identifier)
  (annotations : List (Option Syntax.TypeExpr)) (owner : Resolved.DeclarationId)
  (types : TypeNameTable) (inputs : LocalTypeInputs) (environment : Resolved.Environment)
  (store : Core.Store) (id : Resolved.LocalId) (value : Core.Value)
  (named : LocalNameTable.Lookup inputs.names name.value id)
  (found : Resolved.LocalScope.Lookup environment id value)
  (core : Core.Expr) (type : Core.Ty)

local notation "original" => source spans name annotations

variable (accepted : elaborateComputationReturnTree? elaborateLocalExpression?
    types owner inputs (source spans name annotations) = some (core, type))
  (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)

include spans annotations named found accepted sameIds

/-- The old shared correspondence supplies this endpoint without either new body theorem. -/
theorem independent_checked_core_endpoint :
    Core.Evaluates (Resolved.LocalScope.values environment) store core value store := by
  have originalPaths := independent_original_prefixes spans name annotations owner
    inputs.names environment store id value named found
  have elaboration : ComputationReturnTreeElaborates
      (fun table context child core type =>
        elaborateLocalExpression? table context child = some (core, type))
      types owner inputs original core type :=
    (elaborateComputationReturnTree?_iff (fun {_ _ _ _ _} => Iff.rfl)).mp accepted
  exact (ComputationReturnTreeElaborates.evaluates_iff
    (ChildEval := LocalExpressionEvaluates)
    (F := Core.Expr.LocalFragment)
    (fun child => elaborateLocalExpression?_localFragment child)
    (fun fragment cutoff => fragment.weakenAt cutoff)
    (fun fragment leading suffix inserted => fragment.evaluates_insert_iff leading suffix inserted)
    (fun child aligned => elaborateLocalExpression?_evaluates_iff child aligned)
    elaboration sameIds).mp originalPaths.2.2

/-- Actual Core image endpoints use whole checking and exact IDs, never runtime typing. -/
theorem all_actual_core_images {actualValue : RuntimeValue} {actualFinal : List RuntimeValue} :
    ClosedSourceBodyEvaluates owner inputs.names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (store.map RuntimeValue.ofCore) original actualValue actualFinal ↔
    actualValue = RuntimeValue.ofCore value ∧ actualFinal = store.map RuntimeValue.ofCore := by
  have paths := independent_original_prefixes spans name annotations owner inputs.names environment
    store id value named found
  have independent := independent_checked_core_endpoint spans name annotations owner types inputs
    environment store id value named found core type accepted sameIds
  constructor
  · intro actual
    obtain ⟨result, finalStore, same, finalSame, evaluated⟩ :=
      (paths.1.core_evaluates_iff accepted sameIds).mp actual
    obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated independent
    exact ⟨same, finalSame⟩
  · rintro ⟨rfl, rfl⟩
    exact (paths.1.core_evaluates_iff accepted sameIds).mpr
      ⟨value, store, rfl, rfl, independent⟩

end Checked
end Tests.ClosedSourceDataBodyImages
end

section
-- leanmerge: from Solcore.Test.FrontendClosedSourceDataBoundaryProperties
/- Independent shape/image/alignment counterexamples, not failures inferred from a budget. -/
set_option autoImplicit false
namespace Tests.ClosedSourceDataBoundaries
open Solcore Solcore.Frontend

private def embedded (environment : Resolved.Environment) : Resolved.LocalScope RuntimeValue :=
  environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2))

private def unit (span : Syntax.SourceSpan) : Syntax.Expr := ⟨span, .tuple ⟨span, []⟩⟩
private def reference (span : Syntax.SourceSpan) : Syntax.Expr := ⟨span, .identifier ⟨span, "c"⟩⟩
private def negated (span : Syntax.SourceSpan) : Syntax.Expr :=
  ⟨span, .unary ⟨span, .logicalNot⟩ (reference span)⟩
private def singleton (span : Syntax.SourceSpan) : Syntax.Expr := ⟨span, .tuple ⟨span, [unit span]⟩⟩
private def unary (span : Syntax.SourceSpan) : Syntax.Expr :=
  ⟨span, .lambda span ⟨span, [⟨span, .inferred ⟨span, "x"⟩⟩]⟩ none
    ⟨span, [⟨span, .returnStmt none⟩]⟩⟩
private def applied (span : Syntax.SourceSpan) : Syntax.Expr :=
  ⟨span, .call (unary span) ⟨span, [unit span]⟩⟩
private def skipped (span : Syntax.SourceSpan) (choice : Bool) : Syntax.Expr :=
  ⟨span, .conditional (reference span) span
    (if choice then unit span else unary span) span
    (if choice then unary span else unit span)⟩

private theorem unary_outside (span : Syntax.SourceSpan) :
    ¬ ClosedSourceDataExpression (unary span) := by
  intro fragment
  cases fragment

variable (span : Syntax.SourceSpan) (owner : Resolved.DeclarationId)
  (names : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)

/-- Shape admission of any string spelling establishes neither old nor closed evaluation. -/
theorem string_admission_has_no_evaluation (spelling : String) :
    ClosedSourceDataExpression ⟨span, .literal ⟨span, .string spelling⟩⟩ ∧
    (∀ actual final, ¬ ClosedSourceExpressionEvaluates owner names (embedded environment)
      (store.map RuntimeValue.ofCore) ⟨span, .literal ⟨span, .string spelling⟩⟩ actual final) ∧
    (∀ value final, ¬ LocalExpressionEvaluates names environment store
      ⟨span, .literal ⟨span, .string spelling⟩⟩ value final) := by
  refine ⟨.literal, ?_, ?_⟩
  · intro actual final evaluated
    cases evaluated with
    | wordLiteral meaning => cases meaning
    | creation shape => cases shape
  · intro value final evaluated
    cases evaluated with
    | wordLiteral meaning => cases meaning

/-- Singleton tuples remain excluded, while negation is admitted and evaluates successfully. -/
theorem singleton_and_negation_are_outside_data (id : Resolved.LocalId) (choice : Bool) :
    ¬ ClosedSourceDataExpression (singleton span) ∧
    ClosedSourceDataExpression (negated span) ∧
    ResolvesLocalExpression [("c", id)] (negated span) (.unary .boolNot (.var id)) ∧
    LocalExpressionEvaluates [("c", id)] [(id, .bool choice)] store
      (negated span) (.bool (!choice)) store ∧
    ClosedSourceExpressionEvaluates owner [("c", id)]
      (embedded [(id, .bool choice)]) (store.map RuntimeValue.ofCore) (negated span)
      (.bool (!choice)) (store.map RuntimeValue.ofCore) := by
  refine ⟨?_, ?_, .logicalNot (.identifier .head), .logicalNot (.identifier .head .head), ?_⟩
  · intro fragment; cases fragment
  · exact .logicalNot .reference
  · simp only [embedded, List.map_cons, List.map_nil, RuntimeValue.ofCore]
    exact .logicalNot (.reference .head .head)

/-- A directly created original closure from embedded inputs has no Core-value preimage. -/
theorem creation_from_core_inputs_is_not_core_data :
    ¬ ClosedSourceDataExpression (unary span) ∧
    ClosedSourceExpressionEvaluates owner names (embedded environment)
      (store.map RuntimeValue.ofCore) (unary span)
      (.sourceClosure (unary span) owner names (embedded environment)) (store.map RuntimeValue.ofCore) ∧
    ¬ ∃ value, RuntimeValue.sourceClosure (unary span) owner names (embedded environment) =
      RuntimeValue.ofCore value := by
  refine ⟨unary_outside span, .creation .inferred, ?_⟩
  rintro ⟨value, same⟩
  have impossible := congrArg RuntimeValue.toCore? same
  simp only [RuntimeValue.toCore?, RuntimeValue.toCore?_ofCore, reduceCtorEq] at impossible

/-- An embedded endpoint alone cannot recover a missing old source-call rule. -/
theorem embedded_unit_call_still_has_no_local_rule :
    ¬ ClosedSourceDataExpression (applied span) ∧
    ClosedSourceExpressionEvaluates owner names (embedded environment)
      (store.map RuntimeValue.ofCore) (applied span) (RuntimeValue.ofCore .unit)
      (store.map RuntimeValue.ofCore) ∧
    (∀ value final, ¬ LocalExpressionEvaluates names environment store (applied span) value final) := by
  refine ⟨?_, ?_, ?_⟩
  · intro fragment; cases fragment
  · simp only [RuntimeValue.ofCore]
    exact .call .inferred (.creation .inferred) .unit .bare
  · intro value final evaluated
    cases evaluated

/-- Either actual Boolean choice can skip an original lambda outside the whole syntax gate. -/
theorem unselected_lambda_allows_raw_overlap (id : Resolved.LocalId) (choice : Bool) :
    ¬ ClosedSourceDataExpression (skipped span choice) ∧
    ClosedSourceExpressionEvaluates owner [("c", id)] (embedded [(id, .bool choice)])
      (store.map RuntimeValue.ofCore) (skipped span choice) .unit (store.map RuntimeValue.ofCore) ∧
    LocalExpressionEvaluates [("c", id)] [(id, .bool choice)] store (skipped span choice) .unit store := by
  have outside : ¬ ClosedSourceDataExpression (skipped span choice) := by
    cases choice with
    | false =>
        intro fragment
        cases fragment with
        | conditional _ thenSyntax _ => exact unary_outside span thenSyntax
    | true =>
        intro fragment
        cases fragment with
        | conditional _ _ elseSyntax => exact unary_outside span elseSyntax
  have guard : ClosedSourceExpressionEvaluates owner [("c", id)] (embedded [(id, .bool choice)])
      (store.map RuntimeValue.ofCore) (reference span) (.bool choice) (store.map RuntimeValue.ofCore) := by
    simp only [embedded, List.map_cons, List.map_nil, RuntimeValue.ofCore]
    exact .reference .head .head
  refine ⟨outside, ?_, ?_⟩
  · cases choice with
    | false => exact .conditionalFalse guard .unit
    | true => exact .conditionalTrue guard .unit
  · cases choice with
    | false => exact .ifFalse (.identifier .head .head) .unit
    | true => exact .ifTrue (.identifier .head .head) .unit

private def ordered (first second : Resolved.LocalId) : Resolved.Environment :=
  [(first, .bool true), (second, .bool false)]
private def reordered (first second : Resolved.LocalId) : Resolved.Environment :=
  [(second, .bool false), (first, .bool true)]

/-- Reusing index zero after a same-length reordering changes Core's value, not the named value. -/
theorem equal_lengths_do_not_align_runtime_ids (first second : Resolved.LocalId)
    (different : second ≠ first) :
    (ordered first second).length = (reordered first second).length ∧
    ResolvesLocalExpression [("c", first)] (reference span) (.var first) ∧
    Resolved.Lowers (Resolved.LocalScope.ids (ordered first second)) (.var first) (.var 0) ∧
    Resolved.Lowers (Resolved.LocalScope.ids (reordered first second)) (.var first) (.var 1) ∧
    LocalExpressionEvaluates [("c", first)] (reordered first second) store
      (reference span) (.bool true) store ∧
    ClosedSourceExpressionEvaluates owner [("c", first)] (embedded (reordered first second))
      (store.map RuntimeValue.ofCore) (reference span) (.bool true) (store.map RuntimeValue.ofCore) ∧
    Core.Evaluates (Resolved.LocalScope.values (ordered first second)) store (.var 0) (.bool true) store ∧
    Core.Evaluates (Resolved.LocalScope.values (reordered first second)) store (.var 0) (.bool false) store ∧
    Core.Evaluates (Resolved.LocalScope.values (reordered first second)) store (.var 1) (.bool true) store ∧
    ¬ Resolved.Lowers (Resolved.LocalScope.ids (reordered first second)) (.var first) (.var 0) := by
  refine ⟨rfl, .identifier .head, .var .head, .var (.tail different .head),
    .identifier .head (.tail different .head), ?_, .var rfl, .var rfl, .var rfl, ?_⟩
  · simp only [embedded, reordered, List.map_cons, List.map_nil, RuntimeValue.ofCore]
    exact .reference .head (.tail different .head)
  · intro lowered
    cases lowered with
    | var found =>
        cases found with
        | head => exact different rfl

end Tests.ClosedSourceDataBoundaries
end

section
-- leanmerge: from Solcore.Test.FrontendClosedSourceDataImageProperties
/- Independent original paths keep arbitrary Core payloads and lexical rows literal. -/
set_option autoImplicit false
namespace Tests.ClosedSourceDataImages
open Solcore Solcore.Frontend

private def branch (spans : Nat → Syntax.SourceSpan) (literal : Syntax.CoreLiteral)
    (left right : Syntax.Identifier) : Syntax.Expr :=
  ⟨spans 0, .tuple ⟨spans 1, [
    ⟨spans 2, .group ⟨spans 3, .identifier left⟩⟩,
    ⟨spans 4, .tuple ⟨spans 5, []⟩⟩,
    ⟨spans 6, .identifier right⟩,
    ⟨spans 7, .literal literal⟩]⟩⟩

private def source (spans : Nat → Syntax.SourceSpan) (literal : Syntax.CoreLiteral)
    (guard left right : Syntax.Identifier) : Syntax.Expr :=
  ⟨spans 8, .conditional ⟨spans 9, .identifier guard⟩ (spans 10)
    (branch spans literal left right) (spans 11) (branch spans literal right left)⟩

private def result (left right : Core.Value) (word : Core.Word) : Core.Value :=
  .pair left (.pair .unit (.pair right (.word word)))

private def chosenResult (choice : Bool) (left right : Core.Value) (word : Core.Word) : Core.Value :=
  if choice then result left right word else result right left word

private theorem mapped_lookup {environment : Resolved.Environment} {id : Resolved.LocalId}
    {value : Core.Value} (found : Resolved.LocalScope.Lookup environment id value) :
    Resolved.LocalScope.Lookup
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      id (RuntimeValue.ofCore value) := by
  induction found with
  | head => exact .head
  | tail different _ ih => exact .tail different ih

private theorem branch_syntax (spans : Nat → Syntax.SourceSpan) (literal : Syntax.CoreLiteral)
    (left right : Syntax.Identifier) : ClosedSourceDataExpression (branch spans literal left right) :=
  .many (.group .reference) (.many .unit (.pair .reference .literal))

private theorem original_branches (spans : Nat → Syntax.SourceSpan) (literal : Syntax.CoreLiteral)
    (left right : Syntax.Identifier) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (environment : Resolved.Environment) (store : Core.Store)
    (leftId rightId : Resolved.LocalId) (leftValue rightValue : Core.Value) (word : Core.Word)
    (leftNamed : LocalNameTable.Lookup names left.value leftId)
    (rightNamed : LocalNameTable.Lookup names right.value rightId)
    (leftFound : Resolved.LocalScope.Lookup environment leftId leftValue)
    (rightFound : Resolved.LocalScope.Lookup environment rightId rightValue)
    (meaning : WordLiteralDenotes literal word) :
    ClosedSourceExpressionEvaluates owner names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (store.map RuntimeValue.ofCore) (branch spans literal left right)
      (RuntimeValue.ofCore (result leftValue rightValue word)) (store.map RuntimeValue.ofCore) ∧
    LocalExpressionEvaluates names environment store (branch spans literal left right)
      (result leftValue rightValue word) store := by
  constructor
  · simp only [result, RuntimeValue.ofCore]
    exact .many (.group (.reference leftNamed (mapped_lookup leftFound)))
      (.many .unit (.pair (.reference rightNamed (mapped_lookup rightFound)) (.wordLiteral meaning)))
  · exact .many (.group (.identifier leftNamed leftFound))
      (.many .unit (.pair (.identifier rightNamed rightFound) (.wordLiteral meaning)))

section Family
variable (spans : Nat → Syntax.SourceSpan) (literal : Syntax.CoreLiteral)
  (guard left right : Syntax.Identifier) (choice : Bool)
  (owner : Resolved.DeclarationId) (names : LocalNameTable)
  (environment : Resolved.Environment) (store : Core.Store)
  (guardId leftId rightId : Resolved.LocalId) (leftValue rightValue : Core.Value) (word : Core.Word)
  (guardNamed : LocalNameTable.Lookup names guard.value guardId)
  (leftNamed : LocalNameTable.Lookup names left.value leftId)
  (rightNamed : LocalNameTable.Lookup names right.value rightId)
  (guardFound : Resolved.LocalScope.Lookup environment guardId (.bool choice))
  (leftFound : Resolved.LocalScope.Lookup environment leftId leftValue)
  (rightFound : Resolved.LocalScope.Lookup environment rightId rightValue)
  (meaning : WordLiteralDenotes literal word)

include guardNamed leftNamed rightNamed guardFound leftFound rightFound meaning

local notation "original" => source spans literal guard left right
local notation "expected" => chosenResult choice leftValue rightValue word

/-- Both actual Bool paths have separately constructed closed/local original derivations. -/
theorem independent_original_data_paths :
    ClosedSourceDataExpression original ∧
    ClosedSourceExpressionEvaluates owner names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (store.map RuntimeValue.ofCore) original
      (RuntimeValue.ofCore expected) (store.map RuntimeValue.ofCore) ∧
    LocalExpressionEvaluates names environment store original expected store := by
  have yes := original_branches spans literal left right owner names environment store
    leftId rightId leftValue rightValue word leftNamed rightNamed leftFound rightFound meaning
  have no := original_branches spans literal right left owner names environment store
    rightId leftId rightValue leftValue word rightNamed leftNamed rightFound leftFound meaning
  refine ⟨.conditional .reference (branch_syntax spans literal left right)
    (branch_syntax spans literal right left), ?_⟩
  cases choice with
  | false =>
      simp only [chosenResult, Bool.false_eq_true, ↓reduceIte]
      exact ⟨.conditionalFalse (.reference guardNamed (by simpa only [RuntimeValue.ofCore] using mapped_lookup guardFound)) no.1,
        .ifFalse (.identifier guardNamed guardFound) no.2⟩
  | true =>
      simp only [chosenResult, ↓reduceIte]
      exact ⟨.conditionalTrue (.reference guardNamed (by simpa only [RuntimeValue.ofCore] using mapped_lookup guardFound)) yes.1,
        .ifTrue (.identifier guardNamed guardFound) yes.2⟩

include owner in
/-- Whole original resolution and exact runtime identity lowering are independently available. -/
theorem independent_full_resolution_and_lowering :
    ∃ resolved core,
      ResolvesLocalExpression names original resolved ∧
      Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core ∧
      Core.Evaluates (Resolved.LocalScope.values environment) store core expected store := by
  let yes : Resolved.Expr := .pair (.var leftId) (.pair .unit (.pair (.var rightId) (.word word)))
  let no : Resolved.Expr := .pair (.var rightId) (.pair .unit (.pair (.var leftId) (.word word)))
  let resolved : Resolved.Expr := .ifE (.var guardId) yes no
  have resolution : ResolvesLocalExpression names original resolved :=
    .conditional (.identifier guardNamed)
      (.many (.group (.identifier leftNamed)) (.many .unit (.pair (.identifier rightNamed) (.wordLiteral meaning))))
      (.many (.group (.identifier rightNamed)) (.many .unit (.pair (.identifier leftNamed) (.wordLiteral meaning))))
  obtain ⟨guardIndex, guardAt, _⟩ := guardFound.indexed
  obtain ⟨leftIndex, leftAt, _⟩ := leftFound.indexed
  obtain ⟨rightIndex, rightAt, _⟩ := rightFound.indexed
  let yesCore : Core.Expr := .pair (.var leftIndex) (.pair .unit (.pair (.var rightIndex) (.word word)))
  let noCore : Core.Expr := .pair (.var rightIndex) (.pair .unit (.pair (.var leftIndex) (.word word)))
  let core : Core.Expr := .ifE (.var guardIndex) yesCore noCore
  have lowered : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core :=
    .ifE (.var guardAt)
      (.pair (.var leftAt) (.pair .unit (.pair (.var rightAt) .word)))
      (.pair (.var rightAt) (.pair .unit (.pair (.var leftAt) .word)))
  have paths := independent_original_data_paths spans literal guard left right choice owner names environment store
    guardId leftId rightId leftValue rightValue word guardNamed leftNamed rightNamed guardFound leftFound rightFound meaning
  exact ⟨resolved, core, resolution, lowered, (resolution.core_evaluates_iff lowered).mp paths.2.2⟩

/-- The raw bridge identifies every actual result with the independent original endpoint. -/
theorem all_actual_local_images {actualValue : RuntimeValue} {actualFinal : List RuntimeValue} :
    ClosedSourceExpressionEvaluates owner names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (store.map RuntimeValue.ofCore) original actualValue actualFinal ↔
    actualValue = RuntimeValue.ofCore expected ∧ actualFinal = store.map RuntimeValue.ofCore := by
  have paths := independent_original_data_paths spans literal guard left right choice owner names environment store
    guardId leftId rightId leftValue rightValue word guardNamed leftNamed rightNamed guardFound leftFound rightFound meaning
  constructor
  · intro actual
    obtain ⟨value, finalStore, same, finalSame, old⟩ := paths.1.local_evaluates_iff.mp actual
    obtain ⟨rfl, rfl⟩ := old.deterministic paths.2.2
    exact ⟨same, finalSame⟩
  · rintro ⟨rfl, rfl⟩
    exact paths.1.local_evaluates_iff.mpr ⟨expected, store, rfl, rfl, paths.2.2⟩

/-- The Core bridge is consumed in both directions at independently recovered runtime indices. -/
theorem all_actual_core_images {actualValue : RuntimeValue} {actualFinal : List RuntimeValue} :
    ∃ resolved core,
      ResolvesLocalExpression names original resolved ∧
      Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core ∧
      Core.Evaluates (Resolved.LocalScope.values environment) store core expected store ∧
      (ClosedSourceExpressionEvaluates owner names
        (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
        (store.map RuntimeValue.ofCore) original actualValue actualFinal ↔
       actualValue = RuntimeValue.ofCore expected ∧ actualFinal = store.map RuntimeValue.ofCore) := by
  obtain ⟨resolved, core, resolution, lowered, independent⟩ :=
    independent_full_resolution_and_lowering spans literal guard left right choice owner names environment store
      guardId leftId rightId leftValue rightValue word guardNamed leftNamed rightNamed guardFound leftFound rightFound meaning
  have paths := independent_original_data_paths spans literal guard left right choice owner names environment store
    guardId leftId rightId leftValue rightValue word guardNamed leftNamed rightNamed guardFound leftFound rightFound meaning
  refine ⟨resolved, core, resolution, lowered, independent, ?_⟩
  constructor
  · intro actual
    obtain ⟨value, finalStore, same, finalSame, evaluated⟩ :=
      (paths.1.core_evaluates_iff resolution lowered).mp actual
    obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated independent
    exact ⟨same, finalSame⟩
  · rintro ⟨rfl, rfl⟩
    exact (paths.1.core_evaluates_iff resolution lowered).mpr
      ⟨expected, store, rfl, rfl, independent⟩

end Family
end Tests.ClosedSourceDataImages
end

section
-- leanmerge: from Solcore.Test.FrontendClosedSourceShortCircuitDataBoundaryProperties
set_option autoImplicit false
namespace Tests.ClosedSourceShortCircuitDataBoundaries
open Solcore Solcore.Frontend

private def ref (span : Syntax.SourceSpan) (name : String) : Syntax.Expr :=
  ⟨span, .identifier ⟨span, name⟩⟩
private def binary (span : Syntax.SourceSpan) (isOr : Bool) (left right : Syntax.Expr) : Syntax.Expr :=
  ⟨span, .binary left ⟨span, if isOr then .logicalOr else .logicalAnd⟩ right⟩
private def unit (span : Syntax.SourceSpan) : Syntax.Expr := ⟨span, .tuple ⟨span, []⟩⟩
private def lambda (span : Syntax.SourceSpan) : Syntax.Expr :=
  ⟨span, .lambda span ⟨span, [⟨span, .inferred ⟨span, "p"⟩⟩]⟩ none
    ⟨span, [⟨span, .returnStmt none⟩]⟩⟩
private def call (span : Syntax.SourceSpan) : Syntax.Expr :=
  ⟨span, .call (lambda span) ⟨span, [unit span]⟩⟩

private theorem skip (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (span : Syntax.SourceSpan) (isOr : Bool) (right : Syntax.Expr) (id : Resolved.LocalId)
    (named : LocalNameTable.Lookup names "flag" id)
    (found : Resolved.LocalScope.Lookup captured id (.bool isOr)) :
    ClosedSourceExpressionEvaluates owner names captured store
      (binary span isOr (ref span "flag") right) (.bool isOr) store := by
  cases isOr
  · exact .andFalse (.reference named found)
  · exact .orTrue (.reference named found)

private theorem outside (span : Syntax.SourceSpan) (isOr : Bool) (left right : Syntax.Expr)
    (excluded : ¬ ClosedSourceDataExpression right) :
    ¬ ClosedSourceDataExpression (binary span isOr left right) := by
  cases isOr
  · intro admitted
    cases admitted with
    | logicalAnd _ child => exact excluded child
    | strictWordBinary _ _ notAnd _ => exact notAnd rfl
  · intro admitted
    cases admitted with
    | logicalOr _ child => exact excluded child
    | strictWordBinary _ _ _ notOr => exact notOr rfl

/-- A short-circuit expression can succeed outside the gate from opaque mixed inputs. -/
theorem skipped_lambda_and_call_remain_outside
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (span : Syntax.SourceSpan) (isOr : Bool) (id : Resolved.LocalId)
    (named : LocalNameTable.Lookup names "flag" id)
    (found : Resolved.LocalScope.Lookup captured id (.bool isOr)) :
    ClosedSourceExpressionEvaluates owner names captured store
      (binary span isOr (ref span "flag") (lambda span)) (.bool isOr) store ∧
    ClosedSourceExpressionEvaluates owner names captured store
      (binary span isOr (ref span "flag") (call span)) (.bool isOr) store ∧
    ¬ ClosedSourceDataExpression (binary span isOr (ref span "flag") (lambda span)) ∧
    ¬ ClosedSourceDataExpression (binary span isOr (ref span "flag") (call span)) := by
  have originalLambda := skip owner names captured store span isOr (lambda span) id named found
  have originalCall := skip owner names captured store span isOr (call span) id named found
  exact ⟨originalLambda, originalCall,
    outside span isOr _ _ (by intro gate; cases gate),
    outside span isOr _ _ (by intro gate; cases gate)⟩

/-- Both written references are admitted; skipping a missing one does not resolve it. -/
theorem admitted_missing_right_skips_without_whole_resolution
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (span : Syntax.SourceSpan) (isOr : Bool) (id : Resolved.LocalId)
    (named : LocalNameTable.Lookup names "flag" id)
    (found : Resolved.LocalScope.Lookup captured id (.bool isOr))
    (missing : LocalNameTable.lookup? names "missing" = none) :
    ClosedSourceDataExpression (binary span isOr (ref span "flag") (ref span "missing")) ∧
    ClosedSourceExpressionEvaluates owner names captured store
      (binary span isOr (ref span "flag") (ref span "missing")) (.bool isOr) store ∧
    (∀ resolved, ¬ ResolvesLocalExpression names
      (binary span isOr (ref span "flag") (ref span "missing")) resolved) := by
  have original := skip owner names captured store span isOr (ref span "missing") id named found
  have absent : ∀ target, ¬ LocalNameTable.Lookup names "missing" target := by
    intro target lookup
    have present := LocalNameTable.lookup?_iff.mpr lookup
    rw [missing] at present
    cases present
  refine ⟨?_, original, ?_⟩
  · cases isOr
    · exact .logicalAnd .reference .reference
    · exact .logicalOr .reference .reference
  · intro resolved resolution
    cases isOr
    · cases resolution with
      | logicalAnd _ right =>
          cases right with
          | identifier lookup => exact absent _ lookup
    · cases resolution with
      | logicalOr _ right =>
          cases right with
          | identifier lookup => exact absent _ lookup

/-- Recursive syntax admission still establishes no successful endpoint. -/
theorem admitted_unit_left_has_no_success
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (span : Syntax.SourceSpan) (isOr : Bool) :
    ClosedSourceDataExpression (binary span isOr (unit span) (unit span)) ∧
    (∀ actual final, ¬ ClosedSourceExpressionEvaluates owner names captured store
      (binary span isOr (unit span) (unit span)) actual final) := by
  constructor
  · cases isOr
    · exact .logicalAnd .unit .unit
    · exact .logicalOr .unit .unit
  · intro actual final evaluated
    cases isOr
    · cases evaluated with
      | andTrue left _ => cases left
      | andFalse left => cases left
      | creation shape => cases shape
      | strictWordBinary _ _ meaning => cases meaning
    · cases evaluated with
      | orTrue left => cases left
      | orFalse left _ => cases left
      | creation shape => cases shape
      | strictWordBinary _ _ meaning => cases meaning

end Tests.ClosedSourceShortCircuitDataBoundaries
end

section
-- leanmerge: from Solcore.Test.FrontendClosedSourceShortCircuitDataImageProperties
set_option autoImplicit false
namespace Tests.ClosedSourceShortCircuitDataImages
open Solcore Solcore.Frontend

private def reference (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span, .identifier name⟩
private def left (spans : Fin 6 → Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨spans 2, .group ⟨spans 3, .unary ⟨spans 4, .logicalNot⟩ (reference (spans 5) name)⟩⟩
private def right (span : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr :=
  ⟨span, .group (reference name.span name)⟩
private def source (spans : Fin 6 → Syntax.SourceSpan) (rightSpan : Syntax.SourceSpan)
    (leftName rightName : Syntax.Identifier) (isOr : Bool) : Syntax.Expr :=
  ⟨spans 0, .binary (left spans leftName)
    ⟨spans 1, if isOr then .logicalOr else .logicalAnd⟩ (right rightSpan rightName)⟩
private def result (isOr input : Bool) (payload : Core.Value) : Core.Value :=
  if (!input) == isOr then .bool isOr else payload
private def resolved (isOr : Bool) (leftId rightId : Resolved.LocalId) : Resolved.Expr :=
  if isOr then .ifE (.unary .boolNot (.var leftId)) (.bool true) (.var rightId)
  else .ifE (.unary .boolNot (.var leftId)) (.var rightId) (.bool false)
private def code (isOr : Bool) (leftIndex rightIndex : Nat) : Core.Expr :=
  if isOr then .ifE (.unary .boolNot (.var leftIndex)) (.bool true) (.var rightIndex)
  else .ifE (.unary .boolNot (.var leftIndex)) (.var rightIndex) (.bool false)
private def embedded (environment : Resolved.Environment) : Resolved.LocalScope RuntimeValue :=
  environment.map (fun row => (row.1, RuntimeValue.ofCore row.2))

private theorem mapped_lookup {environment : Resolved.Environment} {id : Resolved.LocalId}
    {value : Core.Value} (found : Resolved.LocalScope.Lookup environment id value) :
    Resolved.LocalScope.Lookup (embedded environment) id (RuntimeValue.ofCore value) := by
  induction found with
  | head => exact .head
  | tail different _ ih => exact .tail different ih

private theorem local_image {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {environment : Resolved.Environment} {store : Core.Store} {original : Syntax.Expr}
    {expected : Core.Value} (gate : ClosedSourceDataExpression original)
    (path : LocalExpressionEvaluates names environment store original expected store) :
    ∀ actual final, ClosedSourceExpressionEvaluates owner names (embedded environment)
      (store.map RuntimeValue.ofCore) original actual final ↔
      actual = RuntimeValue.ofCore expected ∧ final = store.map RuntimeValue.ofCore := by
  intro actual final
  constructor
  · intro closed
    obtain ⟨value, finalStore, same, finalSame, previous⟩ := gate.local_evaluates_iff.mp closed
    obtain ⟨rfl, rfl⟩ := previous.deterministic path
    exact ⟨same, finalSame⟩
  · rintro ⟨rfl, rfl⟩
    exact gate.local_evaluates_iff.mpr ⟨expected, store, rfl, rfl, path⟩

private theorem core_image {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {environment : Resolved.Environment} {store : Core.Store} {original : Syntax.Expr}
    {expected : Core.Value} {resolved : Resolved.Expr} {core : Core.Expr}
    (gate : ClosedSourceDataExpression original)
    (resolution : ResolvesLocalExpression names original resolved)
    (lowering : Resolved.Lowers environment.ids resolved core)
    (path : Core.Evaluates environment.values store core expected store) :
    ∀ actual final, ClosedSourceExpressionEvaluates owner names (embedded environment)
      (store.map RuntimeValue.ofCore) original actual final ↔
      actual = RuntimeValue.ofCore expected ∧ final = store.map RuntimeValue.ofCore := by
  intro actual final
  constructor
  · intro closed
    obtain ⟨value, finalStore, same, finalSame, previous⟩ :=
      (gate.core_evaluates_iff resolution lowering).mp closed
    obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic previous path
    exact ⟨same, finalSame⟩
  · rintro ⟨rfl, rfl⟩
    exact (gate.core_evaluates_iff resolution lowering).mpr ⟨expected, store, rfl, rfl, path⟩

/-- Whole symbolic paths precede both actual-output images. No typing or unique-row premise. -/
theorem original_and_all_actual_images
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (environment : Resolved.Environment) (store : Core.Store)
    (spans : Fin 6 → Syntax.SourceSpan) (rightSpan : Syntax.SourceSpan)
    (leftName rightName : Syntax.Identifier) (leftId rightId : Resolved.LocalId)
    (isOr input : Bool) (payload : Core.Value)
    (leftNamed : LocalNameTable.Lookup names leftName.value leftId)
    (rightNamed : LocalNameTable.Lookup names rightName.value rightId)
    (leftFound : Resolved.LocalScope.Lookup environment leftId (.bool input))
    (rightFound : Resolved.LocalScope.Lookup environment rightId payload) :
    let original := source spans rightSpan leftName rightName isOr
    let expected := result isOr input payload
    ClosedSourceDataExpression original ∧
    ClosedSourceExpressionEvaluates owner names (embedded environment)
      (store.map RuntimeValue.ofCore) original (RuntimeValue.ofCore expected)
      (store.map RuntimeValue.ofCore) ∧
    LocalExpressionEvaluates names environment store original expected store ∧
    ∃ resolved core,
      ResolvesLocalExpression names original resolved ∧
      Resolved.Lowers environment.ids resolved core ∧
      Core.Evaluates environment.values store core expected store ∧
      (∀ actual final, ClosedSourceExpressionEvaluates owner names (embedded environment)
        (store.map RuntimeValue.ofCore) original actual final ↔
        actual = RuntimeValue.ofCore expected ∧ final = store.map RuntimeValue.ofCore) ∧
      (∀ actual final, ClosedSourceExpressionEvaluates owner names (embedded environment)
        (store.map RuntimeValue.ofCore) original actual final ↔
        actual = RuntimeValue.ofCore expected ∧ final = store.map RuntimeValue.ofCore) := by
  dsimp only
  obtain ⟨li, leftIndex, leftAt⟩ := leftFound.indexed
  obtain ⟨ri, rightIndex, rightAt⟩ := rightFound.indexed
  have admitted : ClosedSourceDataExpression (source spans rightSpan leftName rightName isOr) := by
    cases isOr
    · exact .logicalAnd (.group (.logicalNot .reference)) (.group .reference)
    · exact .logicalOr (.group (.logicalNot .reference)) (.group .reference)
  have closedLeft : ClosedSourceExpressionEvaluates owner names (embedded environment)
      (store.map RuntimeValue.ofCore) (left spans leftName)
      (.bool (!input)) (store.map RuntimeValue.ofCore) :=
    .group (.logicalNot (.reference leftNamed
      (by simpa only [RuntimeValue.ofCore] using mapped_lookup leftFound)))
  have closedRight : ClosedSourceExpressionEvaluates owner names (embedded environment)
      (store.map RuntimeValue.ofCore) (right rightSpan rightName)
      (RuntimeValue.ofCore payload) (store.map RuntimeValue.ofCore) :=
    .group (.reference rightNamed (mapped_lookup rightFound))
  have original : ClosedSourceExpressionEvaluates owner names (embedded environment)
      (store.map RuntimeValue.ofCore) (source spans rightSpan leftName rightName isOr)
      (RuntimeValue.ofCore (result isOr input payload)) (store.map RuntimeValue.ofCore) := by
    cases isOr <;> cases input
    all_goals simp only [source, result, Bool.not_true, Bool.not_false,
      Bool.false_beq, Bool.true_beq,
      ↓reduceIte, RuntimeValue.ofCore]
    · exact .andTrue closedLeft closedRight
    · exact .andFalse closedLeft
    · exact .orTrue closedLeft
    · exact .orFalse closedLeft closedRight
  have localLeft : LocalExpressionEvaluates names environment store
      (left spans leftName) (.bool (!input)) store :=
    .group (.logicalNot (.identifier leftNamed leftFound))
  have localRight : LocalExpressionEvaluates names environment store
      (right rightSpan rightName) payload store := .group (.identifier rightNamed rightFound)
  have localPath : LocalExpressionEvaluates names environment store
      (source spans rightSpan leftName rightName isOr) (result isOr input payload) store := by
    cases isOr <;> cases input
    · exact .andTrue localLeft localRight
    · exact .andFalse localLeft
    · exact .orTrue localLeft
    · exact .orFalse localLeft localRight
  have resolution : ResolvesLocalExpression names
      (source spans rightSpan leftName rightName isOr) (resolved isOr leftId rightId) := by
    cases isOr
    · exact .logicalAnd (.group (.logicalNot (.identifier leftNamed))) (.group (.identifier rightNamed))
    · exact .logicalOr (.group (.logicalNot (.identifier leftNamed))) (.group (.identifier rightNamed))
  have lowering : Resolved.Lowers environment.ids (resolved isOr leftId rightId) (code isOr li ri) := by
    cases isOr
    · exact .ifE (.unary (.var leftIndex)) (.var rightIndex) .bool
    · exact .ifE (.unary (.var leftIndex)) .bool (.var rightIndex)
  have coreLeft : Core.Evaluates environment.values store
      (.unary .boolNot (.var li)) (.bool (!input)) store := .unary (.var leftAt) rfl
  have coreRight : Core.Evaluates environment.values store (.var ri) payload store := .var rightAt
  have corePath : Core.Evaluates environment.values store (code isOr li ri)
      (result isOr input payload) store := by
    cases isOr <;> cases input
    · exact .ifTrue coreLeft coreRight
    · exact .ifFalse coreLeft .bool
    · exact .ifTrue coreLeft .bool
    · exact .ifFalse coreLeft coreRight
  exact ⟨admitted, original, localPath, resolved isOr leftId rightId, code isOr li ri,
    resolution, lowering, corePath, local_image admitted localPath,
    core_image admitted resolution lowering corePath⟩

end Tests.ClosedSourceShortCircuitDataImages
end

section
-- leanmerge: from Solcore.Test.FrontendClosedSourceUnaryDataImageProperties
set_option autoImplicit false
namespace Tests.ClosedSourceUnaryDataImages
open Solcore Solcore.Frontend

private def nest (op : Syntax.UnaryOp) (spans : Nat → Syntax.SourceSpan) :
    Nat → Syntax.Expr → Syntax.Expr
  | 0, leaf => leaf
  | n + 1, leaf => ⟨spans (3 * n), .group
      ⟨spans (3 * n + 1), .unary ⟨spans (3 * n + 2), op⟩ (nest op spans n leaf)⟩⟩

private def bval : Nat → Bool → Bool
  | 0, b => b
  | n + 1, b => !(bval n b)

private def wval : Nat → Core.Word → Core.Word
  | 0, w => w
  | n + 1, w => (wval n w).bitNot

private def resolvedNest (op : Core.UnaryOp) (id : Resolved.LocalId) : Nat → Resolved.Expr
  | 0 => .var id
  | n + 1 => .unary op (resolvedNest op id n)

private def coreNest (op : Core.UnaryOp) (index : Nat) : Nat → Core.Expr
  | 0 => .var index
  | n + 1 => .unary op (coreNest op index n)

private def source (spans : Nat → Syntax.SourceSpan) (nb nw : Nat)
    (boolName wordName payloadName : Syntax.Identifier) : Syntax.Expr :=
  ⟨spans 0, .tuple ⟨spans 1, [
    nest .logicalNot (fun i => spans (8 + 2 * i)) nb ⟨spans 4, .identifier boolName⟩,
    ⟨spans 2, .tuple ⟨spans 3, [
      nest .bitNot (fun i => spans (9 + 2 * i)) nw ⟨spans 5, .identifier wordName⟩,
      ⟨spans 6, .group ⟨spans 7, .identifier payloadName⟩⟩]⟩⟩]⟩⟩

private def result (nb nw : Nat) (b : Bool) (w : Core.Word) (payload : Core.Value) : Core.Value :=
  .pair (.bool (bval nb b)) (.pair (.word (wval nw w)) payload)

private def resolvedSource (nb nw : Nat) (boolId wordId payloadId : Resolved.LocalId) : Resolved.Expr :=
  .pair (resolvedNest .boolNot boolId nb) (.pair (resolvedNest .wordNot wordId nw) (.var payloadId))

private def coreSource (nb nw boolIndex wordIndex payloadIndex : Nat) : Core.Expr :=
  .pair (coreNest .boolNot boolIndex nb) (.pair (coreNest .wordNot wordIndex nw) (.var payloadIndex))

private theorem mapped_lookup {environment : Resolved.Environment} {id : Resolved.LocalId}
    {value : Core.Value} (found : Resolved.LocalScope.Lookup environment id value) :
    Resolved.LocalScope.Lookup (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      id (RuntimeValue.ofCore value) := by
  induction found with
  | head => exact .head
  | tail different _ ih => exact .tail different ih

private theorem bool_paths (n : Nat) (spans : Nat → Syntax.SourceSpan)
    (leafSpan : Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (environment : Resolved.Environment) (store : Core.Store) (input : Bool) (index : Nat)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup environment id (.bool input))
    (indexed : Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids environment) id index)
    (atValue : (Resolved.LocalScope.values environment)[index]? = some (.bool input)) :
    ClosedSourceDataExpression (nest .logicalNot spans n ⟨leafSpan, .identifier name⟩) ∧
    ClosedSourceExpressionEvaluates owner names
      (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      (store.map RuntimeValue.ofCore) (nest .logicalNot spans n ⟨leafSpan, .identifier name⟩)
      (.bool (bval n input)) (store.map RuntimeValue.ofCore) ∧
    LocalExpressionEvaluates names environment store
      (nest .logicalNot spans n ⟨leafSpan, .identifier name⟩) (.bool (bval n input)) store ∧
    ResolvesLocalExpression names (nest .logicalNot spans n ⟨leafSpan, .identifier name⟩)
      (resolvedNest .boolNot id n) ∧
    Resolved.Lowers (Resolved.LocalScope.ids environment)
      (resolvedNest .boolNot id n) (coreNest .boolNot index n) ∧
    Core.Evaluates (Resolved.LocalScope.values environment) store
      (coreNest .boolNot index n) (.bool (bval n input)) store := by
  induction n with
  | zero =>
      exact ⟨.reference, .reference named (by simpa only [RuntimeValue.ofCore, bval] using mapped_lookup found), .identifier named found,
        .identifier named, .var indexed, .var atValue⟩
  | succ n ih =>
      rcases ih with ⟨gate, closed, localPath, resolution, lowering, corePath⟩
      exact ⟨.group (.logicalNot gate), .group (.logicalNot closed), .group (.logicalNot localPath),
        .group (.logicalNot resolution), .unary lowering, .unary corePath rfl⟩

private theorem word_paths (n : Nat) (spans : Nat → Syntax.SourceSpan)
    (leafSpan : Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (environment : Resolved.Environment) (store : Core.Store) (input : Core.Word) (index : Nat)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup environment id (.word input))
    (indexed : Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids environment) id index)
    (atValue : (Resolved.LocalScope.values environment)[index]? = some (.word input)) :
    ClosedSourceDataExpression (nest .bitNot spans n ⟨leafSpan, .identifier name⟩) ∧
    ClosedSourceExpressionEvaluates owner names
      (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      (store.map RuntimeValue.ofCore) (nest .bitNot spans n ⟨leafSpan, .identifier name⟩)
      (.word (wval n input)) (store.map RuntimeValue.ofCore) ∧
    LocalExpressionEvaluates names environment store
      (nest .bitNot spans n ⟨leafSpan, .identifier name⟩) (.word (wval n input)) store ∧
    ResolvesLocalExpression names (nest .bitNot spans n ⟨leafSpan, .identifier name⟩)
      (resolvedNest .wordNot id n) ∧
    Resolved.Lowers (Resolved.LocalScope.ids environment)
      (resolvedNest .wordNot id n) (coreNest .wordNot index n) ∧
    Core.Evaluates (Resolved.LocalScope.values environment) store
      (coreNest .wordNot index n) (.word (wval n input)) store := by
  induction n with
  | zero =>
      exact ⟨.reference, .reference named (by simpa only [RuntimeValue.ofCore, wval] using mapped_lookup found), .identifier named found,
        .identifier named, .var indexed, .var atValue⟩
  | succ n ih =>
      rcases ih with ⟨gate, closed, localPath, resolution, lowering, corePath⟩
      exact ⟨.group (.bitNot gate), .group (.bitNot closed), .group (.bitNot localPath),
        .group (.bitNot resolution), .unary lowering, .unary corePath rfl⟩

private theorem all_images {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {environment : Resolved.Environment} {store : Core.Store} {original : Syntax.Expr}
    {expected : Core.Value} {resolved : Resolved.Expr} {core : Core.Expr}
    (gate : ClosedSourceDataExpression original)
    (localPath : LocalExpressionEvaluates names environment store original expected store)
    (resolution : ResolvesLocalExpression names original resolved)
    (lowering : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core)
    (corePath : Core.Evaluates (Resolved.LocalScope.values environment) store core expected store) :
    ∀ (actual : RuntimeValue) (actualFinal : List RuntimeValue),
      ClosedSourceExpressionEvaluates owner names
        (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
        (store.map RuntimeValue.ofCore) original actual actualFinal ↔
      actual = RuntimeValue.ofCore expected ∧ actualFinal = store.map RuntimeValue.ofCore := by
  intro actual actualFinal
  constructor
  · intro evaluated
    obtain ⟨lv, ls, localValue, _, localActual⟩ := gate.local_evaluates_iff.mp evaluated
    obtain ⟨rfl, rfl⟩ := localActual.deterministic localPath
    obtain ⟨cv, cs, _, coreStore, coreActual⟩ :=
      (gate.core_evaluates_iff resolution lowering).mp evaluated
    obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic coreActual corePath
    exact ⟨localValue, coreStore⟩
  · intro images
    have localActual : ClosedSourceExpressionEvaluates owner names
        (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
        (store.map RuntimeValue.ofCore) original actual actualFinal :=
      gate.local_evaluates_iff.mpr ⟨expected, store, images.1, images.2, localPath⟩
    obtain ⟨value, finalStore, sameValue, sameStore, reflectedCore⟩ :=
      (gate.core_evaluates_iff resolution lowering).mp localActual
    obtain ⟨valueSame, storeSame⟩ := Core.evaluation_deterministic reflectedCore corePath
    rw [valueSame] at sameValue
    rw [storeSame] at sameStore
    exact (gate.core_evaluates_iff resolution lowering).mpr
      ⟨expected, store, sameValue, sameStore, corePath⟩

theorem mixed_nesting_original_and_all_actual_images
    (spans : Nat → Syntax.SourceSpan) (nb nw : Nat)
    (boolName wordName payloadName : Syntax.Identifier)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (environment : Resolved.Environment) (store : Core.Store)
    (boolId wordId payloadId : Resolved.LocalId)
    (inputBool : Bool) (inputWord : Core.Word) (payload : Core.Value)
    (boolNamed : LocalNameTable.Lookup names boolName.value boolId)
    (wordNamed : LocalNameTable.Lookup names wordName.value wordId)
    (payloadNamed : LocalNameTable.Lookup names payloadName.value payloadId)
    (boolFound : Resolved.LocalScope.Lookup environment boolId (.bool inputBool))
    (wordFound : Resolved.LocalScope.Lookup environment wordId (.word inputWord))
    (payloadFound : Resolved.LocalScope.Lookup environment payloadId payload) :
    let original := source spans nb nw boolName wordName payloadName
    let expected := result nb nw inputBool inputWord payload
    ClosedSourceDataExpression original ∧
    ClosedSourceExpressionEvaluates owner names
      (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      (store.map RuntimeValue.ofCore) original
      (RuntimeValue.ofCore expected) (store.map RuntimeValue.ofCore) ∧
    LocalExpressionEvaluates names environment store original expected store ∧
    ∃ resolved core,
      ResolvesLocalExpression names original resolved ∧
      Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core ∧
      Core.Evaluates (Resolved.LocalScope.values environment) store core expected store ∧
      (∀ (actual : RuntimeValue) (actualFinal : List RuntimeValue),
        ClosedSourceExpressionEvaluates owner names
          (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
          (store.map RuntimeValue.ofCore) original actual actualFinal ↔
        actual = RuntimeValue.ofCore expected ∧ actualFinal = store.map RuntimeValue.ofCore) := by
  dsimp only
  obtain ⟨bi, boolAt, boolValue⟩ := boolFound.indexed
  obtain ⟨wi, wordAt, wordValue⟩ := wordFound.indexed
  obtain ⟨qi, payloadAt, payloadValue⟩ := payloadFound.indexed
  obtain ⟨bg, bc, bl, br, blo, bcore⟩ :=
    bool_paths nb (fun i => spans (8 + 2 * i)) (spans 4) boolName boolId
      owner names environment store inputBool bi boolNamed boolFound boolAt boolValue
  obtain ⟨wg, wc, wl, wr, wlo, wcore⟩ :=
    word_paths nw (fun i => spans (9 + 2 * i)) (spans 5) wordName wordId
      owner names environment store inputWord wi wordNamed wordFound wordAt wordValue
  have gate : ClosedSourceDataExpression (source spans nb nw boolName wordName payloadName) :=
    .pair bg (.pair wg (.group .reference))
  have closed : ClosedSourceExpressionEvaluates owner names
      (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      (store.map RuntimeValue.ofCore) (source spans nb nw boolName wordName payloadName)
      (RuntimeValue.ofCore (result nb nw inputBool inputWord payload))
      (store.map RuntimeValue.ofCore) := by
    simp only [result, RuntimeValue.ofCore]
    exact .pair bc (.pair wc (.group (.reference payloadNamed (mapped_lookup payloadFound))))
  have localPath : LocalExpressionEvaluates names environment store
      (source spans nb nw boolName wordName payloadName) (result nb nw inputBool inputWord payload) store :=
    .pair bl (.pair wl (.group (.identifier payloadNamed payloadFound)))
  have resolution : ResolvesLocalExpression names (source spans nb nw boolName wordName payloadName)
      (resolvedSource nb nw boolId wordId payloadId) :=
    .pair br (.pair wr (.group (.identifier payloadNamed)))
  have lowering : Resolved.Lowers (Resolved.LocalScope.ids environment)
      (resolvedSource nb nw boolId wordId payloadId) (coreSource nb nw bi wi qi) :=
    .pair blo (.pair wlo (.var payloadAt))
  have corePath : Core.Evaluates (Resolved.LocalScope.values environment) store
      (coreSource nb nw bi wi qi) (result nb nw inputBool inputWord payload) store :=
    .pair bcore (.pair wcore (.var payloadValue))
  exact ⟨gate, closed, localPath, resolvedSource nb nw boolId wordId payloadId,
    coreSource nb nw bi wi qi, resolution, lowering, corePath,
    all_images gate localPath resolution lowering corePath⟩

end Tests.ClosedSourceUnaryDataImages
end

section
-- leanmerge: from Solcore.Test.FrontendParsedClosedSourceBitNotClosures
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Tests.ParsedClosedSourceBitNotClosures
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"UnaryParsed",by decide⟩],by decide⟩⟩,296⟩
private def caller := {owner with declarationIndex := 297}
private def foreign := {owner with declarationIndex := 901}
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def cid (n : Nat) : Resolved.LocalId := ⟨caller,n⟩
private def fid (n : Nat) : Resolved.LocalId := ⟨foreign,n⟩
private def opaqueCore : V := RuntimeValue.ofCore (.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700])
private def savedNames : LocalNameTable := [("saved",sid 7),("tag",sid 31),("saved",sid 9),("arg",sid 8),("other",fid 900)]
private def savedRows (p : V) (x : Core.Word) := [(sid 32,p),(sid 7,RuntimeValue.word x),(sid 31,.hostFunction .storageWrite),
  (sid 7,.word (x.bitNot)),(sid 8,.pair p .unit),(fid 900,opaqueCore),(sid 9,.unit)]
private def innerNames := ("seed",sid 32)::savedNames
private def innerRows (p : V) (x : Core.Word) := (sid 32,RuntimeValue.pair p .unit)::savedRows p x
private def bodyNames := ("ignored",sid 33)::innerNames
private def bodyRows (p : V) (x : Core.Word) (a : V) := (sid 33,a)::innerRows p x
private def callerNames : LocalNameTable := [("picked",cid 0),("arg",cid 900),("saved",cid 7),("picked",cid 0),("ignored",fid 901)]
private def callerRows (p : V) (x : Core.Word) (made : V) := [(cid 900,RuntimeValue.pair .unit p),(cid 7,.word (x.bitNot)),
  (cid 0,made),(cid 0,p),(sid 7,.word (x.bitNot)),(fid 900,opaqueCore)]
private def stores (p : V) (x : Core.Word) := [[p,opaqueCore,.hostFunction .storageWrite,
  .cellRef (.function .word .word) 900,.pair (.word x) .unit],[opaqueCore,p]]
private theorem fresh0 : Resolved.freshLocalId owner (savedNames.map Prod.snd)=sid 32 := by decide
private theorem fresh1 : Resolved.freshLocalId owner (innerNames.map Prod.snd)=sid 33 := by decide
private theorem freshCaller : Resolved.freshLocalId caller (callerNames.map Prod.snd)=cid 901 := by decide
private def visit (file : Syntax.SourceFile) (src : Syntax.Expr) : IO (List (Nat × Nat)) := do
  let range (s : Syntax.SourceSpan) := (s.startByte,s.endByte)
  let valid (parent : Syntax.SourceSpan) (children : List Syntax.SourceSpan) :=
    parent.isValidFor file && children.all (fun s => s.isValidFor file && parent.contains s)
  match src with
  | ⟨s,.identifier n⟩ => check (valid s [n.span] && s==n.span) "reference spans"; return [range s,range n.span]
  | ⟨s,.group e⟩ =>
    check (valid s [e.span] && s.startByte+1==e.span.startByte && e.span.endByte+1==s.endByte &&
      file.content.toUTF8[s.startByte]?==some 40 && file.content.toUTF8[s.endByte-1]?==some 41) "group spans"
    return range s :: (← visit file e)
  | ⟨s,.unary op e⟩ =>
    check (valid s [op.span,e.span] && op.span.length==1 && op.span.endByte==e.span.startByte &&
      s==Syntax.SourceSpan.cover op.span e.span &&
      file.content.toUTF8[op.span.startByte]?==some (if op.value==.logicalNot then 33 else 126)) "unary spans"
    return range s :: range op.span :: (← visit file e)
  | ⟨s,.call f ⟨args,[a]⟩⟩ =>
    check (valid s [f.span,args] && valid args [a.span] && s==Syntax.SourceSpan.cover f.span args &&
      f.span.endByte==args.startByte && args.startByte+1==a.span.startByte && a.span.endByte+1==args.endByte) "call spans"
    return [range s,range args] ++ (← visit file f) ++ (← visit file a)
  | ⟨s,.lambda kw ⟨ps,parameters⟩ none ⟨bs,[⟨rs,.returnStmt (some e)⟩]⟩⟩ =>
    check (valid s [kw,ps,bs] && valid bs [rs] && valid rs [e.span] && kw.length==3 &&
      kw.endByte==ps.startByte && ps.endByte==bs.startByte &&
      file.content.toUTF8[rs.endByte-1]?==some 59) "lambda body/return spans"
    let mut ranges := [range s,range kw,range ps]
    for p in parameters do
      match p with
      | ⟨ns,.inferred n⟩ => check (valid ps [ns] && valid ns [n.span] && ns==n.span) "parameter spans"
                            ranges := ranges ++ [range ns,range n.span]
      | _ => throw (IO.userError "inferred parameters only")
    return ranges ++ [range bs,range rs] ++ (← visit file e)
  | _ => throw (IO.userError "original closure fixture syntax")
termination_by sizeOf src
private def parsed (text : String) (ranges : List (Nat × Nat) := []) : IO (Syntax.SourceFile × Syntax.Expr) := do
  let file : Syntax.SourceFile := ⟨⟨.main,"word-closure-"++text++".sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok src next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
      src.span==Syntax.SourceSpan.fullFile file) "complete original EOF/diagnostics/span"
    let actual ← visit file src
    check (ranges.isEmpty || actual==ranges) "handwritten complete original ranges"
    return (file,src)
  | _ => throw (IO.userError "parser")
private structure Cert (own : Resolved.DeclarationId) (ns : LocalNameTable)
    (es : Resolved.LocalScope V) (st : List V) (src : Syntax.Expr) where
  value : V
  depth : Nat
  original : E own ns es st src value st
  image : ∀ v s, E own ns es st src v s ↔ v=value ∧ s=st
private def certified {own ns es st src value} (d : Nat) (h : E own ns es st src value st) : Cert own ns es st src :=
  ⟨value,d,h,fun _ _ => ⟨fun other => other.deterministic h,by rintro ⟨rfl,rfl⟩; exact h⟩⟩
private def reference (own : Resolved.DeclarationId) (ns : LocalNameTable) (es : Resolved.LocalScope V)
    (st : List V) (src : Syntax.Expr) : IO (Cert own ns es st src) := do
  match shape : src with
  | ⟨_,.identifier n⟩ => match named : ns.lookup? n.value with
    | some id => match found : es.lookup? id with
      | some v => return certified 1 (by rw [shape]; exact .reference (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))
      | none => throw (IO.userError "capture")
    | none => throw (IO.userError "name")
  | _ => throw (IO.userError "reference")
private def wrap {own ns es st} (base : (e : Syntax.Expr) → IO (Cert own ns es st e))
    (src : Syntax.Expr) : IO (Cert own ns es st src) := do
  match shape : src with
  | ⟨_,.group e⟩ =>
    let h ← wrap base e
    return ⟨h.value,h.depth+1,by rw [shape]; exact .group h.original,by
      intro v s; rw [shape]; constructor
      · intro ev; cases ev with
        | group child => exact (h.image _ _).mp child
        | creation impossible => cases impossible
      · rintro ⟨rfl,rfl⟩; exact .group h.original⟩
  | ⟨s,.unary ⟨ops,.bitNot⟩ e⟩ =>
    let h ← wrap base e
    match value : h.value with
    | .word b =>
      have child : E own ns es st e (.word b) st := value ▸ h.original
      have original : E own ns es st src (.word (b.bitNot)) st := by rw [shape]; exact .bitNot child
      proof original; proof (evaluateClosedSourceExpression?_bitNot h.depth own ns es st s ops e)
      return ⟨.word (b.bitNot),h.depth+1,original,by
        intro v fs; rw [shape]; constructor
        · intro ev
          obtain ⟨a,operand,same⟩ := closedSourceExpressionEvaluates_bitNot_iff.mp ev
          obtain ⟨hv,rfl⟩ := (h.image _ _).mp operand
          rw [value] at hv; cases RuntimeValue.word.inj hv; exact ⟨same,rfl⟩
        · rintro ⟨rfl,rfl⟩; exact closedSourceExpressionEvaluates_bitNot_iff.mpr ⟨b,child,rfl⟩⟩
    | _ => throw (IO.userError "saved primitive operand")
  | _ => base src
termination_by sizeOf src
private def run {own ns es st src} (h : Cert own ns es st src) (d : Nat) (expected : V) (sameValue : h.value=expected) : IO Unit := do
  proof h.original; check (h.depth==d) "independent depth"
  for budget in [0,d-1,d,d+3] do
    match result : evaluateClosedSourceExpression? budget own ns es st src with
    | none => check (budget<d) "expected success"
    | some (v,s) =>
      have same := (h.image v s).mp (evaluateClosedSourceExpression?_sound result)
      proof (And.intro (same.1.trans sameValue) same.2); proof ((h.image v s).mpr same); proof ((h.image expected st).mpr ⟨sameValue.symm,rfl⟩)
      check (budget≥d) "adjacent lower depth"
private def primitive (v : V) (expected : Core.Word) : IO (PLift (v=.word expected)) := do
  match value : v with
  | .word b => if same : b=expected then return ⟨by rw [value,same]⟩ else throw (IO.userError "saved Word")
  | _ => throw (IO.userError "complete scalar shape")
private structure Factory (src : Syntax.Expr) (p : V) (x : Core.Word) where
  inner : Syntax.Expr
  parameter : Syntax.Identifier
  body : Syntax.Block
  child : Syntax.Expr
  bs : Syntax.SourceSpan
  rs : Syntax.SourceSpan
  shape : SourceUnaryLambdaShape inner parameter body
  named : parameter.value="ignored"
  returned : body=⟨bs,[⟨rs,.returnStmt (some child)⟩]⟩
  witness : ∀ a st, E owner bodyNames (bodyRows p x a) st child (.word (x.bitNot)) st
  original : E owner savedNames (savedRows p x) [.unit] src
    (.sourceClosure inner owner innerNames (innerRows p x)) [.unit]
private def factory (src : Syntax.Expr) (p : V) (x : Core.Word) : IO (Factory src p x) := do
  match whole : src with
  | ⟨_,.call ⟨_,.group outer⟩ ⟨_,[arg]⟩⟩ => match outerShape : outer with
    | ⟨_,.lambda _ ⟨_,[⟨_,.inferred seed⟩]⟩ none ob⟩ => match returned : ob with
      | ⟨_,[⟨_,.returnStmt (some inner)⟩]⟩ => match innerShape : inner with
        | ⟨_,.lambda _ ⟨_,[⟨_,.inferred ignored⟩]⟩ none ib⟩ => match bodyShape : ib with
          | ⟨bs,[⟨rs,.returnStmt (some child)⟩]⟩ => match childShape : child with
            | ⟨_,.unary ⟨_,.bitNot⟩ ⟨_,.identifier n⟩⟩ =>
              if valid : seed.value="seed" ∧ ignored.value="ignored" ∧ n.value="saved" then
                let a ← reference owner savedNames (savedRows p x) [.unit] arg
                match argShape : arg with
                | ⟨_,.identifier ⟨_,"arg"⟩⟩ =>
                  have av : E owner savedNames (savedRows p x) [.unit] arg (.pair p .unit) [.unit] := by
                    rw [argShape]; exact .reference (.tail (by change "saved"≠"arg"; decide) (.tail (by change "tag"≠"arg"; decide) (.tail (by change "saved"≠"arg"; decide) .head)))
                      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
                  proof (a.original.deterministic av)
                  have ish : SourceUnaryLambdaShape inner ignored ib := by rw [innerShape]; exact .inferred
                  have osh : SourceUnaryLambdaShape outer seed ob := by rw [outerShape]; exact .inferred
                  have witness (a st) : E owner bodyNames (bodyRows p x a) st child (.word (x.bitNot)) st := by
                    rw [childShape]; exact .bitNot (.reference (id:=sid 7) (by rw [valid.2.2]; exact .tail (by decide) (.tail (by decide) .head))
                      (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
                  have body : B owner innerNames (innerRows p x) [.unit] ob
                      (.sourceClosure inner owner innerNames (innerRows p x)) [.unit] := by
                    rw [returned]; exact .expression (.creation ish)
                  return ⟨inner,ignored,ib,child,bs,rs,ish,valid.2.1,bodyShape,witness,by
                    rw [whole]; exact .call osh (.group (.creation osh)) av
                      (by simpa only [valid.1,fresh0,innerNames,innerRows] using body)⟩
                | _ => throw (IO.userError "factory arg")
              else throw (IO.userError "saved names")
            | _ => throw (IO.userError "saved unary")
          | _ => throw (IO.userError "saved return")
        | _ => throw (IO.userError "saved lambda")
      | _ => throw (IO.userError "factory return")
    | _ => throw (IO.userError "factory lambda")
  | _ => throw (IO.userError "factory call")
private def callCert {src p x} (f : Factory src p x) (made : V)
    (hm : made=.sourceClosure f.inner owner innerNames (innerRows p x)) (st : List V)
    (call : Syntax.Expr) : IO (Cert caller callerNames (callerRows p x made) st call) := do
  match shape : call with
  | ⟨_,.call ⟨_,.identifier ⟨_,"picked"⟩⟩ ⟨_,[⟨_,.identifier ⟨_,"arg"⟩⟩]⟩⟩ =>
    return certified 4 (by
      rw [shape]
      exact ClosedSourceExpressionEvaluates.call f.shape
        (by rw [← hm]; exact .reference .head (.tail (by decide) (.tail (by decide) .head)))
        (.reference (.tail (by change "picked"≠"arg"; decide) .head) .head)
        (by rw [f.named,fresh1]; change B owner bodyNames (bodyRows p x (.pair .unit p)) st f.body (.word (x.bitNot)) st
            rw [f.returned]; exact .expression (f.witness _ _)))
  | _ => throw (IO.userError "caller call")
private def callLeaf (src : Syntax.Expr) : IO Syntax.Expr := do
  match src with
  | ⟨_,.group e⟩ | ⟨_,.unary _ e⟩ => callLeaf e
  | ⟨_,.call _ _⟩ => return src
  | _ => throw (IO.userError "original call leaf")
termination_by sizeOf src
private def exercise (p : V) (x : Core.Word) : IO Unit := do
  let (_,src) ← parsed "(lam(seed){return lam(ignored){return ~saved;};})(arg)"
    [(0,54),(49,54),(0,49),(1,48),(1,4),(4,10),(5,9),(5,9),(10,48),(11,47),
      (18,46),(18,21),(21,30),(22,29),(22,29),(30,46),(31,45),(38,44),(38,39),(39,44),(39,44),(50,53),(50,53)]
  let f ← factory src p x
  proof fresh0; proof fresh1; proof freshCaller; proof (show owner≠caller by decide); proof (Core.Word.bitNot_involutive x)
  run (certified 3 f.original) 3 _ rfl
  match created : evaluateClosedSourceExpression? 3 owner savedNames (savedRows p x) [.unit] src with
  | none => throw (IO.userError "factory returned closure")
  | some (made,creationFinal) =>
    have creationEq := (evaluateClosedSourceExpression?_sound created).deterministic f.original
    proof creationEq
    for entry in (stores p x).attach do
      let st := entry.val
      have noSnapshot : st≠[RuntimeValue.unit] := by
        have member := entry.property
        simp only [stores,List.mem_cons,List.not_mem_nil,or_false] at member
        change entry.val≠[RuntimeValue.unit]
        rcases member with same | same <;> rw [same] <;> intro h <;> have := congrArg List.length h <;> simp at this
      proof noSnapshot; proof (show st≠creationFinal from fun h => noSnapshot (h.trans creationEq.2))
      for (text,d,ranges) in [
          ("picked(arg)",4,[(0,11),(6,11),(0,6),(0,6),(7,10),(7,10)]),
          ("~picked(arg)",5,[(0,12),(0,1),(1,12),(7,12),(1,7),(1,7),(8,11),(8,11)]),
          ("~((picked(arg)))",7,[(0,16),(0,1),(1,16),(2,15),(3,14),(9,14),(3,9),(3,9),(10,13),(10,13)])] do
        let (_,whole) ← parsed text ranges
        let h ← wrap (callCert f made creationEq.1 st) whole
        let expected ← primitive h.value (if d==4 then x.bitNot else x)
        proof expected.down
        let leaf ← callLeaf whole
        match callShape : leaf with
        | ⟨_,.call ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩ ⟨_,[⟨argSpan,.identifier ⟨argName,"arg"⟩⟩]⟩⟩ =>
          let fn : Syntax.Expr := ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩
          let arg : Syntax.Expr := ⟨argSpan,.identifier ⟨argName,"arg"⟩⟩
          let independent ← callCert f made creationEq.1 st leaf
          have callee (s) : E caller callerNames (callerRows p x made) s fn made s :=
            .reference .head (.tail (by decide) (.tail (by decide) .head))
          have argument (s) : E caller callerNames (callerRows p x made) s arg (.pair .unit p) s :=
            .reference (.tail (by change "picked"≠"arg"; decide) .head) .head
          proof independent.original; proof (callee st); proof (argument st)
          match fnRun : evaluateClosedSourceExpression? 1 caller callerNames (callerRows p x made) st fn with
          | none => throw (IO.userError "actual callee")
          | some (actualFn,calleeStore) =>
            have fnEq := (evaluateClosedSourceExpression?_sound fnRun).deterministic (callee st)
            match argRun : evaluateClosedSourceExpression? 1 caller callerNames (callerRows p x made) calleeStore arg with
            | none => throw (IO.userError "actual argument")
            | some (actualArg,bodyStore) =>
              have argEq := (evaluateClosedSourceExpression?_sound argRun).deterministic (argument calleeStore)
              proof fnEq; proof argEq; proof (argEq.2.trans fnEq.2)
              have fnValue := fnEq.1.trans creationEq.1
              match actualShape : actualFn with
              | .sourceClosure savedSource savedOwner sn sc =>
                match selected : sourceUnaryLambdaShape? savedSource with
                | none => throw (IO.userError "actual saved source shape")
                | some (parameter,body) =>
                  let ns := (parameter.value,Resolved.freshLocalId savedOwner (sn.map Prod.snd))::sn
                  let es := (Resolved.freshLocalId savedOwner (sn.map Prod.snd),actualArg)::sc
                  have originalBody : B savedOwner ns es bodyStore body (.word (x.bitNot)) bodyStore := by
                    have same : RuntimeValue.sourceClosure savedSource savedOwner sn sc =
                        .sourceClosure f.inner owner innerNames (innerRows p x) := by simpa only [actualShape] using fnValue
                    obtain ⟨rfl,rfl,rfl,rfl⟩ := RuntimeValue.sourceClosure.inj same
                    have shapeEq := Prod.mk.inj (Option.some.inj
                      (selected.symm.trans (sourceUnaryLambdaShape?_iff.mpr f.shape)))
                    obtain ⟨rfl,rfl⟩ := shapeEq
                    dsimp [ns,es]; rw [f.named,fresh1]
                    change B owner bodyNames (bodyRows p x actualArg) bodyStore f.body (.word (x.bitNot)) bodyStore
                    rw [f.returned]; exact .expression (f.witness _ _)
                  proof originalBody
                  match returned : body with
                  | ⟨bs,[⟨rs,.returnStmt (some child)⟩]⟩ =>
                    have independentChild : E savedOwner ns es bodyStore child (.word (x.bitNot)) bodyStore := by
                      rw [returned] at originalBody; cases originalBody with | expression h => exact h
                    let ch ← wrap (reference savedOwner ns es bodyStore) child
                    proof (ch.original.deterministic independentChild); check (ch.depth==2) "saved unary depth2"
                    have image (v s) : B savedOwner ns es bodyStore body v s ↔ v=ch.value ∧ s=bodyStore := by
                      rw [returned]; constructor
                      · intro ev; cases ev with | expression h => exact (ch.image _ _).mp h
                      · rintro ⟨rfl,rfl⟩; exact .expression ((ch.image _ _).mpr ⟨rfl,rfl⟩)
                    for budget in [0,2,3,6] do
                      match bodyRun : evaluateClosedSourceBody? budget savedOwner ns es bodyStore body with
                      | none => check (budget<3) "saved body success3"
                      | some (v,s) =>
                        have same := (image v s).mp (evaluateClosedSourceBody?_sound bodyRun)
                        proof same; proof ((image v s).mpr same); proof ((image ch.value bodyStore).mpr ⟨rfl,rfl⟩)
                        proof ((evaluateClosedSourceBody?_sound bodyRun).deterministic originalBody)
                        check (budget≥3) "saved body lower boundary"
                  | _ => throw (IO.userError "actual saved return")
              | _ => throw (IO.userError "actual source closure")
              run h d _ expected.down
        | _ => throw (IO.userError "call shape")
end Tests.ParsedClosedSourceBitNotClosures
open Tests.ParsedClosedSourceBitNotClosures in
def Tests.frontendParsedClosedSourceBitNotClosureTests : IO Unit := do
  let (_,inert) ← parsed "lam(){return absent;}"
  let p := Solcore.Frontend.RuntimeValue.sourceClosure inert foreign [("unused",fid 700)] [(fid 700,.bool true)]
  for x in [Solcore.Core.Word.zero,Solcore.Core.Word.maximum,Solcore.Core.Word.ofNatModulo 17] do exercise p x
end

section
-- leanmerge: from Solcore.Test.FrontendParsedClosedSourceDataBodies
/- Original gate/Closed/old-cost certificates precede every successful search.
Actual mixed endpoints enter both image laws before any IO projection. -/
set_option autoImplicit false
namespace Tests.ParsedClosedSourceDataBodies
open Solcore Solcore.Frontend
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"DataBodies",by decide⟩],by decide⟩⟩,174⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=901},700⟩
private def up (e : Resolved.Environment) := e.map (fun row => (row.1,RuntimeValue.ofCore row.2))
private structure EC (t : LocalNameTable) (e : Resolved.Environment) (s : Core.Store)
    (src : Syntax.Expr) (v : Core.Value) (cost : Nat) : Type where
  gate : ClosedSourceDataExpression src
  closed : ClosedSourceExpressionEvaluates owner t (up e) (s.map RuntimeValue.ofCore) src (RuntimeValue.ofCore v) (s.map RuntimeValue.ofCore)
  old : LocalExpressionEvaluatesWithCost t e s src v s cost
private structure BC (t : LocalNameTable) (e : Resolved.Environment) (s : Core.Store)
    (src : Syntax.Block) (v : Core.Value) (cost : Nat) : Type where
  gate : ClosedSourceDataBody src
  closed : ClosedSourceBodyEvaluates owner t (up e) (s.map RuntimeValue.ofCore) src (RuntimeValue.ofCore v) (s.map RuntimeValue.ofCore)
  old : ComputationReturnTreeEvaluatesWithCost LocalExpressionEvaluatesWithCost owner t e s src v s cost
private theorem mapped {e : Resolved.Environment} {i : Resolved.LocalId} {v : Core.Value}
    (h : Resolved.LocalScope.Lookup e i v) : Resolved.LocalScope.Lookup (up e) i (RuntimeValue.ofCore v) := by
  induction h with | head => exact .head | tail different _ ih => exact .tail different ih
private theorem freshNe {t : LocalNameTable} {name : String} {i : Resolved.LocalId}
    (h : LocalNameTable.Lookup t name i) : Resolved.freshLocalId owner (t.map Prod.snd) ≠ i := by
  intro same
  apply Resolved.freshLocalId_not_mem owner (t.map Prod.snd)
  rw [same]; exact List.mem_map.mpr ⟨(name,i),h.mem,rfl⟩
private def ref (t : LocalNameTable) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Expr)
    (name : String) (i : Resolved.LocalId) (v : Core.Value)
    (n : LocalNameTable.Lookup t name i) (f : Resolved.LocalScope.Lookup e i v) : IO (EC t e s src v 1) := do
  match shape : src with
  | ⟨_,.identifier actual⟩ =>
    if h : actual.value=name then return by rw [shape]; exact ⟨.reference,.reference (h ▸ n) (mapped f),.identifier (h ▸ n) f⟩
    else throw (IO.userError "original identifier spelling")
  | _ => throw (IO.userError "original identifier shape")
private def ret (t : LocalNameTable) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Block)
    (name : String) (i : Resolved.LocalId) (v : Core.Value)
    (n : LocalNameTable.Lookup t name i) (f : Resolved.LocalScope.Lookup e i v) : IO (BC t e s src v 1) := do
  match shape : src with
  | ⟨_,[⟨_,.returnStmt (some child)⟩]⟩ =>
    let h ← ref t e s child name i v n f
    return by rw [shape]; exact ⟨.expression h.gate,.expression h.closed,.expression h.old⟩
  | _ => throw (IO.userError "original expression return")
private def branch {t : LocalNameTable} {e : Resolved.Environment} {s : Core.Store}
    {bs marker : Syntax.SourceSpan} {guard : Syntax.Expr} {yes no : Syntax.Block}
    {c : Bool} {x y : Core.Value} {a b : Nat} (h : EC t e s guard (.bool c) 1)
    (ht : BC t e s yes x a) (hf : BC t e s no y b) :
    BC t e s ⟨bs,[⟨marker,.ifThen guard yes (some no)⟩]⟩ (if c then x else y) (1+(if c then a else b)+2) := by
  refine ⟨.conditional h.gate ht.gate hf.gate,?_,?_⟩
  · cases c
    · exact .ifFalse (by simpa only [RuntimeValue.ofCore] using h.closed) hf.closed
    · exact .ifTrue (by simpa only [RuntimeValue.ofCore] using h.closed) ht.closed
  · cases c <;> first | exact .ifTrue h.old ht.old | exact .ifFalse h.old hf.old
private def mainWitness (src : Syntax.Block) (t : LocalNameTable) (e : Resolved.Environment) (s : Core.Store)
    (x saved : Core.Value) (c d : Bool)
    (nx : LocalNameTable.Lookup t "x" (sid 7)) (ns : LocalNameTable.Lookup t "saved" (sid 3))
    (nc : LocalNameTable.Lookup t "c" (sid 31)) (nd : LocalNameTable.Lookup t "d" (sid 11))
    (fx : Resolved.LocalScope.Lookup e (sid 7) x) (fs : Resolved.LocalScope.Lookup e (sid 3) saved)
    (fc : Resolved.LocalScope.Lookup e (sid 31) (.bool c)) (fd : Resolved.LocalScope.Lookup e (sid 11) (.bool d)) :
    IO (BC t e s src (if c then x else if d then .unit else saved) (if c then 17 else 20)) := do
  match shape : src with
  | ⟨bs,[⟨ls,.letDecl ⟨xs,"x"⟩ (some ann) (some ⟨gs,.group init⟩)⟩,⟨ys,.letDecl ⟨yns,"y"⟩ none (some savedSrc)⟩,
      ⟨ps,.expression ⟨pairSpan,.tuple ⟨ts,[left,right]⟩⟩ true⟩,
      ⟨innerSpan,.block [⟨ifSpan,.ifThen guard yes (some ⟨elseSpan,[⟨dSpan,.ifThen dg ⟨bareSpan,[⟨rs,.returnStmt none⟩]⟩ (some no)⟩]⟩)⟩]⟩]⟩ =>
        check (bs.startByte==0 && bs.endByte==88 && gs.startByte==12 && gs.endByte==15 && pairSpan==ts) "original main/group/tuple spans"
        let i := Resolved.freshLocalId owner (t.map Prod.snd)
        let t1 := ("x",i)::t; let e1 := (i,x)::e
        let j := Resolved.freshLocalId owner (t1.map Prod.snd)
        let t2 := ("y",j)::t1; let e2 := (j,saved)::e1
        let hi ← ref t e s init "x" (sid 7) x nx fx
        let hs ← ref t1 e1 s savedSrc "saved" (sid 3) saved (.tail (by decide) ns) (.tail (freshNe ns) fs)
        let hl ← ref t2 e2 s left "x" i x (.tail (by decide) .head) (.tail (Resolved.freshLocalId_cons_fresh_ne owner _) .head)
        let hr ← ref t2 e2 s right "y" j saved .head .head
        let hc ← ref t2 e2 s guard "c" (sid 31) (.bool c) (.tail (by decide) (.tail (by decide) nc))
          (.tail (freshNe (t:=t1) (.tail (by decide) nc)) (.tail (freshNe nc) fc))
        let hd ← ref t2 e2 s dg "d" (sid 11) (.bool d) (.tail (by decide) (.tail (by decide) nd))
          (.tail (freshNe (t:=t1) (.tail (by decide) nd)) (.tail (freshNe nd) fd))
        let ht ← ret t2 e2 s yes "x" i x (.tail (by decide) .head) (.tail (Resolved.freshLocalId_cons_fresh_ne owner _) .head)
        let hf ← ret t2 e2 s no "y" j saved .head .head
        let hb : BC t2 e2 s ⟨bareSpan,[⟨rs,.returnStmt none⟩]⟩ .unit 1 := ⟨.bare,by simpa only [RuntimeValue.ofCore] using ClosedSourceBodyEvaluates.bare,.bare⟩
        let tail := branch (bs:=innerSpan) (marker:=ifSpan) hc ht (branch (bs:=elseSpan) (marker:=dSpan) hd hb hf)
        return by
          rw [shape]
          refine ⟨.binding (.group hi.gate) (.binding hs.gate (.discard (.pair hl.gate hr.gate) (.block tail.gate))),?_,?_⟩
          · apply ClosedSourceBodyEvaluates.binding (.group hi.closed)
            apply ClosedSourceBodyEvaluates.inferred (by simpa only [t1,e1,i,up,List.map_cons] using hs.closed)
            have p := ClosedSourceExpressionEvaluates.pair (span:=pairSpan) (tupleSpan:=ts) hl.closed hr.closed
            simpa only [t2,t1,e2,e1,j,i,up,List.map_cons,RuntimeValue.ofCore] using ClosedSourceBodyEvaluates.discard p (.block tail.closed)
          · have h := ComputationReturnTreeEvaluatesWithCost.discard (blockSpan:=bs) (statementSpan:=ps)
              (LocalExpressionEvaluatesWithCost.pair (span:=pairSpan) (tupleSpan:=ts) hl.old hr.old)
              (ComputationReturnTreeEvaluatesWithCost.block (outerSpan:=bs) tail.old)
            have h := ComputationReturnTreeEvaluatesWithCost.inferred (name:=⟨yns,"y"⟩) (letSpan:=ys) hs.old h
            have h := ComputationReturnTreeEvaluatesWithCost.binding (name:=⟨xs,"x"⟩) (annotation:=ann) (letSpan:=ls)
              (LocalExpressionEvaluatesWithCost.group (span:=gs) hi.old) h
            cases c <;> cases d <;> exact h
  | _ => throw (IO.userError "original main body")
private def bindWitness (src : Syntax.Block) (t : LocalNameTable) (e : Resolved.Environment) (s : Core.Store)
    (spelling : String) (id : Resolved.LocalId) (v : Core.Value) (grouped : Bool)
    (n : LocalNameTable.Lookup t spelling id) (f : Resolved.LocalScope.Lookup e id v) : IO (BC t e s src v 4) := do
  match shape : src with
  | ⟨bs,⟨ls,.letDecl ⟨xs,"x"⟩ ann (some init)⟩::rest⟩ =>
    let hi : EC t e s init v 1 ← if grouped then
      match gi : init with
      | ⟨_,.group child⟩ =>
        let h ← ref t e s child spelling id v n f
        pure (by rw [gi]; exact ⟨.group h.gate,.group h.closed,.group h.old⟩)
      | _ => throw (IO.userError "original grouped initializer")
    else ref t e s init spelling id v n f
    let i := Resolved.freshLocalId owner (t.map Prod.snd)
    let ht ← ret (("x",i)::t) ((i,v)::e) s ⟨bs,rest⟩ "x" i v .head .head
    return by
      rw [shape]; refine ⟨.binding hi.gate ht.gate,?_,?_⟩
      · have htail := ht.closed
        simp only [up,List.map_cons] at htail
        cases ann <;> first | exact .binding hi.closed htail | exact .inferred hi.closed htail
      · cases ann with
        | none => exact ComputationReturnTreeEvaluatesWithCost.inferred (name:=⟨xs,"x"⟩) hi.old ht.old
        | some a => exact ComputationReturnTreeEvaluatesWithCost.binding (name:=⟨xs,"x"⟩) (annotation:=a) hi.old ht.old
  | _ => throw (IO.userError "original single initialized let")
private def shadow (src : Syntax.Block) (t : LocalNameTable) (e : Resolved.Environment) (s : Core.Store)
    (v : Core.Value) (wrapped : Bool) (n : LocalNameTable.Lookup t "saved" (sid 3))
    (f : Resolved.LocalScope.Lookup e (sid 3) v) : IO (BC t e s src v 4) := do
  if wrapped then
    match shape : src with
    | ⟨_,[⟨inner,.block rest⟩]⟩ =>
      let h ← bindWitness ⟨inner,rest⟩ t e s "saved" (sid 3) v false n f
      return by rw [shape]; exact ⟨.block h.gate,.block h.closed,.block h.old⟩
    | _ => throw (IO.userError "original explicit scope block")
  else bindWitness src t e s "saved" (sid 3) v false n f
private def inputs : LocalTypeInputs := ⟨[
  ⟨"x",sid 7,.unit⟩,⟨"saved",sid 3,.unit⟩,⟨"c",sid 31,.bool⟩,
  ⟨"d",sid 11,.bool⟩,⟨"tag",foreign,.word⟩],by decide⟩
private def environment (x saved : Core.Value) (c d : Bool) (tag : Core.Value) : Resolved.Environment :=
  [(sid 7,x),(sid 3,saved),(sid 31,.bool c),(sid 11,.bool d),(foreign,tag)]
private def parsed (text : String) : IO Syntax.Block := do
  let file : Syntax.SourceFile := ⟨⟨.main,"data-bodies.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  match Syntax.Parser.block .require (Syntax.Parser.State.initial file lexed) with
  | .ok body next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && body.span==Syntax.SourceSpan.fullFile file) "original whole block/EOF/spans"
    return body
  | _ => throw (IO.userError "original block parser")
private def scopeWitness (src : Syntax.Block) (x saved : Core.Value) (c : Bool) (tag : Core.Value)
    (s : Core.Store) (swapped wrapped : Bool) :
    IO (BC inputs.names (environment x saved c true tag) s src
      (if c=swapped then x else saved) (if c=swapped then 4 else 7)) := do
  let e := environment x saved c true tag
  match shape : src with
  | ⟨bs,[⟨marker,.ifThen guard yes (some no)⟩]⟩ =>
    let hc ← ref inputs.names e s guard "c" (sid 31) (.bool c)
      (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
    if hs : swapped then
      let ht ← ret inputs.names e s yes "x" (sid 7) x .head .head
      let hf ← shadow no inputs.names e s saved wrapped (.tail (by decide) .head) (.tail (by decide) .head)
      return by rw [shape]; have h := branch (bs:=bs) (marker:=marker) hc ht hf; cases swapped <;> cases c <;> simp_all <;> exact h
    else
      let ht ← shadow yes inputs.names e s saved wrapped (.tail (by decide) .head) (.tail (by decide) .head)
      let hf ← ret inputs.names e s no "x" (sid 7) x .head .head
      return by rw [shape]; have h := branch (bs:=bs) (marker:=marker) hc ht hf; cases swapped <;> cases c <;> simp_all <;> exact h
  | _ => throw (IO.userError "original scope conditional")
private def exercise (t : LocalNameTable) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Block)
    (v : Core.Value) (cost depth : Nat) (h : BC t e s src v cost) (withCore : Bool) : IO Unit := do
  let old := (computationReturnTreeEvaluates_iff_exists_cost localExpressionEvaluates_iff_exists_cost).mpr ⟨cost,h.old⟩
  for budget in [0,depth-1,depth,depth+2] do
    match ran : evaluateClosedSourceBody? budget owner t (up e) (s.map RuntimeValue.ofCore) src with
    | none => check (budget<depth) "closed depth exhaustion"
    | some (mv,ms) =>
      have actual := evaluateClosedSourceBody?_sound ran
      have rawImage := h.gate.local_evaluates_iff.mp actual
      proof (show mv=RuntimeValue.ofCore v ∧ ms=s.map RuntimeValue.ofCore from by
        obtain ⟨a,b,hv,hs,ev⟩ := rawImage
        obtain ⟨k,hk⟩ := (computationReturnTreeEvaluates_iff_exists_cost localExpressionEvaluates_iff_exists_cost).mp ev
        obtain ⟨vv,ss,_⟩ := hk.deterministic (fun aa bb => aa.deterministic bb) h.old
        exact ⟨hv.trans (congrArg _ vv),hs.trans (congrArg _ ss)⟩)
      proof (h.gate.local_evaluates_iff.mpr rawImage)
      proof ((h.gate.local_evaluates_iff.mpr ⟨v,s,rfl,rfl,old⟩).deterministic h.closed)
      if withCore then
        if ht : t=inputs.names then
          if aligned : e.ids=inputs.context.ids then
            match accepted : elaborateComputationReturnTree? elaborateLocalExpression? [(["Unit"],.unit)] owner inputs src with
            | none => throw (IO.userError "whole checker")
            | some (core,ty) =>
              have image := (h.gate.core_evaluates_iff accepted aligned).mp (ht ▸ actual)
              proof image
              check (ty==.unit) "actual whole checked type"
              for fuel in [0,cost-1,cost,cost+1] do
                match runCore : Core.runStateful fuel (.initial core e.values s) with
                | .done a b =>
                  have ev := Core.runStateful_evaluation_sound runCore
                  proof (show ClosedSourceBodyEvaluates owner inputs.names (up e) (s.map RuntimeValue.ofCore) src mv ms from by
                    obtain ⟨x,y,hx,hy,oldCore⟩ := image
                    have ⟨vx,vs⟩ := Core.evaluation_deterministic oldCore ev
                    exact (h.gate.core_evaluates_iff accepted aligned).mpr ⟨a,b,hx.trans (congrArg _ vx),hy.trans (congrArg _ vs),ev⟩)
                  check (a==v && b==s && cost<=fuel && mv.toCore?==some a && ms.mapM RuntimeValue.toCore?==some b) "actual whole payload/store and transition cost"
                | .outOfFuel _ => check (fuel<cost) "Core transition exhaustion"
                | .fault _ _ => throw (IO.userError "unexpected Core fault")
          else throw (IO.userError "full runtime ID order")
        else throw (IO.userError "unique static names")
      check (mv.toCore?==some v && ms.mapM RuntimeValue.toCore?==some s && depth<=budget) "actual raw full image"
private def missingWitness (src : Syntax.Block) (typed : LocalTypeInputs) (x saved tag : Core.Value) (s : Core.Store)
    (nx : LocalNameTable.Lookup typed.names "x" (sid 7)) (nc : LocalNameTable.Lookup typed.names "c" (sid 31)) :
    IO (BC typed.names (environment x saved true true tag) s src x 4) := do
  let e := environment x saved true true tag
  match shape : src with
  | ⟨_,[⟨_,.ifThen guard yes (some ⟨_,[⟨_,.returnStmt (some ⟨_,.identifier missing⟩)⟩]⟩)⟩]⟩ =>
    check (missing.value=="missing") "original unselected missing name"
    let hg ← ref typed.names e s guard "c" (sid 31) (.bool true) nc (.tail (by decide) (.tail (by decide) .head))
    let ht ← ret typed.names e s yes "x" (sid 7) x nx .head
    return by rw [shape]; exact ⟨.conditional hg.gate ht.gate (.expression .reference),
      .ifTrue (by simpa only [RuntimeValue.ofCore] using hg.closed) ht.closed,
      ComputationReturnTreeEvaluatesWithCost.ifTrue hg.old ht.old⟩
  | _ => throw (IO.userError "original missing conditional")
end ParsedClosedSourceDataBodies
open Solcore Solcore.Frontend ParsedClosedSourceDataBodies
def frontendParsedClosedSourceDataBodyTests : IO Unit := do
  let src ← parsed "{let x:Unit=(x);let y=saved;(x,y);{if(c){return x;}else{if(d){return;}else{return y;}}}}"
  let x : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .unit 700]
  let saved : Core.Value := .hostFunction .storageWrite
  let tag : Core.Value := .cellRef (.function .word .word) 700
  for c in [true,false] do
    for d in [true,false] do
      for s in [[],[x,tag]] do
        let e := environment x saved c d tag
        let h ← mainWitness src inputs.names e s x saved c d .head (.tail (by decide) .head)
          (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
          .head (.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head))
          (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
        exercise inputs.names e s src (if c then x else if d then .unit else saved) (if c then 17 else 20) (if c || d then 7 else 8) h true
        for extra in [[],[(sid 7,tag),(foreign,x),(sid 32,saved)]] do
          let t := inputs.names++[("x",sid 7),("saved",sid 3),("foreignAlias",foreign)]
          let raw : Resolved.Environment := [(sid 3,saved),(sid 7,x),(sid 31,.bool c),(sid 11,.bool d),(foreign,tag),(sid 7,tag),(sid 32,tag),(sid 33,x)]++extra
          check (Resolved.freshLocalId owner (t.map Prod.snd)==sid 32 && Resolved.freshLocalId owner (sid 32::t.map Prod.snd)==sid 33) "fresh names ignore environment-only poison"
          let hr ← mainWitness src t raw s x saved c d .head (.tail (by decide) .head)
            (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
            (.tail (by decide) .head) .head (.tail (by decide) (.tail (by decide) .head))
            (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
          exercise t raw s src (if c then x else if d then .unit else saved) (if c then 17 else 20) (if c || d then 7 else 8) hr false
  let unknown ← parsed "{let x:Unknown=(x);return x;}"
  let eu := environment x saved true true tag
  let hu ← bindWitness unknown inputs.names eu [x,tag] "x" (sid 7) x true .head .head
  exercise inputs.names eu [x,tag] unknown x 4 3 hu false
  check ((elaborateComputationReturnTree? elaborateLocalExpression? [(["Unit"],.unit)] owner inputs unknown).isNone) "unknown annotation leaves raw rules unchanged"
  for variant in [0,1,2] do
    let source ← parsed (if variant==0 then "{if(c){let x=saved;return x;}else{return x;}}" else if variant==1 then
      "{if(c){{let x=saved;return x;}}else{return x;}}" else "{if(c){return x;}else{let x=saved;return x;}}")
    for c in [true,false] do
      let swapped := variant==2; let wrapped := variant==1
      let h ← scopeWitness source x saved c tag [x,tag] swapped wrapped
      exercise inputs.names (environment x saved c true tag) [x,tag] source (if c=swapped then x else saved)
        (if c=swapped then 4 else 7) (if c=swapped then 3 else if wrapped then 5 else 4) h (variant != 0)
      check ((elaborateComputationReturnTree? elaborateLocalExpression? [(["Unit"],.unit)] owner inputs source).isSome==(variant != 0)) "then-only name protection and explicit block"
  let missing ← parsed "{if(c){return x;}else{return missing;}}"
  let extended : LocalTypeInputs := ⟨inputs.bindings++[⟨"missing",sid 99,.unit⟩],by decide⟩
  for present in [false,true] do
    let typed := if present then extended else inputs
    let h ← missingWitness missing typed x saved tag [x,tag] (by cases present <;> exact .head)
      (by cases present <;> exact .tail (by decide) (.tail (by decide) .head))
    exercise typed.names eu [x,tag] missing x 4 3 h false
    check ((elaborateComputationReturnTree? elaborateLocalExpression? [(["Unit"],.unit)] owner typed missing).isSome==present &&
      decide (eu.ids=typed.context.ids)==(!present)) "missing spelling versus missing runtime ID: whole acceptance and exact alignment differ"
    let visited := environment x saved false true tag
    check ((evaluateClosedSourceBody? 40 owner typed.names (up visited) ([x,tag].map RuntimeValue.ofCore) missing).isNone) "visited missing name or ID is actual None"
  IO.println "ADR0294 parsed body image, independent depth/cost, raw rows, annotations and scopes GREEN"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedClosedSourceDataMatches
/- Original arms, pattern proofs and two body derivations precede search.
The selected body is read from the AST; image witnesses are eliminated only in Prop. -/
set_option autoImplicit false
namespace Tests.ParsedClosedSourceDataMatches
open Solcore Solcore.Frontend
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"DataMatches",by decide⟩],by decide⟩⟩,174⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=901},700⟩
private def up (e : Resolved.Environment) := e.map (fun row => (row.1,RuntimeValue.ofCore row.2))
private structure EC (t : LocalNameTable) (e : Resolved.Environment) (s : Core.Store)
    (src : Syntax.Expr) (v : Core.Value) (cost : Nat) : Type where
  gate : ClosedSourceDataExpression src
  closed : ClosedSourceExpressionEvaluates owner t (up e) (s.map RuntimeValue.ofCore) src (RuntimeValue.ofCore v) (s.map RuntimeValue.ofCore)
  old : LocalExpressionEvaluatesWithCost t e s src v s cost
private structure BC (t : LocalNameTable) (e : Resolved.Environment) (s : Core.Store)
    (src : Syntax.Block) (v : Core.Value) (cost : Nat) : Type where
  gate : ClosedSourceDataBody src
  closed : ClosedSourceBodyEvaluates owner t (up e) (s.map RuntimeValue.ofCore) src (RuntimeValue.ofCore v) (s.map RuntimeValue.ofCore)
  old : ComputationReturnTreeEvaluatesWithCost LocalExpressionEvaluatesWithCost owner t e s src v s cost
private theorem mapped {e : Resolved.Environment} {i : Resolved.LocalId} {v : Core.Value}
    (h : Resolved.LocalScope.Lookup e i v) : Resolved.LocalScope.Lookup (up e) i (RuntimeValue.ofCore v) := by
  induction h with | head => exact .head | tail different _ ih => exact .tail different ih
private def ref (t : LocalNameTable) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Expr)
    (name : String) (i : Resolved.LocalId) (v : Core.Value)
    (n : LocalNameTable.Lookup t name i) (f : Resolved.LocalScope.Lookup e i v) : IO (EC t e s src v 1) := do
  match shape : src with
  | ⟨_,.identifier actual⟩ =>
    if h : actual.value=name then return by rw [shape]; exact ⟨.reference,.reference (h ▸ n) (mapped f),.identifier (h ▸ n) f⟩
    else throw (IO.userError "original identifier spelling")
  | _ => throw (IO.userError "original identifier shape")
private def ret (t : LocalNameTable) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Block)
    (name : String) (i : Resolved.LocalId) (v : Core.Value)
    (n : LocalNameTable.Lookup t name i) (f : Resolved.LocalScope.Lookup e i v) : IO (BC t e s src v 1) := do
  match shape : src with
  | ⟨_,[⟨_,.returnStmt (some child)⟩]⟩ =>
    let h ← ref t e s child name i v n f
    return by rw [shape]; exact ⟨.expression h.gate,.expression h.closed,.expression h.old⟩
  | _ => throw (IO.userError "original expression return")
private def inputs : LocalTypeInputs := ⟨[
  ⟨"x",sid 7,.unit⟩,⟨"saved",sid 3,.unit⟩,⟨"c",sid 31,.bool⟩,
  ⟨"d",sid 11,.bool⟩,⟨"tag",foreign,.word⟩],by decide⟩
private def environment (x saved : Core.Value) (c d : Bool) (tag : Core.Value) : Resolved.Environment :=
  [(sid 7,x),(sid 3,saved),(sid 31,.bool c),(sid 11,.bool d),(foreign,tag)]
private def parsed (text : String) : IO Syntax.Block := do
  let file : Syntax.SourceFile := ⟨⟨.main,"data-matches.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  match Syntax.Parser.block .require (Syntax.Parser.State.initial file lexed) with
  | .ok body next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && body.span==Syntax.SourceSpan.fullFile file) "original whole block/EOF/spans"
    return body
  | _ => throw (IO.userError "original block parser")
private def zero : Core.Word := ⟨0,by decide⟩
private def literal (p : Syntax.Pattern) : IO (PLift (WordMatchPatternClassifies p (some zero))) := do
  match shape : p with
  | ⟨_,.literal ⟨ls,.decimal spelling⟩⟩ =>
    if h : spelling="0" then
      return by
        apply PLift.up; rw [shape]; refine .literal ⟨_,rfl,?_⟩; subst spelling
        exact .decimal (by decide) (.cons (.decimal (digit:=0) (by decide) (by decide)) .nil)
    else throw (IO.userError "original zero spelling")
  | _ => throw (IO.userError "original literal pattern")
private def wildcard (p : Syntax.Pattern) : IO (PLift (WordMatchPatternClassifies p none)) := do
  match shape : p with
  | ⟨a,.group ⟨b,.group ⟨c,.wildcard marker⟩⟩⟩ =>
    check (a.endByte-a.startByte==5 && b.startByte==a.startByte+1 && b.endByte+1==a.endByte && c==marker && c.startByte==b.startByte+1 && c.endByte+1==b.endByte) "original double-group wildcard spans"
    return by apply PLift.up; rw [shape]; exact .group (.group (.wildcard rfl))
  | _ => throw (IO.userError "original grouped wildcard")
private structure Tail (e : Resolved.Environment) (s : Core.Store) (v : Core.Value) (w : Core.Word)
    (rest : List Syntax.MatchCase) (fallback : Option Syntax.Block) : Type where
  body : Syntax.Block
  cert : BC inputs.names e s body v 1
  gates : ∀ arm ∈ rest, ClosedSourceDataBody arm.value.body
  defaults : ∀ b ∈ fallback.toList, ClosedSourceDataBody b
  old : WordMatchChooses (.word w) rest fallback body 0
  closed : RuntimeWordMatchChooses (.word w) rest fallback body 0
private def originalTail (e : Resolved.Environment) (s : Core.Store) (v : Core.Value) (w : Core.Word)
    (rest : List Syntax.MatchCase) (fallback : Option Syntax.Block)
    (found : Resolved.LocalScope.Lookup e (sid 3) v) : IO (Tail e s v w rest fallback) := do
  match shape : (rest,fallback) with
  | ([arm],none) =>
    let hg := (← wildcard arm.value.pattern).down
    let hb ← ret inputs.names e s arm.value.body "saved" (sid 3) v (.tail (by decide) .head) found
    return by cases shape; exact ⟨arm.value.body,hb,by intro a ha; simp only [List.mem_singleton] at ha; exact ha ▸ hb.gate,by simp,.wildcard hg,.wildcard hg⟩
  | ([],some body) =>
    let hb ← ret inputs.names e s body "saved" (sid 3) v (.tail (by decide) .head) found
    return by cases shape; exact ⟨body,hb,by simp,by intro b hb'; simp only [Option.toList,List.mem_singleton] at hb'; exact hb' ▸ hb.gate,.fallback,.fallback⟩
  | _ => throw (IO.userError "original wildcard or default tail")
private def compared (src : Syntax.Block) (x saved : Core.Value) (w : Core.Word) (s : Core.Store) :
    IO (BC inputs.names (environment x saved true true (.word w)) s src (if w=zero then x else saved) 11) := do
  let e := environment x saved true true (.word w)
  match shape : src with
  | ⟨_,[⟨_,.matchWith ⟨_,⟨guard,[]⟩⟩ ⟨_,⟨first::rest,fallback⟩⟩⟩]⟩ =>
    let hg ← ref inputs.names e s guard "tag" foreign (.word w)
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
    let meaning := (← literal first.value.pattern).down
    let ht ← ret inputs.names e s first.value.body "x" (sid 7) x .head .head
    let hf ← originalTail e s saved w rest fallback (.tail (by decide) .head)
    return by
      rw [shape]; refine ⟨.wordMatch hg.gate ?_ hf.defaults,?_,?_⟩
      · intro arm member; rcases List.mem_cons.mp member with rfl|member; exact ht.gate; exact hf.gates _ member
      · by_cases eq : w=zero
        · subst w; simp only [↓reduceIte]; exact .wordMatch (by simpa only [RuntimeValue.ofCore] using hg.closed) (.hit meaning) ht.closed
        · simp only [eq,↓reduceIte]; exact .wordMatch (by simpa only [RuntimeValue.ofCore] using hg.closed) (.miss meaning eq hf.closed) hf.cert.closed
      · by_cases eq : w=zero
        · subst w; simp only [↓reduceIte]; exact ComputationReturnTreeEvaluatesWithCost.wordMatch hg.old (.hit meaning) ht.old
        · simp only [eq,↓reduceIte]; exact ComputationReturnTreeEvaluatesWithCost.wordMatch hg.old (.miss meaning eq hf.old) hf.cert.old
  | _ => throw (IO.userError "original literal-headed match")
private def immediate (src : Syntax.Block) (x saved tag : Core.Value) (s : Core.Store) (bare : Bool) :
    IO (BC inputs.names (environment x saved true true tag) s src (if bare then .unit else x) 4) := do
  let e := environment x saved true true tag
  match shape : src with
  | ⟨_,[⟨_,.matchWith ⟨_,⟨guard,[]⟩⟩ ⟨_,⟨cases,fallback⟩⟩⟩]⟩ =>
    let hg ← ref inputs.names e s guard "tag" foreign tag
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
    if hb : bare then
      match arms : (cases,fallback) with
      | ([],some ⟨bs,[⟨rs,.returnStmt none⟩]⟩) =>
        return by
          rw [shape]; cases arms; simp only [hb,↓reduceIte]; refine ⟨.wordMatch hg.gate (by simp) ?_,?_,?_⟩
          · intro b member; simp only [Option.toList,List.mem_singleton] at member; subst b; exact .bare
          · simp only [RuntimeValue.ofCore]; exact .wordMatch hg.closed .fallback .bare
          · exact ComputationReturnTreeEvaluatesWithCost.wordMatch hg.old .fallback .bare
      | _ => throw (IO.userError "original default bare return")
    else
      match arms : (cases,fallback) with
      | ([first,second],none) =>
        let meaning := (← wildcard first.value.pattern).down
        let ht ← ret inputs.names e s first.value.body "x" (sid 7) x .head .head
        let hf ← ret inputs.names e s second.value.body "saved" (sid 3) saved (.tail (by decide) .head) (.tail (by decide) .head)
        return by
          rw [shape]; cases arms; simp only [hb]; refine ⟨.wordMatch hg.gate ?_ (by simp),.wordMatch hg.closed (.wildcard meaning) ht.closed,?_⟩
          · intro arm member; rcases List.mem_cons.mp member with rfl|member; exact ht.gate; simp only [List.mem_singleton] at member; exact member ▸ hf.gate
          · exact ComputationReturnTreeEvaluatesWithCost.wordMatch hg.old (.wildcard meaning) ht.old
      | _ => throw (IO.userError "original ignored suffix match")
  | _ => throw (IO.userError "original immediate match")
private def exercise (t : LocalNameTable) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Block)
    (v : Core.Value) (cost depth : Nat) (h : BC t e s src v cost) (withCore : Bool) : IO Unit := do
  let old := (computationReturnTreeEvaluates_iff_exists_cost localExpressionEvaluates_iff_exists_cost).mpr ⟨cost,h.old⟩
  for budget in [0,depth-1,depth,depth+2] do
    match ran : evaluateClosedSourceBody? budget owner t (up e) (s.map RuntimeValue.ofCore) src with
    | none => check (budget<depth) "closed depth exhaustion"
    | some (mv,ms) =>
      have actual := evaluateClosedSourceBody?_sound ran
      have rawImage := h.gate.local_evaluates_iff.mp actual
      proof (show mv=RuntimeValue.ofCore v ∧ ms=s.map RuntimeValue.ofCore from by
        obtain ⟨a,b,hv,hs,ev⟩ := rawImage
        obtain ⟨k,hk⟩ := (computationReturnTreeEvaluates_iff_exists_cost localExpressionEvaluates_iff_exists_cost).mp ev
        obtain ⟨vv,ss,_⟩ := hk.deterministic (fun aa bb => aa.deterministic bb) h.old
        exact ⟨hv.trans (congrArg _ vv),hs.trans (congrArg _ ss)⟩)
      proof (h.gate.local_evaluates_iff.mpr rawImage)
      proof ((h.gate.local_evaluates_iff.mpr ⟨v,s,rfl,rfl,old⟩).deterministic h.closed)
      if withCore then
        if ht : t=inputs.names then
          if aligned : e.ids=inputs.context.ids then
            match accepted : elaborateComputationReturnTree? elaborateLocalExpression? [(["Unit"],.unit)] owner inputs src with
            | none => throw (IO.userError "whole checker")
            | some (core,ty) =>
              have image := (h.gate.core_evaluates_iff accepted aligned).mp (ht ▸ actual)
              proof image
              check (ty==.unit) "actual whole checked type"
              for fuel in [0,cost-1,cost,cost+1] do
                match runCore : Core.runStateful fuel (.initial core e.values s) with
                | .done a b =>
                  have ev := Core.runStateful_evaluation_sound runCore
                  proof (show ClosedSourceBodyEvaluates owner inputs.names (up e) (s.map RuntimeValue.ofCore) src mv ms from by
                    obtain ⟨x,y,hx,hy,oldCore⟩ := image
                    have ⟨vx,vs⟩ := Core.evaluation_deterministic oldCore ev
                    exact (h.gate.core_evaluates_iff accepted aligned).mpr ⟨a,b,hx.trans (congrArg _ vx),hy.trans (congrArg _ vs),ev⟩)
                  check (a==v && b==s && cost<=fuel && mv.toCore?==some a && ms.mapM RuntimeValue.toCore?==some b) "actual whole payload/store and transition cost"
                | .outOfFuel _ => check (fuel<cost) "Core transition exhaustion"
                | .fault _ _ => throw (IO.userError "unexpected Core fault")
          else throw (IO.userError "full runtime ID order")
        else throw (IO.userError "unique static names")
      check (mv.toCore?==some v && ms.mapM RuntimeValue.toCore?==some s && depth<=budget) "actual raw full image"
end ParsedClosedSourceDataMatches
open Solcore Solcore.Frontend ParsedClosedSourceDataMatches
def frontendParsedClosedSourceDataMatchTests : IO Unit := do
  let x : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .unit 700]
  let saved : Core.Value := .hostFunction .storageWrite
  let cell : Core.Value := .cellRef (.function .unit .word) 700
  for withDefault in [true,false] do
    let src ← parsed (if withDefault then "{match(tag){case 0{return x;}default{return saved;}}}" else
      "{match(tag){case 0{return x;}case ((_)){return saved;}}}")
    for w in [zero,⟨1,by decide⟩] do
      for s in [[],[x,cell]] do
        let h ← compared src x saved w s
        exercise inputs.names (environment x saved true true (.word w)) s src (if w=zero then x else saved) 11 3 h true
    let bad := environment x saved true true cell
    check ((evaluateClosedSourceBody? 40 owner inputs.names (up bad) [] src).isNone &&
      (elaborateComputationReturnTree? elaborateLocalExpression? [(["Unit"],.unit)] owner inputs src).isSome) "non-Word before literal is actual None despite whole checker success"
  for kind in [2,3,4] do
    let src ← parsed (if kind==2 then "{match(tag){case ((_)){return x;}case 0{return saved;}}}" else if kind==3 then
      "{match(tag){default{return;}}}" else "{match(tag){case ((_)){return x;}case \"bad\"{return saved;}}}")
    for tag in [x,saved,cell,.word zero] do
      for s in [[],[x,cell]] do
        let bare := kind==3
        let h ← immediate src x saved tag s bare
        exercise inputs.names (environment x saved true true tag) s src (if bare then .unit else x) 4 (if bare then 2 else 3) h (kind != 4)
        check ((elaborateComputationReturnTree? elaborateLocalExpression? [(["Unit"],.unit)] owner inputs src).isSome==(kind != 4)) "all original patterns checked despite wildcard short-circuit"
  IO.println "ADR0294 parsed ordered literal/wildcard/default image and whole-pattern boundaries GREEN"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedClosedSourceLogicalNotClosures
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Tests.ParsedClosedSourceLogicalNotClosures
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"UnaryParsed",by decide⟩],by decide⟩⟩,296⟩
private def caller := {owner with declarationIndex := 297}
private def foreign := {owner with declarationIndex := 901}
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def cid (n : Nat) : Resolved.LocalId := ⟨caller,n⟩
private def fid (n : Nat) : Resolved.LocalId := ⟨foreign,n⟩
private def opaqueCore : V := RuntimeValue.ofCore (.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700])
private def savedNames : LocalNameTable := [("saved",sid 7),("tag",sid 31),("saved",sid 9),("arg",sid 8),("other",fid 900)]
private def savedRows (p : V) (x : Bool) := [(sid 32,p),(sid 7,RuntimeValue.bool x),(sid 31,.hostFunction .storageWrite),
  (sid 7,.bool (!x)),(sid 8,.pair p .unit),(fid 900,opaqueCore),(sid 9,.unit)]
private def innerNames := ("seed",sid 32)::savedNames
private def innerRows (p : V) (x : Bool) := (sid 32,RuntimeValue.pair p .unit)::savedRows p x
private def bodyNames := ("ignored",sid 33)::innerNames
private def bodyRows (p : V) (x : Bool) (a : V) := (sid 33,a)::innerRows p x
private def callerNames : LocalNameTable := [("picked",cid 0),("arg",cid 900),("saved",cid 7),("picked",cid 0),("ignored",fid 901)]
private def callerRows (p : V) (x : Bool) (made : V) := [(cid 900,RuntimeValue.pair .unit p),(cid 7,.bool (!x)),
  (cid 0,made),(cid 0,p),(sid 7,.bool (!x)),(fid 900,opaqueCore)]
private def stores (p : V) (x : Bool) := [[p,opaqueCore,.hostFunction .storageWrite,
  .cellRef (.function .word .word) 900,.pair (.bool x) .unit],[opaqueCore,p]]
private theorem fresh0 : Resolved.freshLocalId owner (savedNames.map Prod.snd)=sid 32 := by decide
private theorem fresh1 : Resolved.freshLocalId owner (innerNames.map Prod.snd)=sid 33 := by decide
private theorem freshCaller : Resolved.freshLocalId caller (callerNames.map Prod.snd)=cid 901 := by decide
private def visit (file : Syntax.SourceFile) (src : Syntax.Expr) : IO (List (Nat × Nat)) := do
  let range (s : Syntax.SourceSpan) := (s.startByte,s.endByte)
  let valid (parent : Syntax.SourceSpan) (children : List Syntax.SourceSpan) :=
    parent.isValidFor file && children.all (fun s => s.isValidFor file && parent.contains s)
  match src with
  | ⟨s,.identifier n⟩ => check (valid s [n.span] && s==n.span) "reference spans"; return [range s,range n.span]
  | ⟨s,.group e⟩ =>
    check (valid s [e.span] && s.startByte+1==e.span.startByte && e.span.endByte+1==s.endByte &&
      file.content.toUTF8[s.startByte]?==some 40 && file.content.toUTF8[s.endByte-1]?==some 41) "group spans"
    return range s :: (← visit file e)
  | ⟨s,.unary op e⟩ =>
    check (valid s [op.span,e.span] && op.span.length==1 && op.span.endByte==e.span.startByte &&
      s==Syntax.SourceSpan.cover op.span e.span &&
      file.content.toUTF8[op.span.startByte]?==some (if op.value==.logicalNot then 33 else 126)) "unary spans"
    return range s :: range op.span :: (← visit file e)
  | ⟨s,.call f ⟨args,[a]⟩⟩ =>
    check (valid s [f.span,args] && valid args [a.span] && s==Syntax.SourceSpan.cover f.span args &&
      f.span.endByte==args.startByte && args.startByte+1==a.span.startByte && a.span.endByte+1==args.endByte) "call spans"
    return [range s,range args] ++ (← visit file f) ++ (← visit file a)
  | ⟨s,.lambda kw ⟨ps,parameters⟩ none ⟨bs,[⟨rs,.returnStmt (some e)⟩]⟩⟩ =>
    check (valid s [kw,ps,bs] && valid bs [rs] && valid rs [e.span] && kw.length==3 &&
      kw.endByte==ps.startByte && ps.endByte==bs.startByte &&
      file.content.toUTF8[rs.endByte-1]?==some 59) "lambda body/return spans"
    let mut ranges := [range s,range kw,range ps]
    for p in parameters do
      match p with
      | ⟨ns,.inferred n⟩ => check (valid ps [ns] && valid ns [n.span] && ns==n.span) "parameter spans"
                            ranges := ranges ++ [range ns,range n.span]
      | _ => throw (IO.userError "inferred parameters only")
    return ranges ++ [range bs,range rs] ++ (← visit file e)
  | _ => throw (IO.userError "original closure fixture syntax")
termination_by sizeOf src
private def parsed (text : String) (ranges : List (Nat × Nat) := []) : IO (Syntax.SourceFile × Syntax.Expr) := do
  let file : Syntax.SourceFile := ⟨⟨.main,"bool-closure-"++text++".sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok src next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
      src.span==Syntax.SourceSpan.fullFile file) "complete original EOF/diagnostics/span"
    let actual ← visit file src
    check (ranges.isEmpty || actual==ranges) "handwritten complete original ranges"
    return (file,src)
  | _ => throw (IO.userError "parser")
private structure Cert (own : Resolved.DeclarationId) (ns : LocalNameTable)
    (es : Resolved.LocalScope V) (st : List V) (src : Syntax.Expr) where
  value : V
  depth : Nat
  original : E own ns es st src value st
  image : ∀ v s, E own ns es st src v s ↔ v=value ∧ s=st
private def certified {own ns es st src value} (d : Nat) (h : E own ns es st src value st) : Cert own ns es st src :=
  ⟨value,d,h,fun _ _ => ⟨fun other => other.deterministic h,by rintro ⟨rfl,rfl⟩; exact h⟩⟩
private def reference (own : Resolved.DeclarationId) (ns : LocalNameTable) (es : Resolved.LocalScope V)
    (st : List V) (src : Syntax.Expr) : IO (Cert own ns es st src) := do
  match shape : src with
  | ⟨_,.identifier n⟩ => match named : ns.lookup? n.value with
    | some id => match found : es.lookup? id with
      | some v => return certified 1 (by rw [shape]; exact .reference (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))
      | none => throw (IO.userError "capture")
    | none => throw (IO.userError "name")
  | _ => throw (IO.userError "reference")
private def wrap {own ns es st} (base : (e : Syntax.Expr) → IO (Cert own ns es st e))
    (src : Syntax.Expr) : IO (Cert own ns es st src) := do
  match shape : src with
  | ⟨_,.group e⟩ =>
    let h ← wrap base e
    return ⟨h.value,h.depth+1,by rw [shape]; exact .group h.original,by
      intro v s; rw [shape]; constructor
      · intro ev; cases ev with
        | group child => exact (h.image _ _).mp child
        | creation impossible => cases impossible
      · rintro ⟨rfl,rfl⟩; exact .group h.original⟩
  | ⟨s,.unary ⟨ops,.logicalNot⟩ e⟩ =>
    let h ← wrap base e
    match value : h.value with
    | .bool b =>
      have child : E own ns es st e (.bool b) st := value ▸ h.original
      have original : E own ns es st src (.bool (!b)) st := by rw [shape]; exact .logicalNot child
      proof original; proof (evaluateClosedSourceExpression?_logicalNot h.depth own ns es st s ops e)
      return ⟨.bool (!b),h.depth+1,original,by
        intro v fs; rw [shape]; constructor
        · intro ev
          obtain ⟨a,operand,same⟩ := closedSourceExpressionEvaluates_logicalNot_iff.mp ev
          obtain ⟨hv,rfl⟩ := (h.image _ _).mp operand
          rw [value] at hv; cases RuntimeValue.bool.inj hv; exact ⟨same,rfl⟩
        · rintro ⟨rfl,rfl⟩; exact closedSourceExpressionEvaluates_logicalNot_iff.mpr ⟨b,child,rfl⟩⟩
    | _ => throw (IO.userError "saved primitive operand")
  | _ => base src
termination_by sizeOf src
private def run {own ns es st src} (h : Cert own ns es st src) (d : Nat) (expected : V) (sameValue : h.value=expected) : IO Unit := do
  proof h.original; check (h.depth==d) "independent depth"
  for budget in [0,d-1,d,d+3] do
    match result : evaluateClosedSourceExpression? budget own ns es st src with
    | none => check (budget<d) "expected success"
    | some (v,s) =>
      have same := (h.image v s).mp (evaluateClosedSourceExpression?_sound result)
      proof (And.intro (same.1.trans sameValue) same.2); proof ((h.image v s).mpr same); proof ((h.image expected st).mpr ⟨sameValue.symm,rfl⟩)
      check (budget≥d) "adjacent lower depth"
private def primitive (v : V) (expected : Bool) : IO (PLift (v=.bool expected)) := do
  match value : v with
  | .bool b => if same : b=expected then return ⟨by rw [value,same]⟩ else throw (IO.userError "saved Bool")
  | _ => throw (IO.userError "complete scalar shape")
private structure Factory (src : Syntax.Expr) (p : V) (x : Bool) where
  inner : Syntax.Expr
  parameter : Syntax.Identifier
  body : Syntax.Block
  child : Syntax.Expr
  bs : Syntax.SourceSpan
  rs : Syntax.SourceSpan
  shape : SourceUnaryLambdaShape inner parameter body
  named : parameter.value="ignored"
  returned : body=⟨bs,[⟨rs,.returnStmt (some child)⟩]⟩
  witness : ∀ a st, E owner bodyNames (bodyRows p x a) st child (.bool (!x)) st
  original : E owner savedNames (savedRows p x) [.unit] src
    (.sourceClosure inner owner innerNames (innerRows p x)) [.unit]
private def factory (src : Syntax.Expr) (p : V) (x : Bool) : IO (Factory src p x) := do
  match whole : src with
  | ⟨_,.call ⟨_,.group outer⟩ ⟨_,[arg]⟩⟩ => match outerShape : outer with
    | ⟨_,.lambda _ ⟨_,[⟨_,.inferred seed⟩]⟩ none ob⟩ => match returned : ob with
      | ⟨_,[⟨_,.returnStmt (some inner)⟩]⟩ => match innerShape : inner with
        | ⟨_,.lambda _ ⟨_,[⟨_,.inferred ignored⟩]⟩ none ib⟩ => match bodyShape : ib with
          | ⟨bs,[⟨rs,.returnStmt (some child)⟩]⟩ => match childShape : child with
            | ⟨_,.unary ⟨_,.logicalNot⟩ ⟨_,.identifier n⟩⟩ =>
              if valid : seed.value="seed" ∧ ignored.value="ignored" ∧ n.value="saved" then
                let a ← reference owner savedNames (savedRows p x) [.unit] arg
                match argShape : arg with
                | ⟨_,.identifier ⟨_,"arg"⟩⟩ =>
                  have av : E owner savedNames (savedRows p x) [.unit] arg (.pair p .unit) [.unit] := by
                    rw [argShape]; exact .reference (.tail (by change "saved"≠"arg"; decide) (.tail (by change "tag"≠"arg"; decide) (.tail (by change "saved"≠"arg"; decide) .head)))
                      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
                  proof (a.original.deterministic av)
                  have ish : SourceUnaryLambdaShape inner ignored ib := by rw [innerShape]; exact .inferred
                  have osh : SourceUnaryLambdaShape outer seed ob := by rw [outerShape]; exact .inferred
                  have witness (a st) : E owner bodyNames (bodyRows p x a) st child (.bool (!x)) st := by
                    rw [childShape]; exact .logicalNot (.reference (id:=sid 7) (by rw [valid.2.2]; exact .tail (by decide) (.tail (by decide) .head))
                      (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
                  have body : B owner innerNames (innerRows p x) [.unit] ob
                      (.sourceClosure inner owner innerNames (innerRows p x)) [.unit] := by
                    rw [returned]; exact .expression (.creation ish)
                  return ⟨inner,ignored,ib,child,bs,rs,ish,valid.2.1,bodyShape,witness,by
                    rw [whole]; exact .call osh (.group (.creation osh)) av
                      (by simpa only [valid.1,fresh0,innerNames,innerRows] using body)⟩
                | _ => throw (IO.userError "factory arg")
              else throw (IO.userError "saved names")
            | _ => throw (IO.userError "saved unary")
          | _ => throw (IO.userError "saved return")
        | _ => throw (IO.userError "saved lambda")
      | _ => throw (IO.userError "factory return")
    | _ => throw (IO.userError "factory lambda")
  | _ => throw (IO.userError "factory call")
private def callCert {src p x} (f : Factory src p x) (made : V)
    (hm : made=.sourceClosure f.inner owner innerNames (innerRows p x)) (st : List V)
    (call : Syntax.Expr) : IO (Cert caller callerNames (callerRows p x made) st call) := do
  match shape : call with
  | ⟨_,.call ⟨_,.identifier ⟨_,"picked"⟩⟩ ⟨_,[⟨_,.identifier ⟨_,"arg"⟩⟩]⟩⟩ =>
    return certified 4 (by
      rw [shape]
      exact ClosedSourceExpressionEvaluates.call f.shape
        (by rw [← hm]; exact .reference .head (.tail (by decide) (.tail (by decide) .head)))
        (.reference (.tail (by change "picked"≠"arg"; decide) .head) .head)
        (by rw [f.named,fresh1]; change B owner bodyNames (bodyRows p x (.pair .unit p)) st f.body (.bool (!x)) st
            rw [f.returned]; exact .expression (f.witness _ _)))
  | _ => throw (IO.userError "caller call")
private def callLeaf (src : Syntax.Expr) : IO Syntax.Expr := do
  match src with
  | ⟨_,.group e⟩ | ⟨_,.unary _ e⟩ => callLeaf e
  | ⟨_,.call _ _⟩ => return src
  | _ => throw (IO.userError "original call leaf")
termination_by sizeOf src
private def exercise (p : V) (x : Bool) : IO Unit := do
  let (_,src) ← parsed "(lam(seed){return lam(ignored){return !saved;};})(arg)"
    [(0,54),(49,54),(0,49),(1,48),(1,4),(4,10),(5,9),(5,9),(10,48),(11,47),
      (18,46),(18,21),(21,30),(22,29),(22,29),(30,46),(31,45),(38,44),(38,39),(39,44),(39,44),(50,53),(50,53)]
  let f ← factory src p x
  proof fresh0; proof fresh1; proof freshCaller; proof (show owner≠caller by decide); proof (Bool.not_not x)
  run (certified 3 f.original) 3 _ rfl
  match created : evaluateClosedSourceExpression? 3 owner savedNames (savedRows p x) [.unit] src with
  | none => throw (IO.userError "factory returned closure")
  | some (made,creationFinal) =>
    have creationEq := (evaluateClosedSourceExpression?_sound created).deterministic f.original
    proof creationEq
    for entry in (stores p x).attach do
      let st := entry.val
      have noSnapshot : st≠[RuntimeValue.unit] := by
        have member := entry.property
        simp only [stores,List.mem_cons,List.not_mem_nil,or_false] at member
        change entry.val≠[RuntimeValue.unit]
        rcases member with same | same <;> rw [same] <;> intro h <;> have := congrArg List.length h <;> simp at this
      proof noSnapshot; proof (show st≠creationFinal from fun h => noSnapshot (h.trans creationEq.2))
      for (text,d,ranges) in [
          ("picked(arg)",4,[(0,11),(6,11),(0,6),(0,6),(7,10),(7,10)]),
          ("!picked(arg)",5,[(0,12),(0,1),(1,12),(7,12),(1,7),(1,7),(8,11),(8,11)]),
          ("!((picked(arg)))",7,[(0,16),(0,1),(1,16),(2,15),(3,14),(9,14),(3,9),(3,9),(10,13),(10,13)])] do
        let (_,whole) ← parsed text ranges
        let h ← wrap (callCert f made creationEq.1 st) whole
        let expected ← primitive h.value (if d==4 then !x else x)
        proof expected.down
        let leaf ← callLeaf whole
        match callShape : leaf with
        | ⟨_,.call ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩ ⟨_,[⟨argSpan,.identifier ⟨argName,"arg"⟩⟩]⟩⟩ =>
          let fn : Syntax.Expr := ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩
          let arg : Syntax.Expr := ⟨argSpan,.identifier ⟨argName,"arg"⟩⟩
          let independent ← callCert f made creationEq.1 st leaf
          have callee (s) : E caller callerNames (callerRows p x made) s fn made s :=
            .reference .head (.tail (by decide) (.tail (by decide) .head))
          have argument (s) : E caller callerNames (callerRows p x made) s arg (.pair .unit p) s :=
            .reference (.tail (by change "picked"≠"arg"; decide) .head) .head
          proof independent.original; proof (callee st); proof (argument st)
          match fnRun : evaluateClosedSourceExpression? 1 caller callerNames (callerRows p x made) st fn with
          | none => throw (IO.userError "actual callee")
          | some (actualFn,calleeStore) =>
            have fnEq := (evaluateClosedSourceExpression?_sound fnRun).deterministic (callee st)
            match argRun : evaluateClosedSourceExpression? 1 caller callerNames (callerRows p x made) calleeStore arg with
            | none => throw (IO.userError "actual argument")
            | some (actualArg,bodyStore) =>
              have argEq := (evaluateClosedSourceExpression?_sound argRun).deterministic (argument calleeStore)
              proof fnEq; proof argEq; proof (argEq.2.trans fnEq.2)
              have fnValue := fnEq.1.trans creationEq.1
              match actualShape : actualFn with
              | .sourceClosure savedSource savedOwner sn sc =>
                match selected : sourceUnaryLambdaShape? savedSource with
                | none => throw (IO.userError "actual saved source shape")
                | some (parameter,body) =>
                  let ns := (parameter.value,Resolved.freshLocalId savedOwner (sn.map Prod.snd))::sn
                  let es := (Resolved.freshLocalId savedOwner (sn.map Prod.snd),actualArg)::sc
                  have originalBody : B savedOwner ns es bodyStore body (.bool (!x)) bodyStore := by
                    have same : RuntimeValue.sourceClosure savedSource savedOwner sn sc =
                        .sourceClosure f.inner owner innerNames (innerRows p x) := by simpa only [actualShape] using fnValue
                    obtain ⟨rfl,rfl,rfl,rfl⟩ := RuntimeValue.sourceClosure.inj same
                    have shapeEq := Prod.mk.inj (Option.some.inj
                      (selected.symm.trans (sourceUnaryLambdaShape?_iff.mpr f.shape)))
                    obtain ⟨rfl,rfl⟩ := shapeEq
                    dsimp [ns,es]; rw [f.named,fresh1]
                    change B owner bodyNames (bodyRows p x actualArg) bodyStore f.body (.bool (!x)) bodyStore
                    rw [f.returned]; exact .expression (f.witness _ _)
                  proof originalBody
                  match returned : body with
                  | ⟨bs,[⟨rs,.returnStmt (some child)⟩]⟩ =>
                    have independentChild : E savedOwner ns es bodyStore child (.bool (!x)) bodyStore := by
                      rw [returned] at originalBody; cases originalBody with | expression h => exact h
                    let ch ← wrap (reference savedOwner ns es bodyStore) child
                    proof (ch.original.deterministic independentChild); check (ch.depth==2) "saved unary depth2"
                    have image (v s) : B savedOwner ns es bodyStore body v s ↔ v=ch.value ∧ s=bodyStore := by
                      rw [returned]; constructor
                      · intro ev; cases ev with | expression h => exact (ch.image _ _).mp h
                      · rintro ⟨rfl,rfl⟩; exact .expression ((ch.image _ _).mpr ⟨rfl,rfl⟩)
                    for budget in [0,2,3,6] do
                      match bodyRun : evaluateClosedSourceBody? budget savedOwner ns es bodyStore body with
                      | none => check (budget<3) "saved body success3"
                      | some (v,s) =>
                        have same := (image v s).mp (evaluateClosedSourceBody?_sound bodyRun)
                        proof same; proof ((image v s).mpr same); proof ((image ch.value bodyStore).mpr ⟨rfl,rfl⟩)
                        proof ((evaluateClosedSourceBody?_sound bodyRun).deterministic originalBody)
                        check (budget≥3) "saved body lower boundary"
                  | _ => throw (IO.userError "actual saved return")
              | _ => throw (IO.userError "actual source closure")
              run h d _ expected.down
        | _ => throw (IO.userError "call shape")
end Tests.ParsedClosedSourceLogicalNotClosures
open Tests.ParsedClosedSourceLogicalNotClosures in
def Tests.frontendParsedClosedSourceLogicalNotClosureTests : IO Unit := do
  let (_,inert) ← parsed "lam(){return absent;}"
  let p := Solcore.Frontend.RuntimeValue.sourceClosure inert foreign [("unused",fid 700)] [(fid 700,.bool true)]
  for x in [false,true] do exercise p x
end

section
-- leanmerge: from Solcore.Test.FrontendParsedClosedSourceShortCircuit
/-! Parsed IO consumers. Closed raw-store depth and independently costed
Core-valued source evaluation are separate lanes, not a data-image bridge.
Every original group, identifier and operator range is checked by hand.
Left group depth/cost = 2/1; right grouped double-not = 4/5;
whole skip = 3/4 and whole selected = 5/8. -/
set_option autoImplicit false
namespace Tests.ParsedClosedSourceShortCircuit
open Solcore Solcore.Frontend
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"ParsedShortCircuit",by decide⟩],by decide⟩⟩,298⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.DeclarationId := {owner with declarationIndex := 901}
private def fid : Resolved.LocalId := ⟨foreign,900⟩
private def names : LocalNameTable := [("flag",sid 7),("right",sid 31),("flag",fid)]
private def rawRows (p : RuntimeValue) (left right : Bool) : Resolved.LocalScope RuntimeValue :=
  [(sid 0,p),(sid 7,.bool left),(sid 31,.bool right),(sid 7,.word Core.Word.maximum),(fid,p)]
private def opaqueCore : Core.Value :=
  .closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700]
private def coreRows (left right : Bool) : Resolved.Environment :=
  [(sid 7,.bool left),(sid 31,.bool right),(sid 7,opaqueCore),(fid,.unit)]
private structure Ranges where
  whole : Syntax.SourceSpan
  op : Syntax.SourceSpan
  lg : Syntax.SourceSpan
  lr : Syntax.SourceSpan
  ln : Syntax.SourceSpan
  rg : Syntax.SourceSpan
  uo : Syntax.SourceSpan
  oo : Syntax.SourceSpan
  ui : Syntax.SourceSpan
  oi : Syntax.SourceSpan
  rr : Syntax.SourceSpan
  rn : Syntax.SourceSpan
private def allRanges (s : Ranges) := [s.whole,s.op,s.lg,s.lr,s.ln,s.rg,s.uo,s.oo,s.ui,s.oi,s.rr,s.rn]
private def leftSource (s : Ranges) : Syntax.Expr := ⟨s.lg,.group ⟨s.lr,.identifier ⟨s.ln,"flag"⟩⟩⟩
private def rightSource (s : Ranges) : Syntax.Expr :=
  ⟨s.rg,.group ⟨s.uo,.unary ⟨s.oo,.logicalNot⟩ ⟨s.ui,.unary ⟨s.oi,.logicalNot⟩
    ⟨s.rr,.identifier ⟨s.rn,"right"⟩⟩⟩⟩⟩
private def source (s : Ranges) (isOr : Bool) : Syntax.Expr :=
  ⟨s.whole,.binary (leftSource s) ⟨s.op,if isOr then .logicalOr else .logicalAnd⟩ (rightSource s)⟩
private def answer (isOr left right : Bool) := if left == isOr then isOr else right
private def depth (isOr left : Bool) : Nat := if left == isOr then 3 else 5
private def cost (isOr left : Bool) : Nat := if left == isOr then 4 else 8
private def resolved (isOr : Bool) : Resolved.Expr :=
  let r := Resolved.Expr.unary .boolNot (.unary .boolNot (.var (sid 31)))
  if isOr then .ifE (.var (sid 7)) (.bool true) r else .ifE (.var (sid 7)) r (.bool false)
private def core (isOr : Bool) : Core.Expr :=
  let r := Core.Expr.unary .boolNot (.unary .boolNot (.var 1))
  if isOr then .ifE (.var 0) (.bool true) r else .ifE (.var 0) r (.bool false)

private theorem original (s : Ranges) (isOr left right : Bool) (p : RuntimeValue)
    (store : List RuntimeValue) : ClosedSourceExpressionEvaluates owner names (rawRows p left right)
      store (source s isOr) (.bool (answer isOr left right)) store := by
  have l : ClosedSourceExpressionEvaluates owner names (rawRows p left right) store
      (leftSource s) (.bool left) store := .group (.reference .head (.tail (by decide) .head))
  have leaf : ClosedSourceExpressionEvaluates owner names (rawRows p left right) store
      ⟨s.rr,.identifier ⟨s.rn,"right"⟩⟩ (.bool right) store :=
    .reference (.tail (by change "flag" ≠ "right"; decide) .head) (.tail (by decide) (.tail (by decide) .head))
  have r : ClosedSourceExpressionEvaluates owner names (rawRows p left right) store
      (rightSource s) (.bool right) store := by
    simpa only [rightSource,Bool.not_not] using ClosedSourceExpressionEvaluates.group (span:=s.rg)
      (ClosedSourceExpressionEvaluates.logicalNot (span:=s.uo) (operatorSpan:=s.oo)
        (ClosedSourceExpressionEvaluates.logicalNot (span:=s.ui) (operatorSpan:=s.oi) leaf))
  cases isOr <;> cases left
  · exact .andFalse l
  · exact .andTrue l r
  · exact .orFalse l r
  · exact .orTrue l

private theorem cutoff (s : Ranges) (isOr left right : Bool) (p : RuntimeValue)
    (store : List RuntimeValue) : ∀ n, evaluateClosedSourceExpression? n owner names (rawRows p left right)
      store (source s isOr) = if depth isOr left ≤ n then some (.bool (answer isOr left right),store) else none := by
  cases isOr <;> cases left <;> cases right
  all_goals
    intro n
    by_cases high : 5 ≤ n
    · have split : n = (n-5)+5 := by omega
      rw [split]
      simp [source,leftSource,rightSource,depth,answer,evaluateClosedSourceExpression?,
        names,rawRows,LocalNameTable.lookup?,Resolved.LocalScope.lookup?,sid,owner,fid,foreign]
    · have small : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 := by omega
      rcases small with rfl | rfl | rfl | rfl | rfl
      all_goals simp [source,leftSource,rightSource,depth,answer,evaluateClosedSourceExpression?,
        names,rawRows,LocalNameTable.lookup?,Resolved.LocalScope.lookup?,sid,owner,fid,foreign]

private theorem localOriginal (s : Ranges) (isOr left right : Bool) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (coreRows left right) store (source s isOr)
      (.bool (answer isOr left right)) store (cost isOr left) := by
  have l : LocalExpressionEvaluatesWithCost names (coreRows left right) store
      (leftSource s) (.bool left) store 1 := .group (.identifier .head .head)
  have leaf : LocalExpressionEvaluatesWithCost names (coreRows left right) store
      ⟨s.rr,.identifier ⟨s.rn,"right"⟩⟩ (.bool right) store 1 :=
    .identifier (.tail (by change "flag" ≠ "right"; decide) .head) (.tail (by decide) .head)
  have r : LocalExpressionEvaluatesWithCost names (coreRows left right) store
      (rightSource s) (.bool right) store 5 := by
    simpa only [rightSource,Bool.not_not] using LocalExpressionEvaluatesWithCost.group (span:=s.rg)
      (LocalExpressionEvaluatesWithCost.logicalNot (span:=s.uo) (operatorSpan:=s.oo)
        (LocalExpressionEvaluatesWithCost.logicalNot (span:=s.ui) (operatorSpan:=s.oi) leaf))
  cases isOr <;> cases left
  · exact .andFalse l
  · exact .andTrue l r
  · exact .orFalse l r
  · exact .orTrue l
private theorem resolution (s : Ranges) (isOr : Bool) :
    ResolvesLocalExpression names (source s isOr) (resolved isOr) := by
  cases isOr
  · exact .logicalAnd (.group (.identifier .head))
      (.group (.logicalNot (.logicalNot (.identifier (.tail (by change "flag" ≠ "right"; decide) .head)))))
  · exact .logicalOr (.group (.identifier .head))
      (.group (.logicalNot (.logicalNot (.identifier (.tail (by change "flag" ≠ "right"; decide) .head)))))
private theorem lowering (isOr left right : Bool) :
    Resolved.Lowers (Resolved.LocalScope.ids (coreRows left right)) (resolved isOr) (core isOr) := by
  cases isOr
  · exact .ifE (.var .head) (.unary (.unary (.var (.tail (by change sid 7 ≠ sid 31; decide) .head)))) .bool
  · exact .ifE (.var .head) .bool (.unary (.unary (.var (.tail (by change sid 7 ≠ sid 31; decide) .head))))
private theorem image {captured store src value}
    (h : ClosedSourceExpressionEvaluates owner names captured store src value store) :
    ∀ a st, ClosedSourceExpressionEvaluates owner names captured store src a st ↔ a=value ∧ st=store := by
  intro a st; constructor
  · exact fun e => e.deterministic h
  · rintro ⟨rfl,rfl⟩; exact h
private theorem coreImage {e s c v k} (h : Core.Steps k (.initial c e s) (.final v s)) (fuel a st) :
    Core.runStateful fuel (.initial c e s) = .done a st ↔ a=v ∧ st=s ∧ k≤fuel := by
  constructor
  · intro run
    obtain ⟨rfl,rfl⟩ := Core.evaluation_deterministic (Core.runStateful_evaluation_sound run)
      (Core.steps_from_initial_sound h)
    exact ⟨rfl,rfl,h.runStateful_done_iff.mp run⟩
  · rintro ⟨rfl,rfl,enough⟩; exact h.runStateful_done_iff.mpr enough
private theorem ruleRoundtrip {s : Ranges} {isOr : Bool} {captured store a st}
    (h : ClosedSourceExpressionEvaluates owner names captured store (source s isOr) a st) :
    ClosedSourceExpressionEvaluates owner names captured store (source s isOr) a st := by
  cases isOr
  · exact closedSourceExpressionEvaluates_logicalAnd_iff.mpr
      (closedSourceExpressionEvaluates_logicalAnd_iff.mp h)
  · exact closedSourceExpressionEvaluates_logicalOr_iff.mpr
      (closedSourceExpressionEvaluates_logicalOr_iff.mp h)

private def exercise (src : Syntax.Expr) (s : Ranges) (isOr : Bool) (shape : src=source s isOr)
    (left right : Bool) (p : RuntimeValue) (rawStore : List RuntimeValue) (coreStore : Core.Store) : IO Unit := do
  have orig : ClosedSourceExpressionEvaluates owner names (rawRows p left right)
      rawStore src (.bool (answer isOr left right)) rawStore := by rw [shape]; exact original s isOr left right p rawStore
  have cut : ∀ n, evaluateClosedSourceExpression? n owner names (rawRows p left right) rawStore src =
      if depth isOr left ≤ n then some (.bool (answer isOr left right),rawStore) else none := by
    intro n; rw [shape]; exact cutoff s isOr left right p rawStore n
  proof orig; proof cut
  have lc : LocalExpressionEvaluatesWithCost names (coreRows left right) coreStore src
      (.bool (answer isOr left right)) coreStore (cost isOr left) := by rw [shape]; exact localOriginal s isOr left right coreStore
  have res : ResolvesLocalExpression names src (resolved isOr) := by rw [shape]; exact resolution s isOr
  have low := lowering isOr left right
  have paths := lc.toStepsWithContinuation res low
  have steps := lc.toSteps res low
  proof lc; proof res; proof low; proof paths
  for n in [0,depth isOr left-1,depth isOr left,depth isOr left+3] do
    proof (cut n)
    match run : evaluateClosedSourceExpression? n owner names (rawRows p left right) rawStore src with
    | none =>
      have below : n < depth isOr left := by
        by_cases enough : depth isOr left ≤ n
        · have expected := cut n
          rw [run,if_pos enough] at expected
          cases expected
        · omega
      proof below; check (n < depth isOr left) "raw exact depth rejection"
    | some (a,st) =>
      have actual := evaluateClosedSourceExpression?_sound run
      have endpoints := (image orig a st).mp actual
      proof endpoints; proof ((image orig a st).mpr endpoints)
      proof (ruleRoundtrip (s:=s) (isOr:=isOr) (by rw [← shape]; exact actual))
      have enough : depth isOr left ≤ n := by
        by_cases enough : depth isOr left ≤ n
        · exact enough
        · have expected := cut n
          rw [run,if_neg enough] at expected
          cases expected
      have back : evaluateClosedSourceExpression? n owner names (rawRows p left right) rawStore src = some (a,st) := by
        rw [cut n,if_pos enough,endpoints.1,endpoints.2]
      proof back; check (n ≥ depth isOr left) "raw complete value/store image"
  for k in [0,cost isOr left-1,cost isOr left,cost isOr left+3] do
    match run : Core.runStateful k (.initial (core isOr) (coreRows left right).values coreStore) with
    | .done a st =>
      have endpoints := (coreImage steps k a st).mp run
      proof endpoints; proof ((coreImage steps k a st).mpr endpoints)
      check (a == .bool (answer isOr left right) && st == coreStore && k ≥ cost isOr left) "Core full actual endpoint/cost"
    | .outOfFuel suspended =>
      have below := steps.runStateful_outOfFuel_iff.mp ⟨suspended,run⟩
      proof below; proof (steps.runStateful_outOfFuel_iff.mpr below)
      check (k < cost isOr left) "Core exact exhaustion"
    | _ => throw (IO.userError "independent Core lane stuck")

private def parsedCase (isOr : Bool) : IO Unit := do
  let text := if isOr then "(flag) || (!!right)" else "(flag) && (!!right)"
  let file : Syntax.SourceFile := ⟨⟨.main,"parsed-short-circuit.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "short-circuit lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok src next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
      src.span == Syntax.SourceSpan.fullFile file) "whole AST / source ownership / EOF / zero diagnostics"
    match shape : src with
    | ⟨whole,.binary ⟨lg,.group ⟨lr,.identifier ⟨ln,"flag"⟩⟩⟩ ⟨opSpan,op⟩
        ⟨rg,.group ⟨uo,.unary ⟨oo,.logicalNot⟩ ⟨ui,.unary ⟨oi,.logicalNot⟩
          ⟨rr,.identifier ⟨rn,"right"⟩⟩⟩⟩⟩⟩ =>
      let s : Ranges := ⟨whole,opSpan,lg,lr,ln,rg,uo,oo,ui,oi,rr,rn⟩
      check ((allRanges s).all (fun r => r.isValidFor file) &&
        (allRanges s).map (fun r => (r.startByte,r.endByte)) ==
          [(0,19),(7,9),(0,6),(1,5),(1,5),(10,19),(11,18),(11,12),(12,18),(12,13),(13,18),(13,18)])
        "all handwritten expression, group, identifier and operator ranges"
      if operator : op = (if isOr then .logicalOr else .logicalAnd) then
        have originalShape : src = source s isOr := by rw [shape,operator]; rfl
        let inert : Syntax.Expr := ⟨whole,.identifier ⟨whole,"opaque-unused"⟩⟩
        let p := RuntimeValue.sourceClosure inert foreign [("flag",fid)] [(fid,.unit)]
        for left in [false,true] do
          for right in [false,true] do
            for rawStore in [[],[p,RuntimeValue.ofCore opaqueCore,.hostFunction .storageWrite,
                .cellRef (.function .word .word) 900,.pair .unit (.word Core.Word.maximum)]] do
              for coreStore in [[],[opaqueCore,.hostFunction .storageWrite,.cellRef .word 700,.unit]] do
                exercise src s isOr originalShape left right p rawStore coreStore
      else throw (IO.userError "actual parsed short-circuit operator")
    | _ => throw (IO.userError "actual original groups/double-not/identifiers")
  | _ => throw (IO.userError "short-circuit parser")
end Tests.ParsedClosedSourceShortCircuit
open Tests.ParsedClosedSourceShortCircuit in
def Tests.frontendParsedClosedSourceShortCircuitTests : IO Unit := do
  parsedCase false
  parsedCase true
end

section
-- leanmerge: from Solcore.Test.FrontendParsedClosedSourceShortCircuitBoundaries
/- Original AST witnesses precede every run. Actual full
values/stores are retained through creation, selection and a foreign saved call.
No typing, data-image, Core-cost, NoDup or parser-correctness theorem is claimed. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Tests.ParsedClosedSourceShortCircuitBoundaries
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ShortCircuit",by decide⟩],by decide⟩⟩,298⟩
private def caller := {owner with declarationIndex := 901}
private def lid (own : Resolved.DeclarationId) (i : Nat) : Resolved.LocalId := ⟨own,i⟩
private def names (own : Resolved.DeclarationId) : LocalNameTable :=
  [("flag",lid own 0),("right",lid own 1),("saved",lid own 1),("p",lid own 2)]
private def rows (own : Resolved.DeclarationId) (b : Bool) (p : V)
    (tail : Resolved.LocalScope V) := (lid own 0,RuntimeValue.bool b)::(lid own 1,p)::(lid own 2,RuntimeValue.unit)::tail
private theorem index_ne (own : Resolved.DeclarationId) {i j : Nat} (h : i≠j) : lid own i≠lid own j :=
  fun equal => h (congrArg Resolved.LocalId.binderIndex equal)
private def span (f : Syntax.SourceFile) (a z : Nat) : Syntax.SourceSpan := ⟨f.id,a,z⟩
private def ref (f : Syntax.SourceFile) (a z : Nat) (n : String) : Syntax.Expr :=
  ⟨span f a z,.identifier ⟨span f a z,n⟩⟩
private def binaryAST (b : Bool) (right : String) (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f 0 (8+right.utf8ByteSize),.binary (ref f 0 4 "flag")
    ⟨span f 5 7,if b then .logicalAnd else .logicalOr⟩ (ref f 8 (8+right.utf8ByteSize) right)⟩
private def factoryAST (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f 0 19,.group ⟨span f 1 18,.lambda (span f 1 4)
    ⟨span f 4 7,[⟨span f 5 6,.inferred ⟨span f 5 6,"p"⟩⟩]⟩ none
    ⟨span f 7 18,[⟨span f 8 17,.returnStmt (some (ref f 15 16 "p"))⟩]⟩⟩⟩
private def callAST (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f 0 9,.call (ref f 0 6 "picked") ⟨span f 6 9,[ref f 7 8 "p"]⟩⟩
private def parsed (text : String) (expected : Syntax.SourceFile → Syntax.Expr) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"short-circuit-"++text++".sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok src next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && next.file==file &&
      src.span==Syntax.SourceSpan.fullFile file && src==expected file) "complete original AST/ranges/source/EOF"
    return src
  | _ => throw (IO.userError "parser")
private theorem endpoint {own ns es st src v} (h : E own ns es st src v st) :
    ∀ a s, E own ns es st src a s ↔ a=v ∧ s=st := by
  intro a s; exact ⟨fun other => other.deterministic h,by rintro ⟨rfl,rfl⟩; exact h⟩
private structure Cert (own : Resolved.DeclarationId) (ns : LocalNameTable)
    (es : Resolved.LocalScope V) (st : List V) (src : Syntax.Expr) (v : V) where
  depth : Nat
  original : E own ns es st src v st
  image : ∀ a s, E own ns es st src a s ↔ a=v ∧ s=st
private def certified {own ns es st src v} (d : Nat) (h : E own ns es st src v st) : Cert own ns es st src v :=
  ⟨d,h,endpoint h⟩
private structure Actual (own : Resolved.DeclarationId) (ns : LocalNameTable)
    (es : Resolved.LocalScope V) (st : List V) (src : Syntax.Expr) (v : V) where
  value : V
  store : List V
  evidence : E own ns es st src value store
  endpoint : value=v ∧ store=st
private def run {own ns es st src v} (h : Cert own ns es st src v) : IO (Actual own ns es st src v) := do
  proof h.original
  for budget in [0,h.depth-1,h.depth,h.depth+3] do
    match result : evaluateClosedSourceExpression? budget own ns es st src with
    | none => check (budget<h.depth) "expected positive depth"
    | some (a,s) =>
      have same := (h.image a s).mp (evaluateClosedSourceExpression?_sound result)
      proof same; proof ((h.image a s).mpr same); proof ((h.image v st).mpr ⟨rfl,rfl⟩)
      check (budget≥h.depth) "adjacent lower depth"
  match result : evaluateClosedSourceExpression? h.depth own ns es st src with
  | none => throw (IO.userError "actual certified endpoint")
  | some (a,s) => return ⟨a,s,evaluateClosedSourceExpression?_sound result,
      (h.image a s).mp (evaluateClosedSourceExpression?_sound result)⟩
private def reject {own ns es st src} (absent : ∀ a s, ¬ E own ns es st src a s) : IO Unit := do
  proof absent
  for budget in [0,1,2,3,8] do
    match result : evaluateClosedSourceExpression? budget own ns es st src with
    | none => pure ()
    | some (a,s) => False.elim (absent a s (evaluateClosedSourceExpression?_sound result))
private def selected (b : Bool) (p : V) (tail : Resolved.LocalScope V) (st : List V)
    (src : Syntax.Expr) : IO (Cert owner (names owner) (rows owner b p tail) st src p) := do
  match shape : src with
  | ⟨_,.binary ⟨ls,.identifier ⟨ln,"flag"⟩⟩ ⟨_,op⟩ ⟨rs,.identifier n⟩⟩ =>
    if admitted : n.value="right" ∨ n.value="saved" then
      have l : E owner (names owner) (rows owner b p tail) st
          ⟨ls,.identifier ⟨ln,"flag"⟩⟩ (.bool b) st := .reference .head .head
      have r : E owner (names owner) (rows owner b p tail) st ⟨rs,.identifier n⟩ p st :=
        .reference (LocalNameTable.lookup?_iff.mp (by rcases admitted with h|h <;> rw [h] <;> rfl))
          (.tail (index_ne owner (by decide)) .head)
      match operator : op, choice : b with
      | .logicalAnd,true =>
        have h : E owner (names owner) (rows owner b p tail) st src p st := by
          rw [shape,operator]; exact .andTrue (by simpa only [choice] using l) r
        return ⟨2,h,by
          intro a s; rw [shape,operator]; constructor
          · intro e; exact (closedSourceExpressionEvaluates_logicalAnd_iff.mpr
              (closedSourceExpressionEvaluates_logicalAnd_iff.mp e)).deterministic (by simpa only [shape,operator] using h)
          · rintro ⟨rfl,rfl⟩; exact closedSourceExpressionEvaluates_logicalAnd_iff.mpr
              (.inr ⟨_,by simpa only [choice] using l,r⟩)⟩
      | .logicalOr,false =>
        have h : E owner (names owner) (rows owner b p tail) st src p st := by
          rw [shape,operator]; exact .orFalse (by simpa only [choice] using l) r
        return ⟨2,h,by
          intro a s; rw [shape,operator]; constructor
          · intro e; exact (closedSourceExpressionEvaluates_logicalOr_iff.mpr
              (closedSourceExpressionEvaluates_logicalOr_iff.mp e)).deterministic (by simpa only [shape,operator] using h)
          · rintro ⟨rfl,rfl⟩; exact closedSourceExpressionEvaluates_logicalOr_iff.mpr
              (.inr ⟨_,by simpa only [choice] using l,r⟩)⟩
      | _,_ => throw (IO.userError "selected guard/operator")
    else throw (IO.userError "selected original name")
  | _ => throw (IO.userError "selected original binary")
private def missing (b : Bool) (p : V) (tail : Resolved.LocalScope V) (st : List V)
    (src : Syntax.Expr) : IO Unit := do
  match shape : src with
  | ⟨_,.binary ⟨ls,.identifier ⟨ln,"flag"⟩⟩ ⟨_,op⟩ ⟨rs,.identifier ⟨rn,"missing"⟩⟩⟩ =>
    have l : E owner (names owner) (rows owner b p tail) st
        ⟨ls,.identifier ⟨ln,"flag"⟩⟩ (.bool b) st := .reference .head .head
    have absent (s a final) : ¬ E owner (names owner) (rows owner b p tail) s
        ⟨rs,.identifier ⟨rn,"missing"⟩⟩ a final := by
      intro e; cases e with
      | creation impossible => cases impossible
      | reference named _ => have h := LocalNameTable.lookup?_iff.mpr named; simp [names,LocalNameTable.lookup?] at h
    proof absent
    match operator : op, choice : b with
    | .logicalAnd,false =>
      let _ ← run (certified 2 (show E owner (names owner) (rows owner b p tail) st src (.bool b) st by
        rw [shape,operator,choice]; exact .andFalse (by simpa only [choice] using l)))
      pure ()
    | .logicalOr,true =>
      let _ ← run (certified 2 (show E owner (names owner) (rows owner b p tail) st src (.bool b) st by
        rw [shape,operator,choice]; exact .orTrue (by simpa only [choice] using l)))
      pure ()
    | .logicalAnd,true => reject (own:=owner) (ns:=names owner) (es:=rows owner b p tail) (st:=st) (src:=src) (by
        intro a final e; rw [shape,operator] at e
        rcases closedSourceExpressionEvaluates_logicalAnd_iff.mp e with ⟨_,bad⟩|⟨s,_,right⟩
        · have clash := (l.deterministic bad).1; simp only [choice] at clash; cases clash
        · exact absent s a final right)
    | .logicalOr,false => reject (own:=owner) (ns:=names owner) (es:=rows owner b p tail) (st:=st) (src:=src) (by
        intro a final e; rw [shape,operator] at e
        rcases closedSourceExpressionEvaluates_logicalOr_iff.mp e with ⟨_,bad⟩|⟨s,_,right⟩
        · have clash := (l.deterministic bad).1; simp only [choice] at clash; cases clash
        · exact absent s a final right)
    | _,_ => throw (IO.userError "missing short-circuit operator")
  | _ => throw (IO.userError "missing original binary")
private structure Factory (src : Syntax.Expr) where
  inner : Syntax.Expr
  parameter : Syntax.Identifier
  body : Syntax.Block
  shape : SourceUnaryLambdaShape inner parameter body
  witness : ∀ own ns es id a st, B own ((parameter.value,id)::ns) ((id,a)::es) st body a st
  creation : ∀ ns es st, E owner ns es st src (.sourceClosure inner owner ns es) st
private def factory (src : Syntax.Expr) : IO (Factory src) := do
  match whole : src with
  | ⟨_,.group inner⟩ => match form : inner with
    | ⟨_,.lambda _ ⟨_,[⟨_,.inferred parameter⟩]⟩ none body⟩ => match returned : body with
      | ⟨_,[⟨_,.returnStmt (some ⟨_,.identifier n⟩)⟩]⟩ =>
        if same : n.value=parameter.value then
          have sh : SourceUnaryLambdaShape inner parameter body := by rw [form]; exact .inferred
          return ⟨inner,parameter,body,sh,by
            intro own ns es id a st; rw [returned]; exact .expression (.reference (by rw [same]; exact .head) .head),by
            intro ns es st; rw [whole]; exact .group (.creation sh)⟩
        else throw (IO.userError "parameter return shadow")
      | _ => throw (IO.userError "original return")
    | _ => throw (IO.userError "original lambda")
  | _ => throw (IO.userError "original grouped creation")
private def savedCall {src} (f : Factory src) (sn : LocalNameTable) (sc : Resolved.LocalScope V)
    (made : V) (same : made=.sourceClosure f.inner owner sn sc) (arg : V)
    (tail : Resolved.LocalScope V) (st : List V) (call : Syntax.Expr) : IO Unit := do
  let ns : LocalNameTable := [("picked",lid caller 0),("p",lid caller 1),("p",lid owner 2)]
  let es := (lid caller 0,made)::(lid caller 1,arg)::tail
  proof (show caller≠owner by decide)
  match form : call with
  | ⟨_,.call ⟨fs,.identifier ⟨fn,"picked"⟩⟩ ⟨_,[⟨argSpan,.identifier ⟨an,"p"⟩⟩]⟩⟩ =>
    let callee : Syntax.Expr := ⟨fs,.identifier ⟨fn,"picked"⟩⟩
    let argument : Syntax.Expr := ⟨argSpan,.identifier ⟨an,"p"⟩⟩
    have fetched (s) : E caller ns es s callee made s := .reference .head .head
    have argumentOld (s) : E caller ns es s argument arg s :=
      .reference (.tail (by change "picked"≠"p"; decide) .head) (.tail (index_ne caller (by decide)) .head)
    have old : E caller ns es st call arg st := by
      rw [form]; exact .call f.shape (by rw [← same]; exact fetched st) (argumentOld st)
        (f.witness owner sn sc (Resolved.freshLocalId owner (sn.map Prod.snd)) arg st)
    proof old
    let fetchedActual ← run (certified 1 (fetched st))
    let argumentActual ← run (certified 1 (argumentOld fetchedActual.store))
    have fullClosure := fetchedActual.endpoint.1.trans same
    match actualShape : fetchedActual.value with
    | .sourceClosure savedSource savedOwner actualNames actualRows =>
      match selectedShape : sourceUnaryLambdaShape? savedSource with
      | none => throw (IO.userError "actual saved source shape")
      | some (parameter,body) =>
        let id := Resolved.freshLocalId savedOwner (actualNames.map Prod.snd)
        let bodyNames := (parameter.value,id)::actualNames
        let bodyRows := (id,argumentActual.value)::actualRows
        have bodyOld : B savedOwner bodyNames bodyRows argumentActual.store body argumentActual.value argumentActual.store := by
          have fields : RuntimeValue.sourceClosure savedSource savedOwner actualNames actualRows=.sourceClosure f.inner owner sn sc :=
            by simpa only [actualShape] using fullClosure
          obtain ⟨rfl,rfl,rfl,rfl⟩ := RuntimeValue.sourceClosure.inj fields
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj
            (selectedShape.symm.trans (sourceUnaryLambdaShape?_iff.mpr f.shape)))
          exact f.witness _ _ _ _ _ _
        have image (v s) : B savedOwner bodyNames bodyRows argumentActual.store body v s ↔
            v=argumentActual.value ∧ s=argumentActual.store :=
          ⟨fun other => other.deterministic bodyOld,by rintro ⟨rfl,rfl⟩; exact bodyOld⟩
        proof bodyOld
        for budget in [0,1,2,5] do
          match result : evaluateClosedSourceBody? budget savedOwner bodyNames bodyRows argumentActual.store body with
          | none => check (budget<2) "actual saved body depth2"
          | some (v,s) =>
            have endpoint := (image v s).mp (evaluateClosedSourceBody?_sound result)
            proof endpoint; proof ((image v s).mpr endpoint); proof ((image argumentActual.value argumentActual.store).mpr ⟨rfl,rfl⟩)
            proof (endpoint.1.trans argumentActual.endpoint.1)
            proof (endpoint.2.trans (argumentActual.endpoint.2.trans fetchedActual.endpoint.2))
            have actualCall : E caller ns es st call v s := by
              rw [form]
              exact .call (sourceUnaryLambdaShape?_iff.mp selectedShape)
                (by simpa only [actualShape] using fetchedActual.evidence)
                argumentActual.evidence (evaluateClosedSourceBody?_sound result)
            proof (actualCall.deterministic old)
            proof ((Tests.ParsedClosedSourceShortCircuitBoundaries.endpoint old v s).mpr (actualCall.deterministic old))
            check (budget≥2) "saved body adjacent depth"
    | _ => throw (IO.userError "actual saved closure")
    let _ ← run (certified 3 old)
    pure ()
  | _ => throw (IO.userError "original saved call")
private def exercise (creation : Syntax.Expr) (f : Factory creation) (b : Bool) (p : V)
    (tail : Resolved.LocalScope V) (st : List V) : IO Unit := do
  let text := if b then "flag && " else "flag || "
  let raw ← parsed (text++"right") (binaryAST b "right")
  let _ ← run (← selected b p tail st raw)
  for op in [false,true] do
    let missingSource ← parsed ((if op then "flag && " else "flag || ")++"missing") (binaryAST op "missing")
    missing b p tail st missingSource
  let sn := names owner
  let sc := rows owner b p tail
  let created ← run (certified 2 (f.creation sn sc st))
  let selectSource ← parsed (text++"saved") (binaryAST b "saved")
  let selectedActual ← run (← selected b created.value tail created.store selectSource)
  proof (selectedActual.endpoint.2.trans created.endpoint.2)
  let call ← parsed "picked(p)" callAST
  savedCall f sn sc selectedActual.value (selectedActual.endpoint.1.trans created.endpoint.1)
    p tail selectedActual.store call
end Tests.ParsedClosedSourceShortCircuitBoundaries
open Tests.ParsedClosedSourceShortCircuitBoundaries in
def Tests.frontendParsedClosedSourceShortCircuitBoundaryTests : IO Unit := do
  let creation ← parsed "(lam(p){return p;})" factoryAST
  let f ← factory creation
  let opaquePayload := Solcore.Frontend.RuntimeValue.ofCore
    (.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700])
  let saved := Solcore.Frontend.RuntimeValue.sourceClosure f.inner caller [("p",lid caller 0)] [(lid caller 0,opaquePayload)]
  for p in [Solcore.Frontend.RuntimeValue.unit,.bool false,.bool true,
      .word Solcore.Core.Word.zero,.word Solcore.Core.Word.maximum,.pair saved opaquePayload,opaquePayload,
      .hostFunction .storageWrite,.cellRef .word 700,saved,.inLeft .word saved,
      .inRight .unit opaquePayload,.constructed ⟨⟨4⟩,7⟩ saved] do
    for b in [false,true] do
      for tail in [[],[(lid owner 0,.bool (!b)),(lid owner 2,saved),(lid caller 1,opaquePayload),(lid caller 1,p)]] do
        for st in [[],[p,saved,opaquePayload,.hostFunction .storageWrite,.cellRef .word 900]] do
          exercise creation f b p tail st
end
