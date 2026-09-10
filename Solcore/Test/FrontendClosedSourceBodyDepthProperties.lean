import Solcore.Frontend.ClosedSourceEvaluatorThresholdProperties

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
