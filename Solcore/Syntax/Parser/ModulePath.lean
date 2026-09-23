import Solcore.Syntax.Parser.Name
import Solcore.Syntax.Module
import Solcore.Syntax.DeclarativeModulePathOutcomeGrammar
import Solcore.Syntax.Parser.CoreTypeQualifiedNameRejectionSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.QualifiedNameSoundnessProperties
import Solcore.Syntax.DeclarativeModulePathExactnessProperties
import Solcore.Syntax.DeclarativeModulePathOutcomeProperties
import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.QualifiedNameTotalityProperties

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Parse a dotted module path with its optional external-package marker. -/
def modulePath (context : ParseContext) : Parser ModulePath := fun state =>
  if isSymbol state .at then
    match symbol .at context state with
    | .ok marker afterMarker =>
        match qualifiedName context .topLevel afterMarker with
        | .ok name next => .ok {
            span := SourceSpan.cover marker.span name.span
            value := {
              externalMarker := some marker.span
              components := name.value.components
            }
          } next
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error
  else
    match qualifiedName context .topLevel state with
    | .ok name next => .ok {
        span := name.span
        value := {
          externalMarker := none
          components := name.value.components
        }
      } next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error

/-- Module-path parsing preserves its cover, marker, and component ranges. -/
theorem modulePath_validFor (context : ParseContext) :
    (modulePath context).ValidFor ModulePath.ValidFor := by
  intro input inputValid
  unfold modulePath
  split
  · cases markerResult : symbol .at context input with
    | invariant error => simp only [Reply.ValidFor]
    | reject failure rejected =>
        have markerValid := symbol_validFor .at context input inputValid
        rw [markerResult] at markerValid
        simpa only [markerResult, Reply.ValidFor] using markerValid
    | ok marker afterMarker =>
        have markerValid := symbol_validFor .at context input inputValid
        rw [markerResult] at markerValid
        have markerShape := symbol_ok_state_shape .at context markerResult
        simp only
        cases nameResult : qualifiedName context .topLevel afterMarker with
        | invariant error => simp only [Reply.ValidFor]
        | reject failure rejected =>
            have nameValid := qualifiedName_validFor context .topLevel
              afterMarker markerValid.2.1
            rw [nameResult] at nameValid
            simpa only [nameResult, Reply.ValidFor] using
              nameValid.of_file_eq markerValid.2.2
        | ok name next =>
            have nameValid := qualifiedName_validFor context .topLevel
              afterMarker markerValid.2.1
            rw [nameResult] at nameValid
            have nameValidInput : QualifiedName.ValidFor input.file name := by
              simpa [markerValid.2.2] using nameValid.1
            have markerSpanValid : marker.span.ValidFor input.file := by
              simpa only [Located.ValidFor] using markerValid.1
            rcases qualifiedName_ok_state_shape context .topLevel nameResult with
              ⟨firstToken, firstFound, firstStart, _nameTokens⟩
            have markerFound :=
              State.getElem?_eq_some_of_peek?_eq_some markerShape.1
            have firstFoundInput :
                input.tokens[input.cursor + 1]? = some firstToken := by
              have foundAfterMarker :=
                State.getElem?_eq_some_of_peek?_eq_some firstFound
              simpa [markerShape.2] using foundAfterMarker
            have markerBeforeFirst :
                marker.span.endByte ≤ firstToken.span.startByte := by
              exact inputValid.token_end_le_token_start_of_getElem?_lt
                markerFound firstFoundInput (by simp)
            have markerBeforeNameEnd :
                marker.span.startByte ≤ name.span.endByte := by
              apply Nat.le_trans markerSpanValid.2.1
              apply Nat.le_trans markerBeforeFirst
              rw [firstStart]
              exact nameValidInput.1.2.1
            have coverValid :
                (SourceSpan.cover marker.span name.span).ValidFor input.file :=
              SourceSpan.cover_validFor markerSpanValid nameValidInput.1
                markerBeforeNameEnd
            simp only [Reply.ValidFor, ModulePath.ValidFor]
            exact ⟨⟨coverValid, markerSpanValid, nameValidInput.2⟩,
              nameValid.2.1, nameValid.2.2.trans markerValid.2.2⟩
  · cases nameResult : qualifiedName context .topLevel input with
    | invariant error => simp only [Reply.ValidFor]
    | reject failure rejected =>
        have nameValid := qualifiedName_validFor context .topLevel
          input inputValid
        rw [nameResult] at nameValid
        simpa only [nameResult, Reply.ValidFor] using nameValid
    | ok name next =>
        have nameValid := qualifiedName_validFor context .topLevel
          input inputValid
        rw [nameResult] at nameValid
        simp only [Reply.ValidFor, ModulePath.ValidFor]
        exact ⟨⟨nameValid.1.1, trivial, nameValid.1.2⟩,
          nameValid.2.1, nameValid.2.2⟩

/-- Module paths preserve tokens and the active window on every reply. -/
theorem modulePath_preservesTokenWindow (context : ParseContext) :
    Parser.PreservesTokenWindow (modulePath context) := by
  intro input
  unfold modulePath
  split
  · have markerShape := symbol_preservesTokenWindow .at context input
    cases markerResult : symbol .at context input with
    | invariant error => trivial
    | reject failure rejected =>
        rw [markerResult] at markerShape
        exact markerShape
    | ok marker afterMarker =>
        rw [markerResult] at markerShape
        simp only
        have nameShape := qualifiedName_preservesTokenWindow context
          .topLevel afterMarker
        cases nameResult : qualifiedName context .topLevel afterMarker with
        | invariant error => trivial
        | reject failure rejected =>
            rw [nameResult] at nameShape
            exact nameShape.trans markerShape
        | ok name next =>
            rw [nameResult] at nameShape
            exact nameShape.trans markerShape
  · have nameShape := qualifiedName_preservesTokenWindow context
      .topLevel input
    cases nameResult : qualifiedName context .topLevel input with
    | invariant error => trivial
    | reject failure rejected =>
        rw [nameResult] at nameShape
        exact nameShape
    | ok name next =>
        rw [nameResult] at nameShape
        exact nameShape

/-- Module-path success preserves the immutable token carrier. -/
theorem modulePath_preservesTokensOnSuccess (context : ParseContext) :
    Parser.PreservesTokensOnSuccess (modulePath context) := by
  intro input path next result
  unfold modulePath at result
  split at result
  · cases markerResult : symbol .at context input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok marker afterMarker =>
        simp only [markerResult] at result
        cases nameResult : qualifiedName context .topLevel afterMarker with
        | invariant error => simp [nameResult] at result
        | reject failure rejected => simp [nameResult] at result
        | ok name final =>
            simp only [nameResult] at result
            cases result
            have nameTokens := qualifiedName_preservesTokensOnSuccess
              context .topLevel afterMarker name next nameResult
            have markerShape := symbol_ok_state_shape .at context markerResult
            calc
              next.tokens = afterMarker.tokens := nameTokens
              _ = input.tokens := by rw [markerShape.2]
  · cases nameResult : qualifiedName context .topLevel input with
    | invariant error => simp [nameResult] at result
    | reject failure rejected => simp [nameResult] at result
    | ok name final =>
        simp only [nameResult] at result
        cases result
        exact qualifiedName_preservesTokensOnSuccess context .topLevel
          input name next nameResult

/-- A module path starts at its package marker or first name component. -/
theorem modulePath_startsAtCurrentTokenOnSuccess (context : ParseContext) :
    Parser.StartsAtCurrentTokenOnSuccess (modulePath context) (·.span) := by
  intro input path next result
  unfold modulePath at result
  split at result
  · cases markerResult : symbol .at context input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok marker afterMarker =>
        simp only [markerResult] at result
        cases nameResult : qualifiedName context .topLevel afterMarker with
        | invariant error => simp [nameResult] at result
        | reject failure rejected => simp [nameResult] at result
        | ok name final =>
            simp only [nameResult] at result
            cases result
            exact ⟨marker,
              (symbol_ok_state_shape .at context markerResult).1, rfl⟩
  · cases nameResult : qualifiedName context .topLevel input with
    | invariant error => simp [nameResult] at result
    | reject failure rejected => simp [nameResult] at result
    | ok name final =>
        simp only [nameResult] at result
        cases result
        exact qualifiedName_startsAtCurrentTokenOnSuccess context .topLevel
          input name next nameResult

/-- Every successful module path consumes at least its first path token. -/
theorem modulePath_cursor_lt_onSuccess (context : ParseContext)
    {input next : State} {path : ModulePath}
    (result : modulePath context input = .ok path next) :
    input.cursor < next.cursor := by
  unfold modulePath at result
  split at result
  · cases markerResult : symbol .at context input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok marker afterMarker =>
        simp only [markerResult] at result
        cases nameResult : qualifiedName context .topLevel afterMarker with
        | invariant error => simp [nameResult] at result
        | reject failure rejected => simp [nameResult] at result
        | ok name final =>
            simp only [nameResult] at result
            cases result
            have markerProgress : input.cursor < afterMarker.cursor := by
              rw [(symbol_ok_state_shape .at context markerResult).2]
              simp
            exact Nat.lt_trans markerProgress
              (qualifiedName_cursor_lt_onSuccess context .topLevel nameResult)
  · cases nameResult : qualifiedName context .topLevel input with
    | invariant error => simp [nameResult] at result
    | reject failure rejected => simp [nameResult] at result
    | ok name final =>
        simp only [nameResult] at result
        cases result
        exact qualifiedName_cursor_lt_onSuccess context .topLevel nameResult

/-- Successful module-path parsing never rewinds the cursor. -/
theorem modulePath_cursorMonotoneOnSuccess (context : ParseContext) :
    Parser.CursorMonotoneOnSuccess (modulePath context) := by
  intro input path next result
  exact Nat.le_of_lt (modulePath_cursor_lt_onSuccess context result)

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.ModulePathOrdinaryRejectionSoundnessProperties`
-/

/-! Exact executable rejection reflection for module paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable module-path rejection comes from the qualified name in
the prioritized local or exact-marker external-package branch. -/
theorem modulePath_reject_ordinaryOutcome_sound (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : modulePath context input = .reject failure rejected) :
    DeclarativeGrammar.ModulePathRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold modulePath at result
  by_cases markerPresent : isSymbol input .at = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .at context markerPresent with
      ⟨marker, markerResult⟩
    simp only [markerPresent, if_true, markerResult] at result
    cases nameResult : qualifiedName context .topLevel
        { input with cursor := input.cursor + 1 } with
    | invariant error => simp [nameResult] at result
    | ok name output => simp [nameResult] at result
    | reject nameFailure nameRejected =>
        simp only [nameResult] at result
        cases result
        exact .externalRejected marker.span
          (symbol_success_exactTokenParses .at context markerResult)
          (qualifiedName_reject_type_sound context .topLevel nameResult)
  · have markerAbsent : isSymbol input .at = false :=
      Bool.eq_false_iff.mpr markerPresent
    simp only [markerAbsent, Bool.false_eq_true, if_false] at result
    cases nameResult : qualifiedName context .topLevel input with
    | invariant error => simp [nameResult] at result
    | ok name output => simp [nameResult] at result
    | reject nameFailure nameRejected =>
        simp only [nameResult] at result
        cases result
        exact .localRejected
          (symbolAbsentAt_of_isSymbol_eq_false .at markerAbsent)
          (qualifiedName_reject_type_sound context .topLevel nameResult)

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.ModulePathSoundnessProperties`
-/

/-! Success soundness of canonical module-path parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful module-path parse follows the independent token grammar. -/
theorem modulePath_success_sound (context : ParseContext)
    {input next : State} {path : ModulePath}
    (result : modulePath context input = .ok path next) :
    DeclarativeGrammar.ModulePathParses input.declarativeRemainder path
      next.declarativeRemainder := by
  unfold modulePath at result
  split at result
  · cases markerResult : symbol .at context input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok marker afterMarker =>
        have markerSound := symbol_ok_tokenAt .at context markerResult
        simp only [markerResult] at result
        cases nameResult : qualifiedName context .topLevel afterMarker with
        | invariant error => simp [nameResult] at result
        | reject failure rejected => simp [nameResult] at result
        | ok name final =>
            have nameSound := qualifiedName_success_sound context .topLevel
              nameResult
            simp only [nameResult] at result
            cases result
            apply DeclarativeGrammar.ModulePathParses.externalPackage
              marker.span markerSound.1
            simpa only [markerSound.2, State.declarativeRemainder,
              State.tokens, State.window, State.cursor] using nameSound
  · cases nameResult : qualifiedName context .topLevel input with
    | invariant error => simp [nameResult] at result
    | reject failure rejected => simp [nameResult] at result
    | ok name final =>
        have nameSound := qualifiedName_success_sound context .topLevel
          nameResult
        simp only [nameResult] at result
        cases result
        exact DeclarativeGrammar.ModulePathParses.local nameSound

/-- Success soundness composes with the established source-provenance contract. -/
theorem modulePath_success_sound_and_validFor (context : ParseContext)
    {input next : State} {path : ModulePath} (inputValid : input.ValidFor)
    (result : modulePath context input = .ok path next) :
    DeclarativeGrammar.ModulePathParses input.declarativeRemainder path
        next.declarativeRemainder ∧
      path.ValidFor input.file := by
  refine ⟨modulePath_success_sound context result, ?_⟩
  have valid := modulePath_validFor context input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.ModulePathOrdinarySuccessSoundnessProperties`
-/

/-! Broad ordinary-success soundness for module paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable module-path success follows the existing exact ordinary
grammar without a diagnostic-free premise. -/
theorem modulePath_success_ordinaryOutcome_sound (context : ParseContext)
    {input output : State} {path : ModulePath}
    (result : modulePath context input = .ok path output) :
    DeclarativeGrammar.ModulePathOrdinaryParses input.declarativeRemainder
      path output.declarativeRemainder :=
  modulePath_success_sound context result

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.ModulePathOrdinaryOutcomeSoundnessProperties`
-/

/-! Complete executable broad ordinary outcomes for module paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package module-path success and exact prioritized rejection. -/
theorem modulePath_ordinaryOutcome_sound (context : ParseContext) :
    (∀ {input output : State} {path : ModulePath},
      modulePath context input = .ok path output →
        DeclarativeGrammar.ModulePathOrdinaryParses
          input.declarativeRemainder path output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      modulePath context input = .reject failure rejected →
        DeclarativeGrammar.ModulePathRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨modulePath_success_ordinaryOutcome_sound context,
    modulePath_reject_ordinaryOutcome_sound context⟩

/-- Re-export deterministic and exclusive module-path outcomes. -/
theorem modulePath_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ModulePathOrdinaryParses
      DeclarativeGrammar.ModulePathRejects :=
  DeclarativeGrammar.modulePathDeterministicOutcomeSpec


/-- Exact values and endpoints for the independent modulePath grammar. -/
theorem modulePath_exactOutcomeSpec  :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ModulePathOrdinaryParses DeclarativeGrammar.ModulePathRejects :=
  DeclarativeGrammar.modulePathExactOutcomeSpec

/-- Executable successes agree on their complete value and remainder. -/
theorem modulePath_success_result_unique (context : ParseContext)
    {input leftOutput rightOutput : State} {left right : ModulePath}
    (leftResult : modulePath context input = .ok left leftOutput)
    (rightResult : modulePath context input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (modulePath_exactOutcomeSpec ).successResultUnique
    (modulePath_success_ordinaryOutcome_sound context leftResult)
    (modulePath_success_ordinaryOutcome_sound context rightResult)

/-- Executable rejections agree on their complete declarative endpoint. -/
theorem modulePath_reject_output_unique (context : ParseContext)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : modulePath context input = .reject leftFailure leftOutput)
    (rightResult : modulePath context input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (modulePath_exactOutcomeSpec ).rejectOutputUnique
    (modulePath_reject_ordinaryOutcome_sound context leftResult)
    (modulePath_reject_ordinaryOutcome_sound context rightResult)

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.ModulePathTotalityProperties`
-/

/-! Totality laws for module-path parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Module paths always produce an ordinary success or rejection reply. -/
theorem modulePath_ordinary (context : ParseContext) :
    Parser.Ordinary (modulePath context) := by
  intro input
  unfold modulePath
  split
  · cases markerResult : symbol .at context input with
    | invariant error =>
        exact False.elim
          (symbol_ne_invariant .at context input error markerResult)
    | reject failure rejected =>
        exact Or.inr ⟨failure, rejected, rfl⟩
    | ok marker afterMarker =>
        dsimp only
        cases nameResult : qualifiedName context .topLevel afterMarker with
        | invariant error =>
            exact False.elim
              (qualifiedName_ne_invariant context .topLevel afterMarker error
                nameResult)
        | reject failure rejected =>
            exact Or.inr ⟨failure, rejected, rfl⟩
        | ok name next =>
            exact Or.inl ⟨_, next, rfl⟩
  · cases nameResult : qualifiedName context .topLevel input with
    | invariant error =>
        exact False.elim
          (qualifiedName_ne_invariant context .topLevel input error nameResult)
    | reject failure rejected =>
        exact Or.inr ⟨failure, rejected, rfl⟩
    | ok name next =>
        exact Or.inl ⟨_, next, rfl⟩

/-- Module paths cannot expose an internal parser invariant. -/
theorem modulePath_ne_invariant (context : ParseContext) (input : State)
    (error : ParserInvariantError) :
    modulePath context input ≠ .invariant error :=
  (modulePath_ordinary context).ne_invariant input error

/-- Module paths are invariant-free on the canonical valid-input domain. -/
theorem modulePath_invariantFreeOnValid (context : ParseContext) :
    Parser.InvariantFreeOnValid (modulePath context) :=
  (modulePath_ordinary context).invariantFreeOnValid

/-- Module paths satisfy the generic strict element-parser contract. -/
theorem modulePath_elementTotalityContract (context : ParseContext) :
    ElementTotalityContract (modulePath context) := {
  validFor := (modulePath_validFor context).mono (fun _ _ _ => trivial)
  preservesTokenWindow := modulePath_preservesTokenWindow context
  cursorLtOnSuccess := modulePath_cursor_lt_onSuccess context
  invariantFree := fun input _ error =>
    modulePath_ne_invariant context input error
}

end Solcore.Syntax.Parser
