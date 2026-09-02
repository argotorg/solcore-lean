import Solcore.Syntax.DeclarativeLexedValidationOutcomeGrammar

/-! Totality, functionality, and acceptance laws for lexical validation. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- An ordered-span validation scan has at most one result. -/
theorem OrderedSpanValidationScans.result_unique
    {α : Type} {file : SourceFile} {spanOf : α → SourceSpan}
    {index previousEnd : Nat} {items : List α}
    {left right : Option IndexedSpan}
    (leftScan : OrderedSpanValidationScans file spanOf index previousEnd
      items left)
    (rightScan : OrderedSpanValidationScans file spanOf index previousEnd
      items right) :
    left = right := by
  induction leftScan generalizing right with
  | done =>
      cases rightScan
      rfl
  | rejected leftInvalid =>
      cases rightScan with
      | rejected => rfl
      | continues rightAccepted => contradiction
  | continues leftAccepted leftTail inductionHypothesis =>
      cases rightScan with
      | rejected rightInvalid => contradiction
      | continues _ rightTail =>
          exact inductionHypothesis rightTail

/-- Every finite ordered-span sequence has a validation result. -/
theorem OrderedSpanValidationScans.exists_result
    {α : Type} (file : SourceFile) (spanOf : α → SourceSpan) :
    ∀ (index previousEnd : Nat) (items : List α),
      ∃ result, OrderedSpanValidationScans file spanOf index previousEnd
        items result := by
  intro index previousEnd items
  induction items generalizing index previousEnd with
  | nil => exact ⟨none, .done⟩
  | cons item rest inductionHypothesis =>
      by_cases accepted : OrderedSpanAccepted file previousEnd (spanOf item)
      · rcases inductionHypothesis (index + 1) (spanOf item).endByte with
          ⟨result, tail⟩
        exact ⟨result, .continues accepted tail⟩
      · exact ⟨some { index := index, span := spanOf item },
          .rejected accepted⟩

/-- A clear ordered-span scan is exactly a valid source span sequence. -/
theorem OrderedSpanValidationScans.none_iff_spanSequenceValidFor
    {α : Type} {file : SourceFile} {spanOf : α → SourceSpan}
    {index previousEnd : Nat} {items : List α} :
    OrderedSpanValidationScans file spanOf index previousEnd items none ↔
      SpanSequence.ValidFor file spanOf previousEnd items := by
  constructor
  · intro scan
    induction items generalizing index previousEnd with
    | nil => trivial
    | cons item rest inductionHypothesis =>
        cases scan with
        | continues accepted tail =>
            exact ⟨accepted.1, accepted.2.1, accepted.2.2,
              inductionHypothesis tail⟩
  · intro valid
    induction items generalizing index previousEnd with
    | nil => exact .done
    | cons item rest inductionHypothesis =>
        simp only [SpanSequence.ValidFor] at valid
        rcases valid with
          ⟨spanValid, afterPrevious, nonempty, tailValid⟩
        exact .continues
          ⟨spanValid, afterPrevious, nonempty⟩
          (inductionHypothesis tailValid)

/-- A pointwise span-validation scan has at most one result. -/
theorem SpanValidationScans.result_unique
    {α : Type} {file : SourceFile} {spanOf : α → SourceSpan}
    {index : Nat} {items : List α} {left right : Option IndexedSpan}
    (leftScan : SpanValidationScans file spanOf index items left)
    (rightScan : SpanValidationScans file spanOf index items right) :
    left = right := by
  induction leftScan generalizing right with
  | done =>
      cases rightScan
      rfl
  | rejected leftInvalid =>
      cases rightScan with
      | rejected => rfl
      | continues rightAccepted => contradiction
  | continues leftAccepted leftTail inductionHypothesis =>
      cases rightScan with
      | rejected rightInvalid => contradiction
      | continues _ rightTail =>
          exact inductionHypothesis rightTail

/-- Every finite pointwise span sequence has a validation result. -/
theorem SpanValidationScans.exists_result
    {α : Type} (file : SourceFile) (spanOf : α → SourceSpan) :
    ∀ (index : Nat) (items : List α),
      ∃ result, SpanValidationScans file spanOf index items result := by
  intro index items
  induction items generalizing index with
  | nil => exact ⟨none, .done⟩
  | cons item rest inductionHypothesis =>
      by_cases accepted : (spanOf item).ValidFor file
      · rcases inductionHypothesis (index + 1) with ⟨result, tail⟩
        exact ⟨result, .continues accepted tail⟩
      · exact ⟨some { index := index, span := spanOf item },
          .rejected accepted⟩

/-- A clear pointwise span scan accepts exactly every list member. -/
theorem SpanValidationScans.none_iff_forall_validFor
    {α : Type} {file : SourceFile} {spanOf : α → SourceSpan}
    {index : Nat} {items : List α} :
    SpanValidationScans file spanOf index items none ↔
      ∀ item ∈ items, (spanOf item).ValidFor file := by
  constructor
  · intro scan
    induction items generalizing index with
    | nil => simp
    | cons head tail inductionHypothesis =>
        cases scan with
        | continues accepted tailScan =>
            intro item member
            rcases List.mem_cons.mp member with rfl | member
            · exact accepted
            · exact inductionHypothesis tailScan item member
  · intro valid
    induction items generalizing index with
    | nil => exact .done
    | cons item rest inductionHypothesis =>
        apply SpanValidationScans.continues (valid item (by simp))
        apply inductionHypothesis
        intro tailItem member
        exact valid tailItem (List.mem_cons_of_mem item member)

/-- Whole-file validation has at least one priority-ordered outcome. -/
theorem LexedFileValidationOutcome.exists_result
    (file : SourceFile) (lexed : LexedFile) :
    ∃ result, LexedFileValidationOutcome file lexed result := by
  by_cases mismatch : lexed.source ≠ file.id
  · exact ⟨_, .sourceRejected mismatch⟩
  · have sourceAccepted : lexed.source = file.id :=
      Decidable.of_not_not mismatch
    rcases OrderedSpanValidationScans.exists_result file
        (fun token : Token => token.span) 0 0 lexed.tokens with
      ⟨tokenResult, tokens⟩
    cases tokenResult with
    | some invalid => exact ⟨_, .tokenRejected sourceAccepted tokens⟩
    | none =>
        rcases OrderedSpanValidationScans.exists_result file
            (fun comment : Comment => comment.span) 0 0 lexed.comments with
          ⟨commentResult, comments⟩
        cases commentResult with
        | some invalid =>
            exact ⟨_, .commentRejected sourceAccepted tokens comments⟩
        | none =>
            rcases SpanValidationScans.exists_result file
                (fun diagnostic : LexicalDiagnostic => diagnostic.span)
                0 lexed.diagnostics with
              ⟨diagnosticResult, diagnostics⟩
            cases diagnosticResult with
            | some invalid =>
                exact ⟨_, .diagnosticRejected sourceAccepted tokens comments
                  diagnostics⟩
            | none =>
                exact ⟨none, .accepted sourceAccepted tokens comments
                  diagnostics⟩

/-- Whole-file validation has at most one priority-ordered result. -/
theorem LexedFileValidationOutcome.result_unique
    {file : SourceFile} {lexed : LexedFile}
    {left right : Option LexedValidationFailure}
    (leftOutcome : LexedFileValidationOutcome file lexed left)
    (rightOutcome : LexedFileValidationOutcome file lexed right) :
    left = right := by
  cases leftOutcome with
  | sourceRejected leftMismatch =>
      cases rightOutcome with
      | sourceRejected => rfl
      | tokenRejected rightSource => exact (leftMismatch rightSource).elim
      | commentRejected rightSource => exact (leftMismatch rightSource).elim
      | diagnosticRejected rightSource => exact (leftMismatch rightSource).elim
      | accepted rightSource => exact (leftMismatch rightSource).elim
  | tokenRejected leftSource leftTokens =>
      cases rightOutcome with
      | sourceRejected rightMismatch => exact (rightMismatch leftSource).elim
      | tokenRejected _ rightTokens =>
          cases leftTokens.result_unique rightTokens
          rfl
      | commentRejected _ rightTokens =>
          have impossible := leftTokens.result_unique rightTokens
          contradiction
      | diagnosticRejected _ rightTokens =>
          have impossible := leftTokens.result_unique rightTokens
          contradiction
      | accepted _ rightTokens =>
          have impossible := leftTokens.result_unique rightTokens
          contradiction
  | commentRejected leftSource leftTokens leftComments =>
      cases rightOutcome with
      | sourceRejected rightMismatch => exact (rightMismatch leftSource).elim
      | tokenRejected _ rightTokens =>
          have impossible := leftTokens.result_unique rightTokens
          contradiction
      | commentRejected _ _ rightComments =>
          cases leftComments.result_unique rightComments
          rfl
      | diagnosticRejected _ _ rightComments =>
          have impossible := leftComments.result_unique rightComments
          contradiction
      | accepted _ _ rightComments =>
          have impossible := leftComments.result_unique rightComments
          contradiction
  | diagnosticRejected leftSource leftTokens leftComments leftDiagnostics =>
      cases rightOutcome with
      | sourceRejected rightMismatch => exact (rightMismatch leftSource).elim
      | tokenRejected _ rightTokens =>
          have impossible := leftTokens.result_unique rightTokens
          contradiction
      | commentRejected _ _ rightComments =>
          have impossible := leftComments.result_unique rightComments
          contradiction
      | diagnosticRejected _ _ _ rightDiagnostics =>
          cases leftDiagnostics.result_unique rightDiagnostics
          rfl
      | accepted _ _ _ rightDiagnostics =>
          have impossible := leftDiagnostics.result_unique rightDiagnostics
          contradiction
  | accepted leftSource leftTokens leftComments leftDiagnostics =>
      cases rightOutcome with
      | sourceRejected rightMismatch => exact (rightMismatch leftSource).elim
      | tokenRejected _ rightTokens =>
          have impossible := leftTokens.result_unique rightTokens
          contradiction
      | commentRejected _ _ rightComments =>
          have impossible := leftComments.result_unique rightComments
          contradiction
      | diagnosticRejected _ _ _ rightDiagnostics =>
          have impossible := leftDiagnostics.result_unique rightDiagnostics
          contradiction
      | accepted => rfl

/-- Whole-file validation either accepts or returns one exact failure. -/
theorem lexedFileValidationOutcome_total
    (file : SourceFile) (lexed : LexedFile) :
    LexedFileValidationAccepts file lexed ∨
      ∃ failure, LexedFileValidationRejects file lexed failure := by
  rcases LexedFileValidationOutcome.exists_result file lexed with
    ⟨result, outcome⟩
  cases result with
  | none => exact Or.inl outcome
  | some failure => exact Or.inr ⟨failure, outcome⟩

/-- An exact validation failure excludes acceptance. -/
theorem LexedFileValidationRejects.disjointAccepts
    {file : SourceFile} {lexed : LexedFile}
    {failure : LexedValidationFailure}
    (rejects : LexedFileValidationRejects file lexed failure) :
    ¬ LexedFileValidationAccepts file lexed := by
  intro accepts
  have impossible := rejects.result_unique accepts
  contradiction

/-- The exact first whole-file validation failure is unique. -/
theorem LexedFileValidationRejects.failure_unique
    {file : SourceFile} {lexed : LexedFile}
    {left right : LexedValidationFailure}
    (leftRejects : LexedFileValidationRejects file lexed left)
    (rightRejects : LexedFileValidationRejects file lexed right) :
    left = right := by
  exact Option.some.inj (leftRejects.result_unique rightRejects)

/-- Whole-file validation accepts exactly the lexical provenance contract. -/
theorem lexedFileValidationAccepts_iff_validFor
    (file : SourceFile) (lexed : LexedFile) :
    LexedFileValidationAccepts file lexed ↔ lexed.ValidFor file := by
  constructor
  · intro accepted
    cases accepted with
    | accepted source tokens comments diagnostics =>
        exact {
          source_eq := source
          tokens :=
            OrderedSpanValidationScans.none_iff_spanSequenceValidFor.mp tokens
          comments :=
            OrderedSpanValidationScans.none_iff_spanSequenceValidFor.mp comments
          diagnostics :=
            SpanValidationScans.none_iff_forall_validFor.mp diagnostics
        }
  · intro valid
    exact .accepted valid.source_eq
      (OrderedSpanValidationScans.none_iff_spanSequenceValidFor.mpr valid.tokens)
      (OrderedSpanValidationScans.none_iff_spanSequenceValidFor.mpr
        valid.comments)
      (SpanValidationScans.none_iff_forall_validFor.mpr valid.diagnostics)

end Solcore.Syntax.DeclarativeGrammar
