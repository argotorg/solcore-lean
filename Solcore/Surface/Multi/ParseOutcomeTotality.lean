import Solcore.Surface.Multi.DiagnosticExhaustiveness
import Solcore.Surface.Multi.PostLogicalEofClosure
import Solcore.Surface.Multi.RootlessNormalizationGrammarRank

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

/-- The two grammar-specific facts needed to normalize every item at one
greatest cursor: enabled prediction coverage and one common decreasing rank. -/
def RootlessExecutableProgress
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) : Prop :=
  ∀ cursor,
    GreatestReachableCursor file tokens memo correct final cursor →
      (¬ ContextualReach file tokens memo correct final
        (CanonicalCompleteRootItem tokens .module
          (Boundary.start tokens) (Boundary.afterLogicalEOF tokens)
          .plain)) →
        cursor.val ≤ tokens.length ∧
          (∀ waiting,
            FrontierReach file tokens memo correct final cursor waiting →
              EnabledNonterminalCoverageAt
                file tokens memo correct final waiting) ∧
          RankedFrontierNormalization
            file tokens memo correct final cursor

/-- Coverage, ranked normalization, and post-EOF closure jointly supply the
exact rootless progress interface consumed by the executable outcome. -/
theorem rootlessExecutableProgress_of_components
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (coverage : ∀ cursor,
      GreatestReachableCursor file tokens memo correct final cursor →
        ∀ waiting,
          FrontierReach file tokens memo correct final cursor waiting →
            EnabledNonterminalCoverageAt
              file tokens memo correct final waiting)
    (ranked : ∀ cursor,
      GreatestReachableCursor file tokens memo correct final cursor →
        RankedFrontierNormalization
          file tokens memo correct final cursor)
    (postEof : PostLogicalEofTerminalWaitForcesRoot
      file tokens memo correct final) :
    RootlessExecutableProgress file tokens memo correct final := by
  intro cursor greatest rootAbsent
  have waiting := terminalFrontierWait_of_rootless_rankedNormalization
    greatest (coverage cursor greatest) (ranked cursor greatest) rootAbsent
  exact ⟨
    greatestCursor_le_logicalEOF_of_rootless_terminalWait
      postEof greatest waiting rootAbsent,
    coverage cursor greatest,
    ranked cursor greatest⟩

/-- Static anchor coverage and the two finite grammar-rank tables discharge
the abstract coverage and normalization components of rootless progress. -/
theorem rootlessExecutableProgress_of_grammarComponents
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (anchored : ∀ cursor,
      GreatestReachableCursor file tokens memo correct final cursor →
        ∀ waiting,
          FrontierReach file tokens memo correct final cursor waiting →
            AnchoredNonterminalCoverageAt tokens waiting)
    (ranked : ∀ cursor,
      GreatestReachableCursor file tokens memo correct final cursor →
        GrammarRankedFrontierNormalization
          file tokens owned memo correct final cursor)
    (postEof : PostLogicalEofTerminalWaitForcesRoot
      file tokens memo correct final) :
    RootlessExecutableProgress file tokens memo correct final := by
  apply rootlessExecutableProgress_of_components
      (fun cursor greatest waiting frontier =>
        enabledNonterminalCoverageAt_of_anchored correct final waiting
          (anchored cursor greatest waiting frontier))
      (fun cursor greatest =>
        rankedFrontierNormalization_of_grammarRanked owned
          (ranked cursor greatest))
      postEof

/-- Greatest-cursor functionality lets callers certify coverage and ranking at
one selected maximum instead of quantifying over extensionally equal maxima. -/
theorem rootlessExecutableProgress_of_componentsAt
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {cursor : Boundary tokens}
    (greatest : GreatestReachableCursor
      file tokens memo correct final cursor)
    (coverage : ∀ waiting,
      FrontierReach file tokens memo correct final cursor waiting →
        EnabledNonterminalCoverageAt
          file tokens memo correct final waiting)
    (ranked : RankedFrontierNormalization
      file tokens memo correct final cursor)
    (postEof : PostLogicalEofTerminalWaitForcesRoot
      file tokens memo correct final) :
    RootlessExecutableProgress file tokens memo correct final := by
  apply rootlessExecutableProgress_of_components
  · intro other otherGreatest waiting frontier
    have same := GreatestReachableCursor.functional otherGreatest greatest
    subst other
    exact coverage waiting frontier
  · intro other otherGreatest
    have same := GreatestReachableCursor.functional otherGreatest greatest
    subst other
    exact ranked
  · exact postEof

/-- One greatest cursor with anchored coverage and accepted grammar-rank tables
is a complete finite normalization certificate, modulo post-EOF closure. -/
theorem rootlessExecutableProgress_of_grammarComponentsAt
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {cursor : Boundary tokens}
    (greatest : GreatestReachableCursor
      file tokens memo correct final cursor)
    (anchored : ∀ waiting,
      FrontierReach file tokens memo correct final cursor waiting →
        AnchoredNonterminalCoverageAt tokens waiting)
    (ranked : GrammarRankedFrontierNormalization
      file tokens owned memo correct final cursor)
    (postEof : PostLogicalEofTerminalWaitForcesRoot
      file tokens memo correct final) :
    RootlessExecutableProgress file tokens memo correct final := by
  exact rootlessExecutableProgress_of_componentsAt greatest
    (fun waiting frontier =>
      enabledNonterminalCoverageAt_of_anchored correct final waiting
        (anchored waiting frontier))
    (rankedFrontierNormalization_of_grammarRanked owned ranked)
    postEof

/-- A concrete grammar/span potential is accepted by computation: the two
displayed Boolean equalities are the complete normalization-rank certificate. -/
theorem rootlessExecutableProgress_of_checkedGrammarPotentialAt
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {cursor : Boundary tokens}
    (greatest : GreatestReachableCursor
      file tokens memo correct final cursor)
    (anchored : ∀ waiting,
      FrontierReach file tokens memo correct final cursor waiting →
        AnchoredNonterminalCoverageAt tokens waiting)
    (potential : FrontierGrammarPotential tokens)
    (completion : frontierCompletionRankTable
      owned correct final cursor potential = true)
    (prediction : frontierPredictionRankTable
      owned correct final cursor potential = true)
    (postEof : PostLogicalEofTerminalWaitForcesRoot
      file tokens memo correct final) :
    RootlessExecutableProgress file tokens memo correct final := by
  exact rootlessExecutableProgress_of_grammarComponentsAt
    owned greatest anchored ⟨potential, completion, prediction⟩ postEof

/-- All frontier normalization inputs can be supplied as three executable
Boolean checks: enabled coverage, completion rank, and prediction rank. -/
theorem rootlessExecutableProgress_of_checkedFrontierTablesAt
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {cursor : Boundary tokens}
    (greatest : GreatestReachableCursor
      file tokens memo correct final cursor)
    (coverage : frontierCoverageTable
      owned correct final cursor = true)
    (potential : FrontierGrammarPotential tokens)
    (completion : frontierCompletionRankTable
      owned correct final cursor potential = true)
    (prediction : frontierPredictionRankTable
      owned correct final cursor potential = true)
    (postEof : PostLogicalEofTerminalWaitForcesRoot
      file tokens memo correct final) :
    RootlessExecutableProgress file tokens memo correct final := by
  exact rootlessExecutableProgress_of_componentsAt greatest
    (fun waiting frontier =>
      enabledNonterminalCoverageAt_of_frontierCoverageTable
        owned correct final cursor coverage waiting frontier)
    (rankedFrontierNormalization_of_grammarRanked owned
      ⟨potential, completion, prediction⟩)
    postEof

/-- Once grammar-specific frontier progress is supplied, semantic execution
always selects either a module, a G10 diagnostic, or an ordinary diagnostic. -/
theorem executeObservedContextualValueWorklistMulti?_parseOutcome?_isSome_of_progress
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualValueWorklistResult file tokens)
    (selected : Chart.executeObservedContextualValueWorklistMulti?
      file tokens owned = some result)
    (progress :
      let recognitionSelected :=
        Chart.executeObservedContextualValueWorklistMulti?_recognition
          file tokens owned result selected
      let correct := executeObservedContextualWorklistMulti?_phaseBCorrect
        file tokens owned result.recognition recognitionSelected
      let final :=
        Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
          file tokens owned result.recognition recognitionSelected
      RootlessExecutableProgress
        file tokens result.recognition.memo correct final) :
    (result.parseOutcome? file).isSome = true := by
  let recognitionSelected :=
    Chart.executeObservedContextualValueWorklistMulti?_recognition
      file tokens owned result selected
  let correct := executeObservedContextualWorklistMulti?_phaseBCorrect
    file tokens owned result.recognition recognitionSelected
  let final := Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
    file tokens owned result.recognition recognitionSelected
  change RootlessExecutableProgress
    file tokens result.recognition.memo correct final at progress
  cases parsedEq : result.parsedModule? with
  | some module =>
      apply Option.isSome_iff_exists.mpr
      exact ⟨.ok module,
        (Chart.ContextualValueWorklistResult.parseOutcome?_eq_some_ok_iff
          file result module).mpr parsedEq⟩
  | none =>
      cases repeatedEq :
          result.repeatedNonAssociativeDiagnosticCandidate? file with
      | some diagnostic =>
          apply Option.isSome_iff_exists.mpr
          exact ⟨.error diagnostic,
            (Chart.ContextualValueWorklistResult.parseOutcome?_eq_some_error_iff
              file result diagnostic).mpr
              ⟨parsedEq, Or.inl repeatedEq⟩⟩
      | none =>
          have rootAbsentBit :
              result.recognition.containsCompleteModuleRootItem = false := by
            cases rootEq :
                result.recognition.containsCompleteModuleRootItem with
            | false => rfl
            | true =>
                have parsedSome :=
                  (executeObservedContextualValueWorklistMulti?_parsedModule?_isSome_eq_true_iff_completeModuleRoot
                    file tokens owned result selected).mpr rootEq
                simp [parsedEq] at parsedSome
          obtain ⟨cursor, greatest⟩ :=
            chart_greatest_cursor_exists owned correct final
          have rootAbsent : ¬ ContextualReach file tokens
              result.recognition.memo correct final
              (CanonicalCompleteRootItem tokens .module
                (Boundary.start tokens) (Boundary.afterLogicalEOF tokens)
                .plain) := by
            intro rootReached
            have rootPresent :=
              (executeObservedContextualWorklistMulti?_containsCompleteModuleRootItem_eq_true_iff
                file tokens owned result.recognition recognitionSelected).mpr
                rootReached
            rw [rootAbsentBit] at rootPresent
            contradiction
          rcases progress cursor greatest rootAbsent with
            ⟨atMost, coverage, ranked⟩
          have waiting :=
            terminalFrontierWait_of_rootless_rankedNormalization
              greatest coverage ranked rootAbsent
          have ordinarySome :=
            executeObservedContextualWorklistMulti?_rootlessUnexpectedDiagnosticCandidate?_isSome_of_progress
              file tokens owned result.recognition recognitionSelected
                rootAbsentBit cursor greatest atMost waiting
          obtain ⟨diagnostic, ordinaryEq⟩ :=
            Option.isSome_iff_exists.mp ordinarySome
          apply Option.isSome_iff_exists.mpr
          exact ⟨.error diagnostic,
            (Chart.ContextualValueWorklistResult.parseOutcome?_eq_some_error_iff
              file result diagnostic).mpr
              ⟨parsedEq, Or.inr ⟨repeatedEq, ordinaryEq⟩⟩⟩

/-- Executable parse outcome with the remaining frontier-progress certificate
passed as a proof-erased argument. -/
def executeObservedContextualParseOfProgress
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (progress :
      let result := Chart.executeObservedContextualValueWorklistMulti
        file tokens owned
      let selected :=
        Chart.executeObservedContextualValueWorklistMulti_selected
          file tokens owned
      let recognitionSelected :=
        Chart.executeObservedContextualValueWorklistMulti?_recognition
          file tokens owned result selected
      let correct := executeObservedContextualWorklistMulti?_phaseBCorrect
        file tokens owned result.recognition recognitionSelected
      let final :=
        Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
          file tokens owned result.recognition recognitionSelected
      RootlessExecutableProgress
        file tokens result.recognition.memo correct final) :
    Except ParseDiagnostic ParsedModuleV1 :=
  let result := Chart.executeObservedContextualValueWorklistMulti
    file tokens owned
  let selected := Chart.executeObservedContextualValueWorklistMulti_selected
    file tokens owned
  (result.parseOutcome? file).get
    (executeObservedContextualValueWorklistMulti?_parseOutcome?_isSome_of_progress
      file tokens owned result selected progress)

/-- The certificate-driven executable outcome is exactly the value selected
by the option-based implementation. -/
theorem executeObservedContextualParseOfProgress_selected
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (progress :
      let result := Chart.executeObservedContextualValueWorklistMulti
        file tokens owned
      let selected :=
        Chart.executeObservedContextualValueWorklistMulti_selected
          file tokens owned
      let recognitionSelected :=
        Chart.executeObservedContextualValueWorklistMulti?_recognition
          file tokens owned result selected
      let correct := executeObservedContextualWorklistMulti?_phaseBCorrect
        file tokens owned result.recognition recognitionSelected
      let final :=
        Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
          file tokens owned result.recognition recognitionSelected
      RootlessExecutableProgress
        file tokens result.recognition.memo correct final) :
    let result := Chart.executeObservedContextualValueWorklistMulti
      file tokens owned
    result.parseOutcome? file =
      some (executeObservedContextualParseOfProgress
        file tokens owned progress) := by
  dsimp only
  unfold executeObservedContextualParseOfProgress
  apply Option.eq_some_iff_get_eq.mpr
  exact ⟨
    executeObservedContextualValueWorklistMulti?_parseOutcome?_isSome_of_progress
      file tokens owned
        (Chart.executeObservedContextualValueWorklistMulti file tokens owned)
        (Chart.executeObservedContextualValueWorklistMulti_selected
          file tokens owned)
        progress,
    rfl⟩

/-- The certificate-driven executable result is declaratively sound: modules
parse, and diagnostics apply to the supplied source. -/
theorem executeObservedContextualParseOfProgress_sound
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (progress :
      let result := Chart.executeObservedContextualValueWorklistMulti
        file tokens owned
      let selected :=
        Chart.executeObservedContextualValueWorklistMulti_selected
          file tokens owned
      let recognitionSelected :=
        Chart.executeObservedContextualValueWorklistMulti?_recognition
          file tokens owned result selected
      let correct := executeObservedContextualWorklistMulti?_phaseBCorrect
        file tokens owned result.recognition recognitionSelected
      let final :=
        Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
          file tokens owned result.recognition recognitionSelected
      RootlessExecutableProgress
        file tokens result.recognition.memo correct final)
    (invariant :
      let result := Chart.executeObservedContextualValueWorklistMulti
        file tokens owned
      let selected :=
        Chart.executeObservedContextualValueWorklistMulti_selected
          file tokens owned
      let recognitionSelected :=
        Chart.executeObservedContextualValueWorklistMulti?_recognition
          file tokens owned result selected
      let correct := executeObservedContextualWorklistMulti?_phaseBCorrect
        file tokens owned result.recognition recognitionSelected
      let final :=
        Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
          file tokens owned result.recognition recognitionSelected
      CoherentNonAssociativeRootCompletedInvariant
        file tokens result.recognition.memo correct final) :
    match executeObservedContextualParseOfProgress
        file tokens owned progress with
    | .ok module => Parses file tokens module
    | .error diagnostic => ParseDiagnostic.Applies file tokens diagnostic := by
  let result := Chart.executeObservedContextualValueWorklistMulti
    file tokens owned
  let selected := Chart.executeObservedContextualValueWorklistMulti_selected
    file tokens owned
  have outcomeSelected : result.parseOutcome? file =
      some (executeObservedContextualParseOfProgress
        file tokens owned progress) :=
    executeObservedContextualParseOfProgress_selected
      file tokens owned progress
  cases outcomeEq : executeObservedContextualParseOfProgress
      file tokens owned progress with
  | ok module =>
      rw [outcomeEq] at outcomeSelected
      exact
        executeObservedContextualValueWorklistMulti?_parseOutcome?_ok_sound
          file tokens owned result selected module outcomeSelected
  | error diagnostic =>
      rw [outcomeEq] at outcomeSelected
      exact
        executeObservedContextualValueWorklistMulti?_parseOutcome?_error_sound
          file tokens owned result selected invariant diagnostic outcomeSelected

end Solcore.Surface.Multi
