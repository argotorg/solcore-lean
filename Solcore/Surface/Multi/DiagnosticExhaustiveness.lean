import Solcore.Surface.Multi.ChartProperties

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

/-- The local semantic condition needed to make the selected executable G10
classifier exhaustive.  It asks only that completed-operation shape, rather
than the whole expression value, be invariant between coherent reductions of
one canonical equality or relational root. -/
def CoherentNonAssociativeRootCompletedInvariant
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) : Prop :=
  ∀ (level : NonAssociativeLevel) (origin cursor : Boundary tokens)
      (context : GuardContext tokens)
      (left right : RuleValue level.rule),
    CoherentReduction file tokens memo correct final
        (CanonicalCompleteRootItem tokens level.rule origin cursor context)
        left →
      CoherentReduction file tokens memo correct final
        (CanonicalCompleteRootItem tokens level.rule origin cursor context)
        right →
      ((∃ first, CompletedNonAssociativeValue level left first) ↔
        ∃ first, CompletedNonAssociativeValue level right first)

/-- Full completion-backpointer uniqueness is sufficient for the local
classifier invariant, but downstream exhaustiveness uses only the latter. -/
theorem coherentNonAssociativeRootCompletedInvariant_of_completionBackpointer
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (backpointer : CompletionBackpointerUnique
      file tokens memo correct final) :
    CoherentNonAssociativeRootCompletedInvariant
      file tokens memo correct final := by
  intro level origin cursor context left right leftCoherent rightCoherent
  have same := CoherentReduction.functional_of_completionBackpointer
    backpointer leftCoherent rightCoherent
  subst right
  rfl

private theorem coherentCanonicalRootReduction_castRule
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {left right : GrammarRuleId}
    (same : left = right)
    (origin finish : Boundary tokens) (context : GuardContext tokens)
    (value : RuleValue left)
    (coherent : CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens left origin finish context) value) :
    CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens right origin finish context)
      (same ▸ value) := by
  cases same
  exact coherent

/-- Under local completed-shape invariance, every declarative G10 witness is
found by the semantic executor's selected-value diagnostic classifier. -/
theorem executeObservedContextualValueWorklistMulti?_repeatedNonAssociativeAt_implies_candidate
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualValueWorklistResult file tokens)
    (selected : Chart.executeObservedContextualValueWorklistMulti?
      file tokens owned = some result)
    (invariant :
      let recognitionSelected :=
        Chart.executeObservedContextualValueWorklistMulti?_recognition
          file tokens owned result selected
      let correct := executeObservedContextualWorklistMulti?_phaseBCorrect
        file tokens owned result.recognition recognitionSelected
      let final :=
        Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
          file tokens owned result.recognition recognitionSelected
      CoherentNonAssociativeRootCompletedInvariant
        file tokens result.recognition.memo correct final)
    (cursor : Boundary tokens) (level : NonAssociativeLevel)
    (operator : Located InfixOperator)
    (repeated :
      let recognitionSelected :=
        Chart.executeObservedContextualValueWorklistMulti?_recognition
          file tokens owned result selected
      let correct := executeObservedContextualWorklistMulti?_phaseBCorrect
        file tokens owned result.recognition recognitionSelected
      let final :=
        Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
          file tokens owned result.recognition recognitionSelected
      RepeatedNonAssociativeAt file tokens result.recognition.memo
        correct final cursor level operator) :
    result.repeatedNonAssociativeDiagnosticCandidate? file =
      some (.repeatedNonAssociative operator.span level operator) := by
  let recognitionSelected :=
    Chart.executeObservedContextualValueWorklistMulti?_recognition
      file tokens owned result selected
  let correct := executeObservedContextualWorklistMulti?_phaseBCorrect
    file tokens owned result.recognition recognitionSelected
  let final := Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
    file tokens owned result.recognition recognitionSelected
  change CoherentNonAssociativeRootCompletedInvariant
      file tokens result.recognition.memo correct final at invariant
  change RepeatedNonAssociativeAt file tokens result.recognition.memo
      correct final cursor level operator at repeated
  rcases repeated with
    ⟨candidate, first, completed, _ungrouped, found⟩
  let root := CanonicalCompleteRootItem tokens
    (Chart.nonAssociativeRootRule level) candidate.origin cursor
      candidate.context
  have rootRuleEq : root = CanonicalCompleteRootItem tokens level.rule
      candidate.origin cursor candidate.context := by
    simp [root, Chart.nonAssociativeRootRule_eq_rule]
  have correspondence := executeObservedContextualWorklistMulti?_correspondence
    file tokens owned result.recognition recognitionSelected
  have rootRetained : root ∈ result.recognition.items :=
    (correspondence.1 root).mpr (rootRuleEq.symm ▸ candidate.root.1)
  let frontier : Chart.NonAssociativeFrontierCandidates tokens := {
    cursor := cursor
    level := level
    operator := operator
    roots := result.recognition.nonAssociativeRootItemsAt cursor level
  }
  have greatestSelected : result.recognition.greatestCurrent? = some cursor :=
    (Chart.ContextualWorklistResult.greatestCurrent?_eq_some_iff
      result.recognition cursor).mpr ⟨⟨root, rootRetained,
        by simpa [root] using candidate.frontier.2.2⟩, fun item member =>
          candidate.frontier.1.2 item
            ((correspondence.1 item).mp member)⟩
  have foundSelected : Chart.observedNonAssociativeOperatorAt?
      file tokens cursor = some {
        level := level
        operator := operator
      } :=
    (chart_observedNonAssociativeOperatorAt?_eq_some_iff owned cursor {
      level := level
      operator := operator
    }).mpr found
  have frontierSelected :
      result.recognition.nonAssociativeFrontierCandidates? file =
        some frontier := by
    apply
      (Chart.ContextualWorklistResult.nonAssociativeFrontierCandidates?_eq_some_iff
        file result.recognition frontier).mpr
    exact ⟨greatestSelected, foundSelected, rfl⟩
  have rootMember : root ∈ frontier.roots := by
    apply
      (Chart.ContextualWorklistResult.nonAssociativeRootItemsAt_mem_iff
        result.recognition cursor level root).mpr
    exact ⟨rootRetained, rfl⟩
  have materialized :=
    executeObservedContextualValueWorklistMulti?_recognitionPrefixesMaterialized
      file tokens owned result selected
  have prefixPresent : result.frontier.prefixMemberBool root = true :=
    materialized root rootRetained
  have prefixMember : root ∈ result.frontier.prefixKeys :=
    (result.frontier.prefixMemberBool_eq_true_iff root).mp prefixPresent
  have wellFormed :=
    executeObservedContextualValueWorklistMulti?_executableWellFormed
      file tokens owned result selected
  have reductionMember : root ∈ result.frontier.reductionKeys :=
    wellFormed.2 root prefixMember candidate.root.2.1
  have reductionSome : (result.frontier.lookupReduction? root).isSome = true :=
    (result.frontier.lookupReduction?_isSome_eq_true_iff_member root).mpr
      reductionMember
  obtain ⟨reduction, reductionEq⟩ := Option.isSome_iff_exists.mp reductionSome
  have valuesCoherent :=
    executeObservedContextualValueWorklistMulti?_valuesCoherent
      file tokens owned result selected
  have coherentSelected := result.frontier.lookupReduction?_coherent
    root reduction valuesCoherent reductionEq
  let selectedValue : RuleValue level.rule :=
    Chart.nonAssociativeRootRule_eq_rule level ▸ reduction.value
  have coherentSelectedAtRule : CoherentReduction file tokens
      result.recognition.memo correct final
      (CanonicalCompleteRootItem tokens level.rule candidate.origin cursor
        candidate.context) selectedValue :=
    coherentCanonicalRootReduction_castRule
      (Chart.nonAssociativeRootRule_eq_rule level)
      candidate.origin cursor candidate.context reduction.value
        coherentSelected
  have selectedCompleted : ∃ selectedFirst,
      CompletedNonAssociativeValue level selectedValue selectedFirst :=
    (invariant level candidate.origin cursor candidate.context
      candidate.value selectedValue candidate.root.2.2
        coherentSelectedAtRule).mp
      ⟨first,
        (completedNonAssociative_iff_value level candidate first).mp completed⟩
  have completedBool : Chart.completedNonAssociativeValueBool
      level reduction.value = true :=
    (Chart.completedNonAssociativeValueBool_eq_true_iff
      level reduction.value).mpr selectedCompleted
  have accepted : result.frontier.completedNonAssociativeAtBool cursor level
      candidate.origin candidate.context = true :=
    (Chart.ContextualValueFrontierState.completedNonAssociativeAtBool_eq_true_iff
      result.frontier cursor level candidate.origin candidate.context).mpr
      ⟨reduction, by simpa [root] using reductionEq, completedBool⟩
  unfold Chart.ContextualValueWorklistResult.repeatedNonAssociativeDiagnosticCandidate?
  rw [frontierSelected]
  apply
    (Chart.NonAssociativeFrontierCandidates.repeatedDiagnosticCandidate?_eq_some_iff
      frontier (fun root =>
        result.frontier.completedNonAssociativeAtBool frontier.cursor
          frontier.level root.raw.origin root.context)
      (.repeatedNonAssociative operator.span level operator)).mpr
  refine ⟨⟨root, rootMember, ?_⟩, rfl⟩
  simpa [frontier, root, CanonicalCompleteRootItem] using accepted

/-- Consequently, a missing semantic G10 candidate refutes every declarative
repeated-nonassociative witness at the displayed frontier. -/
theorem executeObservedContextualValueWorklistMulti?_candidate_none_implies_notRepeated
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualValueWorklistResult file tokens)
    (selected : Chart.executeObservedContextualValueWorklistMulti?
      file tokens owned = some result)
    (invariant :
      let recognitionSelected :=
        Chart.executeObservedContextualValueWorklistMulti?_recognition
          file tokens owned result selected
      let correct := executeObservedContextualWorklistMulti?_phaseBCorrect
        file tokens owned result.recognition recognitionSelected
      let final :=
        Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
          file tokens owned result.recognition recognitionSelected
      CoherentNonAssociativeRootCompletedInvariant
        file tokens result.recognition.memo correct final)
    (absent : result.repeatedNonAssociativeDiagnosticCandidate? file = none) :
    let recognitionSelected :=
      Chart.executeObservedContextualValueWorklistMulti?_recognition
        file tokens owned result selected
    let correct := executeObservedContextualWorklistMulti?_phaseBCorrect
      file tokens owned result.recognition recognitionSelected
    let final :=
        Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
        file tokens owned result.recognition recognitionSelected
    ∀ cursor level operator,
      ¬ RepeatedNonAssociativeAt file tokens result.recognition.memo
        correct final cursor level operator := by
  dsimp only
  intro cursor level operator repeated
  have emitted :=
    executeObservedContextualValueWorklistMulti?_repeatedNonAssociativeAt_implies_candidate
      file tokens owned result selected invariant cursor level operator repeated
  rw [absent] at emitted
  contradiction

/-- Every successful parse outcome emitted by semantic execution is a
declaratively valid parse. -/
theorem executeObservedContextualValueWorklistMulti?_parseOutcome?_ok_sound
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualValueWorklistResult file tokens)
    (selected : Chart.executeObservedContextualValueWorklistMulti?
      file tokens owned = some result)
    (module : ParsedModuleV1)
    (outcome : result.parseOutcome? file = some (.ok module)) :
    Parses file tokens module := by
  have parsed :=
    (Chart.ContextualValueWorklistResult.parseOutcome?_eq_some_ok_iff
      file result module).mp outcome
  exact executeObservedContextualValueWorklistMulti?_parses
    file tokens owned result selected module parsed

/-- Under only the local completed-shape invariant, every error already
emitted by the parse outcome is declaratively applicable. -/
theorem executeObservedContextualValueWorklistMulti?_parseOutcome?_error_sound
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualValueWorklistResult file tokens)
    (selected : Chart.executeObservedContextualValueWorklistMulti?
      file tokens owned = some result)
    (invariant :
      let recognitionSelected :=
        Chart.executeObservedContextualValueWorklistMulti?_recognition
          file tokens owned result selected
      let correct := executeObservedContextualWorklistMulti?_phaseBCorrect
        file tokens owned result.recognition recognitionSelected
      let final :=
        Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
          file tokens owned result.recognition recognitionSelected
      CoherentNonAssociativeRootCompletedInvariant
        file tokens result.recognition.memo correct final)
    (diagnostic : ParseDiagnostic)
    (outcome : result.parseOutcome? file = some (.error diagnostic)) :
    ParseDiagnostic.Applies file tokens diagnostic := by
  let recognitionSelected :=
    Chart.executeObservedContextualValueWorklistMulti?_recognition
      file tokens owned result selected
  rcases
      (Chart.ContextualValueWorklistResult.parseOutcome?_eq_some_error_iff
        file result diagnostic).mp outcome with
    ⟨parsedAbsent, repeated | ⟨repeatedAbsent, ordinary⟩⟩
  have rootAbsent :
      result.recognition.containsCompleteModuleRootItem = false := by
    cases rootEq : result.recognition.containsCompleteModuleRootItem with
    | false => rfl
    | true =>
        have parsedSome :=
          (executeObservedContextualValueWorklistMulti?_parsedModule?_isSome_eq_true_iff_completeModuleRoot
            file tokens owned result selected).mpr rootEq
        simp [parsedAbsent] at parsedSome
  · exact
      executeObservedContextualValueWorklistMulti?_repeatedNonAssociativeDiagnosticCandidate?_applies
        file tokens owned result selected rootAbsent diagnostic repeated
  · have notRepeated :=
      executeObservedContextualValueWorklistMulti?_candidate_none_implies_notRepeated
        file tokens owned result selected invariant repeatedAbsent
    cases diagnostic with
    | unexpected span found expected =>
        exact
          executeObservedContextualWorklistMulti?_rootlessUnexpectedDiagnosticCandidate?_applies
            file tokens owned result.recognition recognitionSelected
              span found expected ordinary notRepeated
    | repeatedNonAssociative span level operator =>
        unfold Chart.ContextualWorklistResult.rootlessUnexpectedDiagnosticCandidate?
          at ordinary
        split at ordinary
        · contradiction
        · unfold Chart.ContextualWorklistResult.unexpectedDiagnosticCandidate?
            at ordinary
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at ordinary
          rcases ordinary with ⟨frontier, _selectedFrontier, impossible⟩
          cases frontier with
          | mk frontierCursor frontierSpan frontierFound frontierExpected =>
              cases frontierExpected <;>
                simp [Chart.ObservedFrontier.unexpected?] at impossible

/-- The exact declarative progress witnesses produce an executable rootless
ordinary diagnostic on a saturated multi-ledger result.  This is the direct
consumer of the remaining rootless-frontier progress theorem. -/
theorem executeObservedContextualWorklistMulti?_rootlessUnexpectedDiagnosticCandidate?_isSome_of_progress
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklistMulti?
      file tokens owned = some result)
    (absent : result.containsCompleteModuleRootItem = false)
    (cursor : Boundary tokens)
    (greatest : GreatestReachableCursor file tokens result.memo
      (executeObservedContextualWorklistMulti?_phaseBCorrect
        file tokens owned result selected)
      (Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
        file tokens owned result selected)
      cursor)
    (atMost : cursor.val ≤ tokens.length)
    (waiting : TerminalFrontierWait file tokens result.memo
      (executeObservedContextualWorklistMulti?_phaseBCorrect
        file tokens owned result selected)
      (Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
        file tokens owned result selected)
      cursor) :
    (result.rootlessUnexpectedDiagnosticCandidate? file).isSome = true := by
  let correct := executeObservedContextualWorklistMulti?_phaseBCorrect
    file tokens owned result selected
  let final := Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
    file tokens owned result selected
  change GreatestReachableCursor file tokens result.memo correct final cursor
    at greatest
  change TerminalFrontierWait file tokens result.memo correct final cursor
    at waiting
  have correspondence := executeObservedContextualWorklistMulti?_correspondence
    file tokens owned result selected
  have greatestSelected : result.greatestCurrent? = some cursor := by
    apply (Chart.ContextualWorklistResult.greatestCurrent?_eq_some_iff
      result cursor).mpr
    rcases greatest.1 with ⟨item, reached, current⟩
    refine ⟨⟨item, (correspondence.1 item).mpr reached, current⟩, ?_⟩
    intro candidate member
    exact greatest.2 candidate ((correspondence.1 candidate).mp member)
  rcases waiting with
    ⟨waitingItem, terminal, waitingFrontier, next, _enabled⟩
  have expectedMember : terminal.expected ∈
      result.expectedAtCurrent cursor :=
    (Chart.ContextualWorklistResult.expectedAtCurrent_mem_iff
      result cursor terminal.expected).mpr
      ⟨waitingItem,
        (correspondence.1 waitingItem).mpr waitingFrontier.2.1,
        waitingFrontier.2.2, terminal, next, rfl⟩
  cases expectedEq : result.expectedAtCurrent cursor with
  | nil =>
      rw [expectedEq] at expectedMember
      contradiction
  | cons head tail =>
      let expectedFrontier : Chart.ExpectedFrontier tokens := {
        cursor := cursor
        expected := head :: tail
      }
      have expectedFrontierEq : result.expectedFrontier? =
          some expectedFrontier := by
        apply
          (Chart.ContextualWorklistResult.expectedFrontier?_eq_some_iff
            result expectedFrontier).mpr
        exact ⟨greatestSelected, by simpa [expectedFrontier] using
          expectedEq.symm⟩
      have observationSome :
          (Chart.observedFoundAt? file tokens cursor).isSome = true := by
        unfold Chart.observedFoundAt?
        split <;> rename_i inRange
        · simp
        · split <;> rename_i atEnd
          · simp
          · omega
      obtain ⟨observation, observationEq⟩ :=
        Option.isSome_iff_exists.mp observationSome
      let frontier : Chart.ObservedFrontier tokens := {
        cursor := cursor
        span := observation.span
        found := observation.found
        expected := head :: tail
      }
      have frontierEq : result.observedFrontier? file = some frontier := by
        unfold Chart.ContextualWorklistResult.observedFrontier?
        simp [expectedFrontierEq, observationEq, expectedFrontier, frontier]
      let expected : NonemptyList Expected := { head := head, tail := tail }
      let diagnostic : ParseDiagnostic :=
        .unexpected observation.span observation.found expected
      have unexpectedEq : frontier.unexpected? = some diagnostic := by
        simp [Chart.ObservedFrontier.unexpected?, frontier, diagnostic,
          expected]
      have ordinaryEq : result.unexpectedDiagnosticCandidate? file =
          some diagnostic := by
        unfold Chart.ContextualWorklistResult.unexpectedDiagnosticCandidate?
        simp [frontierEq, unexpectedEq]
      have rootlessEq : result.rootlessUnexpectedDiagnosticCandidate? file =
          some diagnostic := by
        unfold
          Chart.ContextualWorklistResult.rootlessUnexpectedDiagnosticCandidate?
        simp [absent, ordinaryEq]
      exact Option.isSome_iff_exists.mpr ⟨diagnostic, rootlessEq⟩

end Solcore.Surface.Multi
