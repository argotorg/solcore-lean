import Solcore.Surface.Multi.Chart
import Solcore.Surface.Multi.ParserJudgment

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace
open Grammar

/-- A normalized Phase-B observation denotes exactly one declarative guard
decision, provided its positive bit and G02 pipe bit are exact. -/
theorem guardEvidence_iff_classified_observation
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (key : GuardInstanceKey tokens)
    (positive pipeAtSite : Bool)
    (positiveExact :
      positive = true ↔ GuardEvidence file tokens key .positive)
    (pipeExact :
      key.guard = .G02_matchArmBoundary →
        (pipeAtSite = true ↔
          SymbolAtBoundary file tokens key.siteCursor .pipe))
    (decision : GuardDecision) :
    Chart.classifyGuardObservation key.guard positive pipeAtSite =
        decision ↔
      GuardEvidence file tokens key decision := by
  have classifiedEvidence : GuardEvidence file tokens key
      (Chart.classifyGuardObservation key.guard positive pipeAtSite) := by
    rcases key with ⟨guard, contextStart, siteCursor, ordered⟩
    by_cases selected : positive = true
    · have evidence := positiveExact.mp selected
      simpa [Chart.classifyGuardObservation, selected] using evidence
    · have positiveFalse : positive = false :=
        Bool.eq_false_iff.mpr selected
      have notPositive : ¬ GuardEvidence file tokens
          { guard := guard, contextStart := contextStart,
            siteCursor := siteCursor, ordered := ordered }
          .positive := by
        intro evidence
        exact selected (positiveExact.mpr evidence)
      cases guard with
      | G01_statementIf =>
          simp only [Chart.classifyGuardObservation, positiveFalse,
            Bool.false_eq_true, ↓reduceIte]
          refine ⟨owned, ?_⟩
          intro evidence
          exact notPositive ⟨owned, evidence⟩
      | G02_matchArmBoundary =>
          by_cases pipeSelected : pipeAtSite = true
          · have pipeEvidence := (pipeExact rfl).mp pipeSelected
            simp only [Chart.classifyGuardObservation, positiveFalse,
              Bool.false_eq_true, ↓reduceIte, pipeSelected]
            refine ⟨owned, pipeEvidence, ?_⟩
            intro evidence
            exact notPositive ⟨owned, evidence⟩
          · have pipeFalse : pipeAtSite = false :=
              Bool.eq_false_iff.mpr pipeSelected
            have noPipe :
                ¬ SymbolAtBoundary file tokens siteCursor .pipe := by
              intro evidence
              exact pipeSelected ((pipeExact rfl).mpr evidence)
            simp only [Chart.classifyGuardObservation, positiveFalse,
              Bool.false_eq_true, ↓reduceIte, pipeFalse]
            exact ⟨owned, noPipe⟩
      | G03_parameterComptime =>
          simp only [Chart.classifyGuardObservation, positiveFalse,
            Bool.false_eq_true, ↓reduceIte]
          refine ⟨owned, ?_⟩
          intro evidence
          exact notPositive ⟨owned, evidence⟩
      | G04_letComptime =>
          simp only [Chart.classifyGuardObservation, positiveFalse,
            Bool.false_eq_true, ↓reduceIte]
          refine ⟨owned, ?_⟩
          intro evidence
          exact notPositive ⟨owned, evidence⟩
      | G05_typeComptime =>
          simp only [Chart.classifyGuardObservation, positiveFalse,
            Bool.false_eq_true, ↓reduceIte]
          refine ⟨owned, ?_⟩
          intro evidence
          exact notPositive ⟨owned, evidence⟩
      | G06_patternComptime =>
          simp only [Chart.classifyGuardObservation, positiveFalse,
            Bool.false_eq_true, ↓reduceIte]
          refine ⟨owned, ?_⟩
          intro evidence
          exact notPositive ⟨owned, evidence⟩
      | G07_leadingDotArguments =>
          simp only [Chart.classifyGuardObservation, positiveFalse,
            Bool.false_eq_true, ↓reduceIte]
          refine ⟨owned, ?_⟩
          intro evidence
          exact notPositive ⟨owned, evidence⟩
      | G08_terminalExpression =>
          simp only [Chart.classifyGuardObservation, positiveFalse,
            Bool.false_eq_true, ↓reduceIte]
          refine ⟨owned, ?_⟩
          intro evidence
          exact notPositive ⟨owned, evidence⟩
      | G09_genericContext =>
          simp only [Chart.classifyGuardObservation, positiveFalse,
            Bool.false_eq_true, ↓reduceIte]
          refine ⟨owned, ?_⟩
          intro evidence
          exact notPositive ⟨owned, evidence⟩
  constructor
  · intro selected
    simpa only [selected] using classifiedEvidence
  · intro evidence
    exact GuardEvidence.functional classifiedEvidence evidence

/-- Pointwise-exact normalized observations assemble a correct final table. -/
theorem phaseBCorrect_of_exact_guard_observations
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (positive pipeAtSite : GuardInstanceKey tokens → Bool)
    (positiveExact : ∀ key,
      positive key = true ↔
        GuardEvidence file tokens key .positive)
    (pipeExact : ∀ key,
      key.guard = .G02_matchArmBoundary →
        (pipeAtSite key = true ↔
          SymbolAtBoundary file tokens key.siteCursor .pipe)) :
    PhaseBCorrect file tokens (fun key =>
      .final (Chart.classifyGuardObservation key.guard
        (positive key) (pipeAtSite key))) := by
  intro key decision
  rw [GuardMemoState.final.injEq]
  exact guardEvidence_iff_classified_observation owned key
    (positive key) (pipeAtSite key) (positiveExact key)
      (pipeExact key) decision


/-- The Chart terminal observation is exactly the checked terminal witness. -/
theorem chart_observedTerminalAtBool_eq_true_iff
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (terminal : TerminalSymbol) (boundary : Boundary tokens) :
    Chart.observedTerminalAtBool owned terminal boundary = true ↔
      ∃ matched : MatchedTerminal file tokens terminal,
        matched.cursor.beforeBoundary = boundary := by
  constructor
  · intro accepted
    unfold Chart.observedTerminalAtBool at accepted
    split at accepted
    case isFalse => simp at accepted
    case isTrue inRange =>
      let cursor : TerminalCursor tokens := ⟨boundary.val, inRange⟩
      change (MatchedTerminal.atCursor?
        file tokens owned terminal cursor).isSome = true at accepted
      obtain ⟨result, selected⟩ := Option.isSome_iff_exists.mp accepted
      refine ⟨result.val, ?_⟩
      apply Fin.ext
      have cursorEq := congrArg Fin.val result.property
      change result.val.cursor.val = boundary.val
      simpa [cursor] using cursorEq
  · rintro ⟨matched, atBoundary⟩
    have inRange : boundary.val < tokens.length + 1 := by
      have cursorEq := congrArg Fin.val atBoundary
      change matched.cursor.val = boundary.val at cursorEq
      omega
    let cursor : TerminalCursor tokens := ⟨boundary.val, inRange⟩
    have cursorEq : matched.cursor = cursor := by
      apply Fin.ext
      have atValue := congrArg Fin.val atBoundary
      change matched.cursor.val = boundary.val at atValue
      simpa [cursor] using atValue
    have terminalAt : TerminalAt file tokens cursor
        matched.value matched.span := by
      simpa only [← cursorEq] using matched.at
    obtain ⟨result, selected⟩ := MatchedTerminal.atCursor?_complete
      owned terminal cursor terminalAt matched.matches
    unfold Chart.observedTerminalAtBool
    rw [dif_pos inRange]
    change (MatchedTerminal.atCursor?
      file tokens owned terminal cursor).isSome = true
    rw [selected]
    rfl

/-- Symbol-terminal observation specializes to the public symbol judgment. -/
theorem chart_observedSymbolAtBool_eq_true_iff
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (cursor : Boundary tokens) (symbol : Symbol) :
    Chart.observedTerminalAtBool owned (.symbol symbol) cursor = true ↔
      SymbolAtBoundary file tokens cursor symbol := by
  rw [chart_observedTerminalAtBool_eq_true_iff]
  constructor
  · rintro ⟨matched, atCursor⟩
    rcases matched with
      ⟨terminalCursor, value, span, terminalAt, matchedEvidence⟩
    cases value with
    | retained token =>
        cases terminalAt with
        | retained _ inRange lookup valid =>
            refine ⟨terminalCursor, token, atCursor,
              .retained terminalCursor token inRange lookup valid, ?_⟩
            simpa [TerminalMatches] using matchedEvidence
    | endOfFile =>
        simp [TerminalMatches] at matchedEvidence
  · rintro ⟨terminalCursor, token, atCursor, terminalAt, payload⟩
    refine ⟨{
      cursor := terminalCursor
      value := .retained token
      span := token.span
      «at» := terminalAt
      «matches» := ?_
    }, atCursor⟩
    simpa [TerminalMatches] using payload

/-- The Chart exact-slice observation is the declarative exact slice. -/
theorem chart_observedExactSliceBool_eq_true_iff
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (start finish : Boundary tokens)
    (classes : List TerminalSymbol) :
    Chart.observedExactSliceBool tokens start finish classes = true ↔
      ExactSlice file tokens start finish classes := by
  have executableEq :
      Chart.observedExactSliceBool tokens start finish classes =
        exactSliceBool file tokens owned start finish classes := by
    rfl
  rw [executableEq]
  exact exactSliceBool_eq_true_iff owned start finish classes

/-- G03--G05 and G07 have saturation-independent exact positive bits. -/
theorem basicGuardPositiveObservation?_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (key : GuardInstanceKey tokens)
    (supported :
      key.guard = .G03_parameterComptime ∨
      key.guard = .G04_letComptime ∨
      key.guard = .G05_typeComptime ∨
      key.guard = .G07_leadingDotArguments) :
    ∃ observed,
      Chart.basicGuardPositiveObservation? owned key = some observed ∧
        (observed = true ↔
          GuardEvidence file tokens key .positive) := by
  rcases key with ⟨guard, contextStart, siteCursor, ordered⟩
  cases guard with
  | G01_statementIf => simp at supported
  | G02_matchArmBoundary => simp at supported
  | G03_parameterComptime =>
      refine ⟨Chart.observedTerminalAtBool owned
        (.contextualKeyword .comptimeKw) siteCursor, rfl, ?_⟩
      simpa [GuardEvidence, owned] using
        chart_observedTerminalAtBool_eq_true_iff owned
          (.contextualKeyword .comptimeKw) siteCursor
  | G04_letComptime =>
      refine ⟨Chart.observedTerminalAtBool owned
        (.contextualKeyword .comptimeKw) siteCursor, rfl, ?_⟩
      simpa [GuardEvidence, owned] using
        chart_observedTerminalAtBool_eq_true_iff owned
          (.contextualKeyword .comptimeKw) siteCursor
  | G05_typeComptime =>
      refine ⟨Chart.observedTerminalAtBool owned
        (.contextualKeyword .comptimeKw) siteCursor, rfl, ?_⟩
      simpa [GuardEvidence, owned] using
        chart_observedTerminalAtBool_eq_true_iff owned
          (.contextualKeyword .comptimeKw) siteCursor
  | G06_patternComptime => simp at supported
  | G07_leadingDotArguments =>
      refine ⟨Chart.observedExactSliceBool tokens
          contextStart siteCursor [
            .symbol .dot,
            .category .identifier
          ] &&
        Chart.observedTerminalAtBool owned
          (.symbol .leftParen) siteCursor, rfl, ?_⟩
      rw [Bool.and_eq_true,
        chart_observedExactSliceBool_eq_true_iff owned,
        chart_observedSymbolAtBool_eq_true_iff owned]
      simp [GuardEvidence, owned]
  | G08_terminalExpression => simp at supported
  | G09_genericContext => simp at supported

/-- G02's pipe bit is exact independently of its saturation-backed header. -/
theorem matchArmPipeObservationBool_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (key : GuardInstanceKey tokens) :
    Chart.matchArmPipeObservationBool owned key = true ↔
      SymbolAtBoundary file tokens key.siteCursor .pipe := by
  exact chart_observedSymbolAtBool_eq_true_iff
    owned key.siteCursor .pipe

/-- Each saturation-independent positive observation already classifies to
the exact declarative decision. -/
theorem basicGuardClassifiedObservation_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (key : GuardInstanceKey tokens)
    (supported :
      key.guard = .G03_parameterComptime ∨
      key.guard = .G04_letComptime ∨
      key.guard = .G05_typeComptime ∨
      key.guard = .G07_leadingDotArguments)
    {observed : Bool}
    (selected :
      Chart.basicGuardPositiveObservation? owned key = some observed)
    (decision : GuardDecision) :
    Chart.classifyGuardObservation key.guard observed false = decision ↔
      GuardEvidence file tokens key decision := by
  obtain ⟨canonical, canonicalSelected, exact⟩ :=
    basicGuardPositiveObservation?_exact owned key supported
  have observedEq : observed = canonical := by
    exact Option.some.inj (selected.symm.trans canonicalSelected)
  subst canonical
  apply guardEvidence_iff_classified_observation owned key observed false exact
  intro impossible
  exfalso
  rcases supported with supported | supported | supported | supported <;>
    simp_all

/-- Once the G02 header bit is saturation-exact, its already-exact pipe bit
closes the entire three-way decision. -/
theorem matchArmClassifiedObservation_exact_of_header
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (key : GuardInstanceKey tokens)
    (_isMatchArm : key.guard = .G02_matchArmBoundary)
    (header : Bool)
    (headerExact :
      header = true ↔ GuardEvidence file tokens key .positive)
    (decision : GuardDecision) :
    Chart.classifyGuardObservation key.guard header
        (Chart.matchArmPipeObservationBool owned key) = decision ↔
      GuardEvidence file tokens key decision := by
  exact guardEvidence_iff_classified_observation owned key header
    (Chart.matchArmPipeObservationBool owned key) headerExact
      (fun _ => matchArmPipeObservationBool_exact owned key) decision


/-- G09 is exact once the raw Phase-A greatest predicate-list end is exact. -/
theorem genericContextPositiveObservationBool_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (greatest : Chart.GreatestEndObservation tokens)
    (key : GuardInstanceKey tokens)
    (isGeneric : key.guard = .G09_genericContext)
    (greatestExact : ∀ start upperBound finish,
      greatest (.rule .predicateList) start upperBound finish = true ↔
        GreatestUnguardedEnd file tokens (.rule .predicateList)
          start upperBound finish) :
    Chart.genericContextPositiveObservationBool owned greatest key = true ↔
      GuardEvidence file tokens key .positive := by
  rcases key with ⟨guard, contextStart, siteCursor, ordered⟩
  change guard = .G09_genericContext at isGeneric
  subst guard
  simp [Chart.genericContextPositiveObservationBool, GuardEvidence, owned,
    List.any_eq_true, chart_observedSymbolAtBool_eq_true_iff,
    greatestExact]

/-- Thus G09's classifier is declaratively exact under only the explicit
Phase-A greatest-end adequacy boundary. -/
theorem genericContextClassifiedObservation_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (greatest : Chart.GreatestEndObservation tokens)
    (key : GuardInstanceKey tokens)
    (isGeneric : key.guard = .G09_genericContext)
    (greatestExact : ∀ start upperBound finish,
      greatest (.rule .predicateList) start upperBound finish = true ↔
        GreatestUnguardedEnd file tokens (.rule .predicateList)
          start upperBound finish)
    (decision : GuardDecision) :
    Chart.classifyGuardObservation key.guard
        (Chart.genericContextPositiveObservationBool owned greatest key)
        false = decision ↔
      GuardEvidence file tokens key decision := by
  apply guardEvidence_iff_classified_observation owned key
    (Chart.genericContextPositiveObservationBool owned greatest key)
      false
  · exact genericContextPositiveObservationBool_exact owned greatest key
      isGeneric greatestExact
  · intro impossible
    rw [isGeneric] at impossible
    contradiction


/-- Checked boundary construction succeeds exactly at its coordinate. -/
theorem chart_observedBoundaryAt?_eq_some_iff
    {tokens : List Token} (coordinate : Nat)
    (boundary : Boundary tokens) :
    Chart.observedBoundaryAt? tokens coordinate = some boundary ↔
      boundary.val = coordinate := by
  unfold Chart.observedBoundaryAt?
  split
  · constructor
    · intro selected
      exact congrArg Fin.val (Option.some.inj selected.symm)
    · intro coordinateEq
      apply congrArg some
      apply Fin.ext
      exact coordinateEq.symm
  · rename_i outOfRange
    constructor
    · intro impossible
      contradiction
    · intro coordinateEq
      exact False.elim (outOfRange (coordinateEq ▸ boundary.isLt))

/-- Immediate terminal observation is exactly the two-boundary witness. -/
theorem chart_observedImmediatelyAfterTerminalBool_eq_true_iff
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (terminal : TerminalSymbol)
    (boundary after : Boundary tokens) :
    Chart.observedImmediatelyAfterTerminalBool owned
        terminal boundary after = true ↔
      ∃ matched : MatchedTerminal file tokens terminal,
        matched.cursor.beforeBoundary = boundary ∧
          matched.cursor.afterBoundary = after := by
  unfold Chart.observedImmediatelyAfterTerminalBool
  rw [Bool.and_eq_true, decide_eq_true_iff,
    chart_observedTerminalAtBool_eq_true_iff]
  constructor
  · rintro ⟨⟨matched, atBoundary⟩, afterValue⟩
    refine ⟨matched, atBoundary, ?_⟩
    apply Fin.ext
    have beforeValue := congrArg Fin.val atBoundary
    change matched.cursor.val = boundary.val at beforeValue
    change matched.cursor.val + 1 = after.val
    omega
  · rintro ⟨matched, atBoundary, atAfter⟩
    refine ⟨⟨matched, atBoundary⟩, ?_⟩
    have beforeValue := congrArg Fin.val atBoundary
    have afterValue := congrArg Fin.val atAfter
    change matched.cursor.val = boundary.val at beforeValue
    change matched.cursor.val + 1 = after.val at afterValue
    omega

/-- G06 is exact under the explicit delimiter and greatest-end adequacy
contracts; all terminal and finite-search behavior is discharged here. -/
theorem patternComptimePositiveObservationBool_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (nextDelimiter : Chart.PatternDelimiterObservation tokens)
    (greatest : Chart.GreatestEndObservation tokens)
    (key : GuardInstanceKey tokens)
    (isPattern : key.guard = .G06_patternComptime)
    (nextExact : ∀ start limit,
      nextDelimiter start limit = true ↔
        NextSameDepthDelimiter tokens start limit {
          head := .comma
          tail := [.rightParen, .fatArrow]
        })
    (greatestExact : ∀ start upperBound finish,
      greatest (.rule .expression) start upperBound finish = true ↔
        GreatestUnguardedEnd file tokens (.rule .expression)
          start upperBound finish) :
    Chart.patternComptimePositiveObservationBool owned
        nextDelimiter greatest key = true ↔
      GuardEvidence file tokens key .positive := by
  rcases key with ⟨guard, contextStart, siteCursor, ordered⟩
  change guard = .G06_patternComptime at isPattern
  subst guard
  unfold Chart.patternComptimePositiveObservationBool
  cases boundarySelected :
      Chart.observedBoundaryAt? tokens (siteCursor.val + 1) with
  | none =>
      simp only
      constructor
      · intro impossible
        contradiction
      · intro evidence
        rcases evidence with
          ⟨_owned, expressionStart, limit, immediate, _next, _greatest⟩
        rcases immediate with ⟨matched, atSite, atExpression⟩
        have expressionValue : expressionStart.val = siteCursor.val + 1 := by
          have siteValue := congrArg Fin.val atSite
          have afterValue := congrArg Fin.val atExpression
          change matched.cursor.val = siteCursor.val at siteValue
          change matched.cursor.val + 1 = expressionStart.val at afterValue
          omega
        have existsBoundary :
            Chart.observedBoundaryAt? tokens (siteCursor.val + 1) =
              some expressionStart :=
          (chart_observedBoundaryAt?_eq_some_iff
            (siteCursor.val + 1) expressionStart).mpr expressionValue
        rw [boundarySelected] at existsBoundary
        contradiction
  | some expressionStart =>
      have expressionValue : expressionStart.val = siteCursor.val + 1 :=
        (chart_observedBoundaryAt?_eq_some_iff
          (siteCursor.val + 1) expressionStart).mp boundarySelected
      rw [show GuardEvidence file tokens {
          guard := .G06_patternComptime
          contextStart := contextStart
          siteCursor := siteCursor
          ordered := ordered
        } .positive =
          (TokensOwnedBy file tokens ∧
            ∃ expressionStart limit,
              (∃ matched : MatchedTerminal file tokens
                  (.contextualKeyword .comptimeKw),
                matched.cursor.beforeBoundary = siteCursor ∧
                  matched.cursor.afterBoundary = expressionStart) ∧
              NextSameDepthDelimiter tokens expressionStart limit {
                head := .comma
                tail := [.rightParen, .fatArrow]
              } ∧
              GreatestUnguardedEnd file tokens (.rule .expression)
                expressionStart limit limit) by rfl]
      constructor
      · intro selected
        have selectedParts := by
          simpa only [Bool.and_eq_true] using selected
        rcases selectedParts with
          ⟨immediateSelected, limitsSelected⟩
        have immediate :=
          (chart_observedImmediatelyAfterTerminalBool_eq_true_iff
            owned (.contextualKeyword .comptimeKw)
              siteCursor expressionStart).mp immediateSelected
        rcases List.any_eq_true.mp limitsSelected with
          ⟨limit, _inRange, factsSelected⟩
        have factParts := by
          simpa only [Bool.and_eq_true] using factsSelected
        rcases factParts with
          ⟨nextSelected, greatestSelected⟩
        refine ⟨owned, expressionStart, limit, immediate,
          (nextExact expressionStart limit).mp nextSelected,
          (greatestExact expressionStart limit limit).mp greatestSelected⟩
      · rintro ⟨_owned, otherStart, limit, immediate, nextEvidence,
          greatestEvidence⟩
        rcases immediate with ⟨matched, atSite, atOther⟩
        have otherValue : otherStart.val = siteCursor.val + 1 := by
          have siteValue := congrArg Fin.val atSite
          have afterValue := congrArg Fin.val atOther
          change matched.cursor.val = siteCursor.val at siteValue
          change matched.cursor.val + 1 = otherStart.val at afterValue
          omega
        have startEq : otherStart = expressionStart := by
          apply Fin.ext
          omega
        have canonicalImmediate :
            ∃ matched : MatchedTerminal file tokens
                (.contextualKeyword .comptimeKw),
              matched.cursor.beforeBoundary = siteCursor ∧
                matched.cursor.afterBoundary = expressionStart := by
          refine ⟨matched, atSite, ?_⟩
          simpa only [startEq] using atOther
        have canonicalNext :
            NextSameDepthDelimiter tokens expressionStart limit {
              head := .comma
              tail := [.rightParen, .fatArrow]
            } := by
          simpa only [startEq] using nextEvidence
        have canonicalGreatest :
            GreatestUnguardedEnd file tokens (.rule .expression)
              expressionStart limit limit := by
          simpa only [startEq] using greatestEvidence
        rw [Bool.and_eq_true]
        refine ⟨(chart_observedImmediatelyAfterTerminalBool_eq_true_iff
          owned (.contextualKeyword .comptimeKw)
            siteCursor expressionStart).mpr canonicalImmediate, ?_⟩
        apply List.any_eq_true.mpr
        refine ⟨limit, ?_, ?_⟩
        simp only [List.mem_finRange]
        rw [Bool.and_eq_true]
        exact ⟨(nextExact expressionStart limit).mpr canonicalNext,
          (greatestExact expressionStart limit limit).mpr
            canonicalGreatest⟩

/-- G06 classification is exact under the same two explicit phase contracts. -/
theorem patternComptimeClassifiedObservation_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (nextDelimiter : Chart.PatternDelimiterObservation tokens)
    (greatest : Chart.GreatestEndObservation tokens)
    (key : GuardInstanceKey tokens)
    (isPattern : key.guard = .G06_patternComptime)
    (nextExact : ∀ start limit,
      nextDelimiter start limit = true ↔
        NextSameDepthDelimiter tokens start limit {
          head := .comma
          tail := [.rightParen, .fatArrow]
        })
    (greatestExact : ∀ start upperBound finish,
      greatest (.rule .expression) start upperBound finish = true ↔
        GreatestUnguardedEnd file tokens (.rule .expression)
          start upperBound finish)
    (decision : GuardDecision) :
    Chart.classifyGuardObservation key.guard
        (Chart.patternComptimePositiveObservationBool owned
          nextDelimiter greatest key) false = decision ↔
      GuardEvidence file tokens key decision := by
  apply guardEvidence_iff_classified_observation owned key
    (Chart.patternComptimePositiveObservationBool owned
      nextDelimiter greatest key) false
  · exact patternComptimePositiveObservationBool_exact owned nextDelimiter
      greatest key isPattern nextExact greatestExact
  · intro impossible
    rw [isPattern] at impossible
    contradiction


/-- G02's positive bit is exact once Phase A's arm-header oracle is exact. -/
theorem matchArmHeaderObservationBool_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (header : Chart.MatchArmHeaderObservation tokens)
    (key : GuardInstanceKey tokens)
    (isMatchArm : key.guard = .G02_matchArmBoundary)
    (headerExact : ∀ regionStart cursor,
      header regionStart cursor = true ↔
        ArmHeaderAt file tokens regionStart cursor) :
    Chart.matchArmHeaderObservationBool header key = true ↔
      GuardEvidence file tokens key .positive := by
  rcases key with ⟨guard, contextStart, siteCursor, ordered⟩
  change guard = .G02_matchArmBoundary at isMatchArm
  subst guard
  simp [Chart.matchArmHeaderObservationBool, GuardEvidence, owned,
    headerExact]

/-- G02's full three-way classification is exact under that single Phase-A
header contract; its pipe observation is discharged unconditionally. -/
theorem matchArmClassifiedObservation_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (header : Chart.MatchArmHeaderObservation tokens)
    (key : GuardInstanceKey tokens)
    (isMatchArm : key.guard = .G02_matchArmBoundary)
    (headerExact : ∀ regionStart cursor,
      header regionStart cursor = true ↔
        ArmHeaderAt file tokens regionStart cursor)
    (decision : GuardDecision) :
    Chart.classifyGuardObservation key.guard
        (Chart.matchArmHeaderObservationBool header key)
        (Chart.matchArmPipeObservationBool owned key) = decision ↔
      GuardEvidence file tokens key decision := by
  apply guardEvidence_iff_classified_observation owned key
    (Chart.matchArmHeaderObservationBool header key)
      (Chart.matchArmPipeObservationBool owned key)
  · exact matchArmHeaderObservationBool_exact owned header key
      isMatchArm headerExact
  · intro _
    exact matchArmPipeObservationBool_exact owned key


/-- G08 is exact once nearest-region and raw greatest-expression observations
are exact. -/
theorem terminalExpressionPositiveObservationBool_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (region : Chart.StatementRegionObservation tokens)
    (greatest : Chart.GreatestEndObservation tokens)
    (key : GuardInstanceKey tokens)
    (isTerminalExpression : key.guard = .G08_terminalExpression)
    (regionExact : ∀ regionStart regionEnd,
      region regionStart regionEnd = true ↔
        NearestStatementRegion file tokens regionStart regionEnd)
    (greatestExact : ∀ start upperBound finish,
      greatest (.rule .expression) start upperBound finish = true ↔
        GreatestUnguardedEnd file tokens (.rule .expression)
          start upperBound finish) :
    Chart.terminalExpressionPositiveObservationBool region greatest key =
        true ↔
      GuardEvidence file tokens key .positive := by
  rcases key with ⟨guard, contextStart, siteCursor, ordered⟩
  change guard = .G08_terminalExpression at isTerminalExpression
  subst guard
  simp [Chart.terminalExpressionPositiveObservationBool, GuardEvidence,
    owned, List.any_eq_true, regionExact, greatestExact]

/-- G08 classification is exact under the same two explicit phase contracts. -/
theorem terminalExpressionClassifiedObservation_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (region : Chart.StatementRegionObservation tokens)
    (greatest : Chart.GreatestEndObservation tokens)
    (key : GuardInstanceKey tokens)
    (isTerminalExpression : key.guard = .G08_terminalExpression)
    (regionExact : ∀ regionStart regionEnd,
      region regionStart regionEnd = true ↔
        NearestStatementRegion file tokens regionStart regionEnd)
    (greatestExact : ∀ start upperBound finish,
      greatest (.rule .expression) start upperBound finish = true ↔
        GreatestUnguardedEnd file tokens (.rule .expression)
          start upperBound finish)
    (decision : GuardDecision) :
    Chart.classifyGuardObservation key.guard
        (Chart.terminalExpressionPositiveObservationBool
          region greatest key) false = decision ↔
      GuardEvidence file tokens key decision := by
  apply guardEvidence_iff_classified_observation owned key
    (Chart.terminalExpressionPositiveObservationBool region greatest key)
      false
  · exact terminalExpressionPositiveObservationBool_exact owned region
      greatest key isTerminalExpression regionExact greatestExact
  · intro impossible
    rw [isTerminalExpression] at impossible
    contradiction

/-- At its own upper bound, greatest-end evidence is exactly recognition. -/
theorem greatestUnguardedEnd_at_finish_iff
    {file : WorkspaceFile} {tokens : List Token}
    (symbol : NonterminalSymbol) (start finish : Boundary tokens) :
    GreatestUnguardedEnd file tokens symbol start finish finish ↔
      UnguardedRecognizes file tokens symbol start finish := by
  constructor
  · exact fun greatest => greatest.1
  · intro recognized
    exact ⟨recognized, Nat.le_refl _, fun other _ bounded => bounded⟩

/-- G01's terminal-only observation is exact without a saturation contract. -/
theorem statementIfTerminalObservationBool_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (siteCursor openCursor expressionStart closeCursor : Boundary tokens) :
    Chart.statementIfTerminalObservationBool owned siteCursor openCursor
        expressionStart closeCursor = true ↔
      ∃ afterClose : Boundary tokens,
        (∃ matched : MatchedTerminal file tokens (.hardKeyword .ifKw),
          matched.cursor.beforeBoundary = siteCursor ∧
            matched.cursor.afterBoundary = openCursor) ∧
        (∃ matched : MatchedTerminal file tokens (.symbol .leftParen),
          matched.cursor.beforeBoundary = openCursor ∧
            matched.cursor.afterBoundary = expressionStart) ∧
        (∃ matched : MatchedTerminal file tokens (.symbol .rightParen),
          matched.cursor.beforeBoundary = closeCursor ∧
            matched.cursor.afterBoundary = afterClose) ∧
        (∃ matched : MatchedTerminal file tokens (.symbol .leftBrace),
          matched.cursor.beforeBoundary = afterClose) := by
  unfold Chart.statementIfTerminalObservationBool
  cases boundarySelected :
      Chart.observedBoundaryAt? tokens (closeCursor.val + 1) with
  | none =>
      simp only
      constructor
      · intro impossible
        contradiction
      · rintro ⟨afterClose, _ifEvidence, _openEvidence,
          closeEvidence, _braceEvidence⟩
        rcases closeEvidence with ⟨matched, atClose, atAfter⟩
        have afterValue : afterClose.val = closeCursor.val + 1 := by
          have closeValue := congrArg Fin.val atClose
          have successorValue := congrArg Fin.val atAfter
          change matched.cursor.val = closeCursor.val at closeValue
          change matched.cursor.val + 1 = afterClose.val at successorValue
          omega
        have existsBoundary :
            Chart.observedBoundaryAt? tokens (closeCursor.val + 1) =
              some afterClose :=
          (chart_observedBoundaryAt?_eq_some_iff
            (closeCursor.val + 1) afterClose).mpr afterValue
        rw [boundarySelected] at existsBoundary
        contradiction
  | some afterClose =>
      constructor
      · intro selected
        simp only [Bool.and_eq_true,
          chart_observedImmediatelyAfterTerminalBool_eq_true_iff,
          chart_observedTerminalAtBool_eq_true_iff] at selected
        rcases selected with
          ⟨⟨⟨ifEvidence, openEvidence⟩, closeEvidence⟩, braceEvidence⟩
        exact ⟨afterClose, ifEvidence, openEvidence, closeEvidence,
          braceEvidence⟩
      · rintro ⟨otherAfter, ifEvidence, openEvidence,
          closeEvidence, braceEvidence⟩
        rcases closeEvidence with ⟨matched, atClose, atOtherAfter⟩
        have otherValue : otherAfter.val = closeCursor.val + 1 := by
          have closeValue := congrArg Fin.val atClose
          have afterValue := congrArg Fin.val atOtherAfter
          change matched.cursor.val = closeCursor.val at closeValue
          change matched.cursor.val + 1 = otherAfter.val at afterValue
          omega
        have selectedValue : afterClose.val = closeCursor.val + 1 :=
          (chart_observedBoundaryAt?_eq_some_iff
            (closeCursor.val + 1) afterClose).mp boundarySelected
        have afterEq : otherAfter = afterClose := by
          apply Fin.ext
          omega
        have canonicalClose :
            ∃ matched : MatchedTerminal file tokens (.symbol .rightParen),
              matched.cursor.beforeBoundary = closeCursor ∧
                matched.cursor.afterBoundary = afterClose := by
          refine ⟨matched, atClose, ?_⟩
          simpa only [afterEq] using atOtherAfter
        have canonicalBrace :
            ∃ matched : MatchedTerminal file tokens (.symbol .leftBrace),
              matched.cursor.beforeBoundary = afterClose := by
          simpa only [afterEq] using braceEvidence
        have parts :=
          And.intro (And.intro (And.intro ifEvidence openEvidence)
            canonicalClose) canonicalBrace
        simpa only [Bool.and_eq_true,
          chart_observedImmediatelyAfterTerminalBool_eq_true_iff,
          chart_observedTerminalAtBool_eq_true_iff] using parts



/-- G01 is exact once matching-parenthesis and raw greatest-expression
observations are exact; all terminal and boundary behavior is closed here. -/
theorem statementIfPositiveObservationBool_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (matching : Chart.MatchingParenthesisObservation tokens)
    (greatest : Chart.GreatestEndObservation tokens)
    (key : GuardInstanceKey tokens)
    (isStatementIf : key.guard = .G01_statementIf)
    (matchingExact : ∀ openCursor closeCursor,
      matching openCursor closeCursor = true ↔
        MatchingDelimiter tokens openCursor closeCursor
          .leftParen .rightParen)
    (greatestExact : ∀ start upperBound finish,
      greatest (.rule .expression) start upperBound finish = true ↔
        GreatestUnguardedEnd file tokens (.rule .expression)
          start upperBound finish) :
    Chart.statementIfPositiveObservationBool owned matching greatest key =
        true ↔
      GuardEvidence file tokens key .positive := by
  rcases key with ⟨guard, contextStart, siteCursor, ordered⟩
  change guard = .G01_statementIf at isStatementIf
  subst guard
  unfold Chart.statementIfPositiveObservationBool
  rw [show GuardEvidence file tokens {
      guard := .G01_statementIf
      contextStart := contextStart
      siteCursor := siteCursor
      ordered := ordered
    } .positive =
      (TokensOwnedBy file tokens ∧
        ∃ openCursor expressionStart closeCursor afterClose,
          (∃ matched : MatchedTerminal file tokens (.hardKeyword .ifKw),
            matched.cursor.beforeBoundary = siteCursor ∧
              matched.cursor.afterBoundary = openCursor) ∧
          (∃ matched : MatchedTerminal file tokens (.symbol .leftParen),
            matched.cursor.beforeBoundary = openCursor ∧
              matched.cursor.afterBoundary = expressionStart) ∧
          MatchingDelimiter tokens openCursor closeCursor
            .leftParen .rightParen ∧
          UnguardedRecognizes file tokens (.rule .expression)
            expressionStart closeCursor ∧
          (∃ matched : MatchedTerminal file tokens (.symbol .rightParen),
            matched.cursor.beforeBoundary = closeCursor ∧
              matched.cursor.afterBoundary = afterClose) ∧
          (∃ matched : MatchedTerminal file tokens (.symbol .leftBrace),
            matched.cursor.beforeBoundary = afterClose)) by rfl]
  cases openSelected :
      Chart.observedBoundaryAt? tokens (siteCursor.val + 1) with
  | none =>
      simp only
      constructor
      · intro impossible
        contradiction
      · rintro ⟨_owned, openCursor, expressionStart, closeCursor,
          afterClose, ifEvidence, _openEvidence, _matchingEvidence,
          _recognized, _closeEvidence, _braceEvidence⟩
        rcases ifEvidence with ⟨matched, atSite, atOpen⟩
        have openValue : openCursor.val = siteCursor.val + 1 := by
          have siteValue := congrArg Fin.val atSite
          have afterValue := congrArg Fin.val atOpen
          change matched.cursor.val = siteCursor.val at siteValue
          change matched.cursor.val + 1 = openCursor.val at afterValue
          omega
        have existsBoundary :
            Chart.observedBoundaryAt? tokens (siteCursor.val + 1) =
              some openCursor :=
          (chart_observedBoundaryAt?_eq_some_iff
            (siteCursor.val + 1) openCursor).mpr openValue
        rw [openSelected] at existsBoundary
        contradiction
  | some openCursor =>
      have openValue : openCursor.val = siteCursor.val + 1 :=
        (chart_observedBoundaryAt?_eq_some_iff
          (siteCursor.val + 1) openCursor).mp openSelected
      cases expressionSelected :
          Chart.observedBoundaryAt? tokens (siteCursor.val + 2) with
      | none =>
          simp only
          constructor
          · intro impossible
            contradiction
          · rintro ⟨_owned, otherOpen, expressionStart, closeCursor,
              afterClose, ifEvidence, openEvidence, _matchingEvidence,
              _recognized, _closeEvidence, _braceEvidence⟩
            rcases ifEvidence with ⟨ifMatched, atSite, atOtherOpen⟩
            rcases openEvidence with
              ⟨openMatched, atOpen, atExpression⟩
            have expressionValue :
                expressionStart.val = siteCursor.val + 2 := by
              have siteValue := congrArg Fin.val atSite
              have otherOpenValue := congrArg Fin.val atOtherOpen
              have atOpenValue := congrArg Fin.val atOpen
              have afterValue := congrArg Fin.val atExpression
              change ifMatched.cursor.val = siteCursor.val at siteValue
              change ifMatched.cursor.val + 1 = otherOpen.val at otherOpenValue
              change openMatched.cursor.val = otherOpen.val at atOpenValue
              change openMatched.cursor.val + 1 = expressionStart.val at afterValue
              omega
            have existsBoundary :
                Chart.observedBoundaryAt? tokens (siteCursor.val + 2) =
                  some expressionStart :=
              (chart_observedBoundaryAt?_eq_some_iff
                (siteCursor.val + 2) expressionStart).mpr expressionValue
            rw [expressionSelected] at existsBoundary
            contradiction
      | some expressionStart =>
          have expressionValue :
              expressionStart.val = siteCursor.val + 2 :=
            (chart_observedBoundaryAt?_eq_some_iff
              (siteCursor.val + 2) expressionStart).mp expressionSelected
          constructor
          · intro selected
            rcases List.any_eq_true.mp selected with
              ⟨closeCursor, _inRange, factsSelected⟩
            simp only [Bool.and_eq_true] at factsSelected
            rcases factsSelected with
              ⟨terminalSelected, matchingSelected, greatestSelected⟩
            rcases (statementIfTerminalObservationBool_exact owned
              siteCursor openCursor expressionStart closeCursor).mp
                terminalSelected with
              ⟨afterClose, ifEvidence, openEvidence, closeEvidence,
                braceEvidence⟩
            exact ⟨owned, openCursor, expressionStart, closeCursor,
              afterClose, ifEvidence, openEvidence,
              (matchingExact openCursor closeCursor).mp matchingSelected,
              (greatestUnguardedEnd_at_finish_iff
                (.rule .expression) expressionStart closeCursor).mp
                  ((greatestExact expressionStart closeCursor
                    closeCursor).mp greatestSelected),
              closeEvidence, braceEvidence⟩
          · rintro ⟨_owned, otherOpen, otherStart, closeCursor,
              afterClose, ifEvidence, openEvidence, matchingEvidence,
              recognized, closeEvidence, braceEvidence⟩
            rcases ifEvidence with ⟨ifMatched, atSite, atOtherOpen⟩
            rcases openEvidence with
              ⟨openMatched, atOpen, atOtherStart⟩
            have otherOpenValue : otherOpen.val = siteCursor.val + 1 := by
              have siteValue := congrArg Fin.val atSite
              have afterValue := congrArg Fin.val atOtherOpen
              change ifMatched.cursor.val = siteCursor.val at siteValue
              change ifMatched.cursor.val + 1 = otherOpen.val at afterValue
              omega
            have otherStartValue : otherStart.val = siteCursor.val + 2 := by
              have beforeValue := congrArg Fin.val atOpen
              have afterValue := congrArg Fin.val atOtherStart
              change openMatched.cursor.val = otherOpen.val at beforeValue
              change openMatched.cursor.val + 1 = otherStart.val at afterValue
              omega
            have openEq : otherOpen = openCursor := by
              apply Fin.ext
              omega
            have startEq : otherStart = expressionStart := by
              apply Fin.ext
              omega
            have canonicalIf :
                ∃ matched : MatchedTerminal file tokens
                    (.hardKeyword .ifKw),
                  matched.cursor.beforeBoundary = siteCursor ∧
                    matched.cursor.afterBoundary = openCursor := by
              refine ⟨ifMatched, atSite, ?_⟩
              simpa only [openEq] using atOtherOpen
            have canonicalOpen :
                ∃ matched : MatchedTerminal file tokens
                    (.symbol .leftParen),
                  matched.cursor.beforeBoundary = openCursor ∧
                    matched.cursor.afterBoundary = expressionStart := by
              refine ⟨openMatched, ?_, ?_⟩
              · simpa only [openEq] using atOpen
              · simpa only [startEq] using atOtherStart
            have canonicalMatching :
                MatchingDelimiter tokens openCursor closeCursor
                  .leftParen .rightParen := by
              simpa only [openEq] using matchingEvidence
            have canonicalRecognized :
                UnguardedRecognizes file tokens (.rule .expression)
                  expressionStart closeCursor := by
              simpa only [startEq] using recognized
            apply List.any_eq_true.mpr
            refine ⟨closeCursor, ?_, ?_⟩
            · simp only [List.mem_finRange]
            · simp only [Bool.and_eq_true]
              exact ⟨(statementIfTerminalObservationBool_exact owned
                  siteCursor openCursor expressionStart closeCursor).mpr
                    ⟨afterClose, canonicalIf, canonicalOpen,
                      closeEvidence, braceEvidence⟩,
                (matchingExact openCursor closeCursor).mpr canonicalMatching,
                (greatestExact expressionStart closeCursor closeCursor).mpr
                  ((greatestUnguardedEnd_at_finish_iff
                    (.rule .expression) expressionStart closeCursor).mpr
                      canonicalRecognized)⟩

/-- G01 classification is exact under the same two explicit phase contracts. -/
theorem statementIfClassifiedObservation_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (matching : Chart.MatchingParenthesisObservation tokens)
    (greatest : Chart.GreatestEndObservation tokens)
    (key : GuardInstanceKey tokens)
    (isStatementIf : key.guard = .G01_statementIf)
    (matchingExact : ∀ openCursor closeCursor,
      matching openCursor closeCursor = true ↔
        MatchingDelimiter tokens openCursor closeCursor
          .leftParen .rightParen)
    (greatestExact : ∀ start upperBound finish,
      greatest (.rule .expression) start upperBound finish = true ↔
        GreatestUnguardedEnd file tokens (.rule .expression)
          start upperBound finish)
    (decision : GuardDecision) :
    Chart.classifyGuardObservation key.guard
        (Chart.statementIfPositiveObservationBool
          owned matching greatest key) false = decision ↔
      GuardEvidence file tokens key decision := by
  apply guardEvidence_iff_classified_observation owned key
    (Chart.statementIfPositiveObservationBool owned matching greatest key)
      false
  · exact statementIfPositiveObservationBool_exact owned matching greatest
      key isStatementIf matchingExact greatestExact
  · intro impossible
    rw [isStatementIf] at impossible
    contradiction

/-- Erase a constructive decision to the Boolean observation consumed by
Phase B. -/
private def semanticDecisionBool {proposition : Prop} :
    Decidable proposition → Bool
  | .isTrue _ => true
  | .isFalse _ => false

private theorem semanticDecisionBool_eq_true_iff
    {proposition : Prop} (decision : Decidable proposition) :
    semanticDecisionBool decision = true ↔ proposition := by
  cases decision with
  | isTrue evidence => simp [semanticDecisionBool, evidence]
  | isFalse impossible => simp [semanticDecisionBool, impossible]

/-- The semantic matching-parenthesis decision in Chart's observation shape. -/
def semanticMatchingParenthesisObservation
    (tokens : List Token) : Chart.MatchingParenthesisObservation tokens :=
  fun openCursor closeCursor => semanticDecisionBool
    (matchingDelimiterDecision tokens openCursor closeCursor
      .leftParen .rightParen)

theorem semanticMatchingParenthesisObservation_exact
    (tokens : List Token) (openCursor closeCursor : Boundary tokens) :
    semanticMatchingParenthesisObservation tokens openCursor closeCursor =
        true ↔
      MatchingDelimiter tokens openCursor closeCursor
        .leftParen .rightParen :=
  semanticDecisionBool_eq_true_iff _

/-- The semantic G06 delimiter decision in Chart's observation shape. -/
def semanticPatternDelimiterObservation
    (tokens : List Token) : Chart.PatternDelimiterObservation tokens :=
  fun start finish => semanticDecisionBool
    (nextSameDepthDelimiterDecision tokens start finish {
      head := .comma
      tail := [.rightParen, .fatArrow]
    })

theorem semanticPatternDelimiterObservation_exact
    (tokens : List Token) (start finish : Boundary tokens) :
    semanticPatternDelimiterObservation tokens start finish = true ↔
      NextSameDepthDelimiter tokens start finish {
        head := .comma
        tail := [.rightParen, .fatArrow]
      } :=
  semanticDecisionBool_eq_true_iff _

/-- The semantic greatest-end decision in Chart's observation shape. -/
def semanticGreatestEndObservation
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    Chart.GreatestEndObservation tokens :=
  fun symbol start upperBound finish => semanticDecisionBool
    (greatestUnguardedEndDecision owned symbol start upperBound finish)

theorem semanticGreatestEndObservation_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (symbol : NonterminalSymbol)
    (start upperBound finish : Boundary tokens) :
    semanticGreatestEndObservation owned symbol start upperBound finish =
        true ↔
      GreatestUnguardedEnd file tokens symbol start upperBound finish :=
  semanticDecisionBool_eq_true_iff _

/-- The semantic match-arm header decision in Chart's observation shape. -/
def semanticMatchArmHeaderObservation
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    Chart.MatchArmHeaderObservation tokens :=
  fun regionStart cursor => semanticDecisionBool
    (armHeaderAtDecision owned regionStart cursor)

theorem semanticMatchArmHeaderObservation_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (regionStart cursor : Boundary tokens) :
    semanticMatchArmHeaderObservation owned regionStart cursor = true ↔
      ArmHeaderAt file tokens regionStart cursor :=
  semanticDecisionBool_eq_true_iff _

/-- The semantic nearest-region decision in Chart's observation shape. -/
def semanticStatementRegionObservation
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    Chart.StatementRegionObservation tokens :=
  fun regionStart regionEnd => semanticDecisionBool
    (nearestStatementRegionSemanticDecision owned regionStart regionEnd)

theorem semanticStatementRegionObservation_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (regionStart regionEnd : Boundary tokens) :
    semanticStatementRegionObservation owned regionStart regionEnd = true ↔
      NearestStatementRegion file tokens regionStart regionEnd :=
  semanticDecisionBool_eq_true_iff _

/-- G01 classification using the declarative decision adapters is exact
without further observation hypotheses. -/
theorem semanticStatementIfClassifiedObservation_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (key : GuardInstanceKey tokens)
    (isStatementIf : key.guard = .G01_statementIf)
    (decision : GuardDecision) :
    Chart.classifyGuardObservation key.guard
        (Chart.statementIfPositiveObservationBool owned
          (semanticMatchingParenthesisObservation tokens)
          (semanticGreatestEndObservation owned) key) false = decision ↔
      GuardEvidence file tokens key decision := by
  exact statementIfClassifiedObservation_exact owned
    (semanticMatchingParenthesisObservation tokens)
    (semanticGreatestEndObservation owned) key isStatementIf
    (semanticMatchingParenthesisObservation_exact tokens)
    (fun start upperBound finish =>
      semanticGreatestEndObservation_exact owned (.rule .expression)
        start upperBound finish) decision

/-- G02 classification using the declarative header adapter is exact. -/
theorem semanticMatchArmClassifiedObservation_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (key : GuardInstanceKey tokens)
    (isMatchArm : key.guard = .G02_matchArmBoundary)
    (decision : GuardDecision) :
    Chart.classifyGuardObservation key.guard
        (Chart.matchArmHeaderObservationBool
          (semanticMatchArmHeaderObservation owned) key)
        (Chart.matchArmPipeObservationBool owned key) = decision ↔
      GuardEvidence file tokens key decision := by
  exact matchArmClassifiedObservation_exact owned
    (semanticMatchArmHeaderObservation owned) key isMatchArm
    (semanticMatchArmHeaderObservation_exact owned) decision

/-- G06 classification using the declarative delimiter and greatest-end
adapters is exact. -/
theorem semanticPatternComptimeClassifiedObservation_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (key : GuardInstanceKey tokens)
    (isPattern : key.guard = .G06_patternComptime)
    (decision : GuardDecision) :
    Chart.classifyGuardObservation key.guard
        (Chart.patternComptimePositiveObservationBool owned
          (semanticPatternDelimiterObservation tokens)
          (semanticGreatestEndObservation owned) key) false = decision ↔
      GuardEvidence file tokens key decision := by
  exact patternComptimeClassifiedObservation_exact owned
    (semanticPatternDelimiterObservation tokens)
    (semanticGreatestEndObservation owned) key isPattern
    (semanticPatternDelimiterObservation_exact tokens)
    (fun start upperBound finish =>
      semanticGreatestEndObservation_exact owned (.rule .expression)
        start upperBound finish) decision

/-- G08 classification using the declarative nearest-region and greatest-end
adapters is exact. -/
theorem semanticTerminalExpressionClassifiedObservation_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (key : GuardInstanceKey tokens)
    (isTerminalExpression : key.guard = .G08_terminalExpression)
    (decision : GuardDecision) :
    Chart.classifyGuardObservation key.guard
        (Chart.terminalExpressionPositiveObservationBool
          (semanticStatementRegionObservation owned)
          (semanticGreatestEndObservation owned) key) false = decision ↔
      GuardEvidence file tokens key decision := by
  exact terminalExpressionClassifiedObservation_exact owned
    (semanticStatementRegionObservation owned)
    (semanticGreatestEndObservation owned) key isTerminalExpression
    (semanticStatementRegionObservation_exact owned)
    (fun start upperBound finish =>
      semanticGreatestEndObservation_exact owned (.rule .expression)
        start upperBound finish) decision

/-- G09 classification using the declarative greatest-end adapter is exact. -/
theorem semanticGenericContextClassifiedObservation_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (key : GuardInstanceKey tokens)
    (isGeneric : key.guard = .G09_genericContext)
    (decision : GuardDecision) :
    Chart.classifyGuardObservation key.guard
        (Chart.genericContextPositiveObservationBool owned
          (semanticGreatestEndObservation owned) key) false = decision ↔
      GuardEvidence file tokens key decision := by
  exact genericContextClassifiedObservation_exact owned
    (semanticGreatestEndObservation owned) key isGeneric
    (fun start upperBound finish =>
      semanticGreatestEndObservation_exact owned (.rule .predicateList)
        start upperBound finish) decision


/-- The semantic positive bit for every grammar-owned priority guard. -/
def semanticGuardPositiveObservationBool
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (key : GuardInstanceKey tokens) : Bool :=
  match key.guard with
  | .G01_statementIf =>
      Chart.statementIfPositiveObservationBool owned
        (semanticMatchingParenthesisObservation tokens)
        (semanticGreatestEndObservation owned) key
  | .G02_matchArmBoundary =>
      Chart.matchArmHeaderObservationBool
        (semanticMatchArmHeaderObservation owned) key
  | .G03_parameterComptime | .G04_letComptime |
      .G05_typeComptime | .G07_leadingDotArguments =>
      (Chart.basicGuardPositiveObservation? owned key).getD false
  | .G06_patternComptime =>
      Chart.patternComptimePositiveObservationBool owned
        (semanticPatternDelimiterObservation tokens)
        (semanticGreatestEndObservation owned) key
  | .G08_terminalExpression =>
      Chart.terminalExpressionPositiveObservationBool
        (semanticStatementRegionObservation owned)
        (semanticGreatestEndObservation owned) key
  | .G09_genericContext =>
      Chart.genericContextPositiveObservationBool owned
        (semanticGreatestEndObservation owned) key

/-- The unified semantic positive bit denotes positive evidence exactly. -/
theorem semanticGuardPositiveObservationBool_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (key : GuardInstanceKey tokens) :
    semanticGuardPositiveObservationBool owned key = true ↔
      GuardEvidence file tokens key .positive := by
  cases guardEq : key.guard with
  | G01_statementIf =>
      simpa [semanticGuardPositiveObservationBool, guardEq] using
        statementIfPositiveObservationBool_exact owned
          (semanticMatchingParenthesisObservation tokens)
          (semanticGreatestEndObservation owned) key guardEq
          (semanticMatchingParenthesisObservation_exact tokens)
          (fun start upperBound finish =>
            semanticGreatestEndObservation_exact owned (.rule .expression)
              start upperBound finish)
  | G02_matchArmBoundary =>
      simpa [semanticGuardPositiveObservationBool, guardEq] using
        matchArmHeaderObservationBool_exact owned
          (semanticMatchArmHeaderObservation owned) key guardEq
          (semanticMatchArmHeaderObservation_exact owned)
  | G03_parameterComptime =>
      obtain ⟨observed, selected, exact⟩ :=
        basicGuardPositiveObservation?_exact owned key (Or.inl guardEq)
      simpa [semanticGuardPositiveObservationBool, guardEq, selected] using
        exact
  | G04_letComptime =>
      obtain ⟨observed, selected, exact⟩ :=
        basicGuardPositiveObservation?_exact owned key
          (Or.inr (Or.inl guardEq))
      simpa [semanticGuardPositiveObservationBool, guardEq, selected] using
        exact
  | G05_typeComptime =>
      obtain ⟨observed, selected, exact⟩ :=
        basicGuardPositiveObservation?_exact owned key
          (Or.inr (Or.inr (Or.inl guardEq)))
      simpa [semanticGuardPositiveObservationBool, guardEq, selected] using
        exact
  | G06_patternComptime =>
      simpa [semanticGuardPositiveObservationBool, guardEq] using
        patternComptimePositiveObservationBool_exact owned
          (semanticPatternDelimiterObservation tokens)
          (semanticGreatestEndObservation owned) key guardEq
          (semanticPatternDelimiterObservation_exact tokens)
          (fun start upperBound finish =>
            semanticGreatestEndObservation_exact owned (.rule .expression)
              start upperBound finish)
  | G07_leadingDotArguments =>
      obtain ⟨observed, selected, exact⟩ :=
        basicGuardPositiveObservation?_exact owned key
          (Or.inr (Or.inr (Or.inr guardEq)))
      simpa [semanticGuardPositiveObservationBool, guardEq, selected] using
        exact
  | G08_terminalExpression =>
      simpa [semanticGuardPositiveObservationBool, guardEq] using
        terminalExpressionPositiveObservationBool_exact owned
          (semanticStatementRegionObservation owned)
          (semanticGreatestEndObservation owned) key guardEq
          (semanticStatementRegionObservation_exact owned)
          (fun start upperBound finish =>
            semanticGreatestEndObservation_exact owned (.rule .expression)
              start upperBound finish)
  | G09_genericContext =>
      simpa [semanticGuardPositiveObservationBool, guardEq] using
        genericContextPositiveObservationBool_exact owned
          (semanticGreatestEndObservation owned) key guardEq
          (fun start upperBound finish =>
            semanticGreatestEndObservation_exact owned
              (.rule .predicateList) start upperBound finish)

/-- A public, fully-final semantic guard table in the same normalized shape
as the executable Phase-B worklist. -/
def semanticGuardMemo
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) : GuardMemo tokens :=
  fun key => .final (Chart.classifyGuardObservation key.guard
    (semanticGuardPositiveObservationBool owned key)
    (Chart.matchArmPipeObservationBool owned key))

/-- The unified semantic guard table is declaratively correct. -/
theorem semanticGuardMemo_correct
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    PhaseBCorrect file tokens (semanticGuardMemo owned) := by
  unfold semanticGuardMemo
  exact phaseBCorrect_of_exact_guard_observations owned
    (semanticGuardPositiveObservationBool owned)
    (Chart.matchArmPipeObservationBool owned)
    (semanticGuardPositiveObservationBool_exact owned)
    (fun key _isMatchArm => matchArmPipeObservationBool_exact owned key)

/-- Every entry in the unified semantic guard table is final. -/
theorem semanticGuardMemo_allFinal
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    AllGuardsFinal (semanticGuardMemo owned) := by
  intro key
  exact ⟨Chart.classifyGuardObservation key.guard
    (semanticGuardPositiveObservationBool owned key)
    (Chart.matchArmPipeObservationBool owned key), rfl⟩

/-- Correct fully-final guard tables are extensionally unique. -/
theorem phaseBCorrect_final_memo_unique
    {file : WorkspaceFile} {tokens : List Token}
    {left right : GuardMemo tokens}
    (leftCorrect : PhaseBCorrect file tokens left)
    (leftFinal : AllGuardsFinal left)
    (rightCorrect : PhaseBCorrect file tokens right)
    (rightFinal : AllGuardsFinal right) :
    left = right := by
  funext key
  rcases leftFinal key with ⟨leftDecision, leftState⟩
  rcases rightFinal key with ⟨rightDecision, rightState⟩
  have leftEvidence : GuardEvidence file tokens key leftDecision :=
    (leftCorrect key leftDecision).mp leftState
  have rightEvidence : GuardEvidence file tokens key rightDecision :=
    (rightCorrect key rightDecision).mp rightState
  have decisionEq : leftDecision = rightDecision :=
    GuardEvidence.functional leftEvidence rightEvidence
  subst rightDecision
  exact leftState.trans rightState.symm

/-- For a successful executable guard worklist, declarative correctness is
equivalent to agreement with the unified semantic table. -/
theorem executeObservedGuardWorklist?_correct_iff_semanticMemo
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.GuardWorklistResult tokens)
    (selected : Chart.executeObservedGuardWorklist? file tokens owned =
      some result) :
    PhaseBCorrect file tokens result.memo ↔
      result.memo = semanticGuardMemo owned := by
  constructor
  · intro correct
    exact phaseBCorrect_final_memo_unique correct
      (Chart.executeObservedGuardWorklist?_allGuardsFinal
        file tokens owned result selected)
      (semanticGuardMemo_correct owned)
      (semanticGuardMemo_allFinal owned)
  · intro agreement
    rw [agreement]
    exact semanticGuardMemo_correct owned

/-- Chart's proof-free raw saturation is exactly the least unguarded parser
relation on an owned token stream. -/
theorem saturatedRawItem_iff_unguardedReach
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (item : DottedItem tokens) :
    Chart.SaturatedRawItem tokens item ↔
      UnguardedReach file tokens item := by
  constructor
  · intro member
    exact Chart.saturatedRawItem_induction owned
      (UnguardedReach file tokens)
      (unguardedReachDecision owned)
      (fun production cursor => .seed production cursor)
      (fun waiting predicted reached next =>
        .predict waiting predicted reached next)
      (fun before after cursor terminal value span reached next atCurrent
          terminalAt matched advance =>
        .scan before after cursor terminal value span reached next atCurrent
          terminalAt matched advance)
      (fun waiting finished after waitingReached finishedReached next
          finishedComplete sameCursor advance =>
        .complete waiting finished after waitingReached finishedReached next
          finishedComplete sameCursor advance)
      member
  · intro reached
    induction reached with
    | seed production cursor =>
        exact Chart.saturatedRawItem_seed production cursor
    | predict waiting predicted _ next induction =>
        exact Chart.saturatedRawItem_predict waiting predicted induction next
    | scan before after cursor terminal value span _ next atCurrent
        terminalAt matched advance induction =>
        exact Chart.saturatedRawItem_scan before after cursor terminal value
          span induction next atCurrent terminalAt matched advance
    | complete waiting finished after _ _ next finishedComplete sameCursor
        advance waitingInduction finishedInduction =>
        exact Chart.saturatedRawItem_complete waiting finished after
          waitingInduction finishedInduction next finishedComplete sameCursor
          advance


/-- Recognition over Chart's canonical raw saturation is exactly declarative
unguarded recognition. -/
theorem saturatedRawRecognizesBool_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (symbol : NonterminalSymbol) (start finish : Boundary tokens) :
    Chart.saturatedRawRecognizesBool tokens symbol start finish = true ↔
      UnguardedRecognizes file tokens symbol start finish := by
  rw [Chart.saturatedRawRecognizesBool_eq_true_iff]
  unfold UnguardedRecognizes
  constructor
  · rintro ⟨item, saturated, complete, lhs, origin, current⟩
    exact ⟨item,
      (saturatedRawItem_iff_unguardedReach owned item).mp saturated,
      complete, lhs, origin, current⟩
  · rintro ⟨item, reached, complete, lhs, origin, current⟩
    exact ⟨item,
      (saturatedRawItem_iff_unguardedReach owned item).mpr reached,
      complete, lhs, origin, current⟩

/-- Greatest-end over canonical raw saturation is semantically exact. -/
theorem saturatedRawGreatestEndObservation_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (symbol : NonterminalSymbol)
    (start upperBound finish : Boundary tokens) :
    Chart.saturatedRawGreatestEndObservation tokens symbol start
        upperBound finish = true ↔
      GreatestUnguardedEnd file tokens symbol start upperBound finish := by
  unfold Chart.saturatedRawGreatestEndObservation
  simp only [Bool.and_eq_true, decide_eq_true_iff,
    saturatedRawRecognizesBool_exact owned]
  rw [show GreatestUnguardedEnd file tokens symbol start upperBound finish =
      (UnguardedRecognizes file tokens symbol start finish ∧
        finish.val ≤ upperBound.val ∧
        ∀ other : Boundary tokens,
          UnguardedRecognizes file tokens symbol start other →
          other.val ≤ upperBound.val →
          other.val ≤ finish.val) by rfl]
  constructor
  · rintro ⟨⟨recognized, bounded⟩, maximalSelected⟩
    refine ⟨recognized, bounded, ?_⟩
    intro other otherRecognized otherBounded
    rw [List.all_eq_true] at maximalSelected
    have selected := maximalSelected other (List.mem_finRange _)
    have recognizedSelected :
        Chart.saturatedRawRecognizesBool tokens symbol start other = true :=
      (saturatedRawRecognizesBool_exact owned symbol start other).mpr
        otherRecognized
    simp only [if_pos otherBounded, recognizedSelected, Bool.not_true,
      Bool.false_or, decide_eq_true_iff] at selected
    exact selected
  · rintro ⟨recognized, bounded, maximal⟩
    refine ⟨⟨recognized, bounded⟩, ?_⟩
    rw [List.all_eq_true]
    intro other _member
    by_cases otherBounded : other.val ≤ upperBound.val
    · by_cases recognizedSelected :
          Chart.saturatedRawRecognizesBool tokens symbol start other = true
      · have otherRecognized :=
          (saturatedRawRecognizesBool_exact owned symbol start other).mp
            recognizedSelected
        have otherLe := maximal other otherRecognized otherBounded
        simp [otherBounded, recognizedSelected, otherLe]
      · have recognizedFalse :
            Chart.saturatedRawRecognizesBool tokens symbol start other =
              false := Bool.eq_false_iff.mpr recognizedSelected
        simp [otherBounded, recognizedFalse]
    · simp [otherBounded]

/-- The canonical saturated observer and the constructive semantic observer
compute the same greatest-end bit. -/
theorem saturatedRawGreatestEndObservation_eq_semantic
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (symbol : NonterminalSymbol)
    (start upperBound finish : Boundary tokens) :
    Chart.saturatedRawGreatestEndObservation tokens symbol start
        upperBound finish =
      semanticGreatestEndObservation owned symbol start upperBound finish := by
  apply Bool.eq_iff_iff.mpr
  rw [saturatedRawGreatestEndObservation_exact owned,
    semanticGreatestEndObservation_exact owned]


open Solcore.Workspace
open Grammar

private theorem memoEnablesProduction_iff_enabled
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (productionInstance : ProductionInstanceKey tokens) :
    Chart.MemoEnablesProduction memo productionInstance ↔
      EnabledProductionInstance file tokens memo correct final
        productionInstance := by
  constructor
  · intro enabled guard polarity member
    obtain ⟨guardInstance, decision, anchor, stored, allowed⟩ :=
      enabled guard polarity member
    have sameGuard : guardInstance.guard = guard := anchor.2.1
    let raw : GuardWitnessKey.Raw tokens := {
      productionInstance := productionInstance
      guardInstance := guardInstance
      polarity := polarity
    }
    have valid : GuardWitnessKey.Valid raw := by
      constructor
      · simpa only [raw, sameGuard] using member
      · simpa only [raw, sameGuard] using anchor
    let key : GuardWitnessKey tokens := ⟨raw, valid⟩
    refine ⟨key, rfl, sameGuard, rfl, decision, stored, ?_, allowed⟩
    exact (correct guardInstance decision).mp stored
  · intro enabled guard polarity member
    obtain ⟨key, productionEq, guardEq, polarityEq,
      decision, stored, _evidence, allowed⟩ :=
      enabled guard polarity member
    refine ⟨key.guardInstance, decision, ?_, ?_, ?_⟩
    · have anchor := key.property.2
      change GuardAnchor key.productionInstance
        (key.guardInstance.guard, key.polarity) key.guardInstance at anchor
      change key.productionInstance = productionInstance at productionEq
      change key.guardInstance.guard = guard at guardEq
      change key.polarity = polarity at polarityEq
      rw [productionEq, guardEq, polarityEq] at anchor
      exact anchor
    · exact stored
    · simpa only [polarityEq] using allowed

private theorem operationalContextualReach_sound
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    {item : ContextualItemKey tokens}
    (reached : Chart.OperationalContextualReach file tokens memo item) :
    ContextualReach file tokens memo correct final item := by
  induction reached with
  | root => exact ContextualReach.root
  | predict waiting predicted _ next enabled waitingInduction =>
      exact ContextualReach.predict waiting predicted waitingInduction next
        ((memoEnablesProduction_iff_enabled correct final _).mp enabled)
  | scan before after cursor _ structural beforeInduction =>
      exact ContextualReach.scan before after cursor beforeInduction structural
  | complete waiting finished after shared _ _ structural
      waitingInduction finishedInduction =>
      exact ContextualReach.complete waiting finished after shared
        waitingInduction finishedInduction structural

private theorem operationalContextualEdgeReach_sound
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    {key : ContextualPackedEdgeKey tokens}
    (reached : Chart.OperationalContextualEdgeReach file tokens memo key) :
    ContextualEdgeReach file tokens memo correct final key := by
  rcases reached with ⟨structural, endpoints⟩
  constructor
  · exact structural
  · cases key with
    | scanned before after cursor =>
        exact ⟨operationalContextualReach_sound correct final endpoints.1,
          operationalContextualReach_sound correct final endpoints.2⟩
    | completed waiting finished after shared =>
        exact ⟨operationalContextualReach_sound correct final endpoints.1,
          operationalContextualReach_sound correct final endpoints.2.1,
          operationalContextualReach_sound correct final endpoints.2.2⟩

/-- Conditional semantic soundness of the actual checked Phase-C worklist.
The only remaining Phase-B premise is exact correctness of the returned memo;
finality follows from successful observed execution. -/
theorem executeObservedContextualWorklist?_sound
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result)
    (correct : PhaseBCorrect file tokens result.memo) :
    ∃ final : AllGuardsFinal result.memo,
      (∀ item, item ∈ result.items →
        ContextualReach file tokens result.memo correct final item) ∧
      (∀ edge, edge ∈ result.edges →
        ContextualEdgeReach file tokens result.memo correct final edge.val) := by
  let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
    file tokens owned result selected
  have operational :=
    Chart.executeObservedContextualWorklist?_operational_sound
      file tokens owned result selected
  refine ⟨final, ?_, ?_⟩
  · intro item member
    exact operationalContextualReach_sound correct final
      (operational.1 item member)
  · intro edge member
    exact operationalContextualEdgeReach_sound correct final
      (operational.2 edge member)

/-- Retained ledger consistency upgrades to the declarative completion
backpointer invariant exactly when every declaratively reached edge is
retained.  Proving that edge-completeness premise is the remaining worklist
fairness/correspondence obligation. -/
theorem executeObservedContextualWorklist?_completionBackpointerUnique_of_edge_complete
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result)
    (correct : PhaseBCorrect file tokens result.memo)
    (final : AllGuardsFinal result.memo)
    (edgeComplete : ∀ key,
      ContextualEdgeReach file tokens result.memo correct final key →
        ∃ retained, retained ∈ result.edges ∧ retained.val = key) :
    CompletionBackpointerUnique file tokens result.memo correct final := by
  intro after leftWaiting leftFinished rightWaiting rightFinished
    leftShared rightShared leftReached rightReached
  obtain ⟨left, leftMember, leftKey⟩ := edgeComplete _ leftReached
  obtain ⟨right, rightMember, rightKey⟩ := edgeComplete _ rightReached
  have consistent :=
    Chart.executeObservedContextualWorklist?_retainedBackpointersConsistent
      file tokens owned result selected left leftMember right rightMember
  rw [leftKey, rightKey] at consistent
  exact consistent rfl

open Solcore.Workspace
open Grammar

private theorem contextualReach_operational
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    {item : ContextualItemKey tokens}
    (reached : ContextualReach file tokens memo correct final item) :
    Chart.OperationalContextualReach file tokens memo item := by
  induction reached with
  | root => exact Chart.OperationalContextualReach.root
  | predict waiting predicted _ next enabled waitingInduction =>
      exact Chart.OperationalContextualReach.predict waiting predicted
        waitingInduction next
          ((memoEnablesProduction_iff_enabled correct final _).mpr enabled)
  | scan before after cursor _ structural beforeInduction =>
      exact Chart.OperationalContextualReach.scan before after cursor
        beforeInduction structural
  | complete waiting finished after shared _ _ structural
      waitingInduction finishedInduction =>
      exact Chart.OperationalContextualReach.complete waiting finished after
        shared waitingInduction finishedInduction structural

private theorem contextualEdgeReach_operational
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    {key : ContextualPackedEdgeKey tokens}
    (reached : ContextualEdgeReach file tokens memo correct final key) :
    Chart.OperationalContextualEdgeReach file tokens memo key := by
  rcases reached with ⟨structural, endpoints⟩
  constructor
  · exact structural
  · cases key with
    | scanned before after cursor =>
        exact ⟨contextualReach_operational correct final endpoints.1,
          contextualReach_operational correct final endpoints.2⟩
    | completed waiting finished after shared =>
        exact ⟨contextualReach_operational correct final endpoints.1,
          contextualReach_operational correct final endpoints.2.1,
          contextualReach_operational correct final endpoints.2.2⟩

/-- Declarative completeness factors through one exact operational boundary:
the successful result must be closed under every Phase-C rule.  Queue
fairness/freshness is precisely what remains to establish that premise. -/
theorem executeObservedContextualWorklist?_complete_of_operationalClosure
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result)
    (correct : PhaseBCorrect file tokens result.memo)
    (closed : Chart.OperationalContextualClosure file tokens result.memo
      result.items result.edges) :
    ∃ final : AllGuardsFinal result.memo,
      (∀ item, ContextualReach file tokens result.memo correct final item →
        item ∈ result.items) ∧
      (∀ key, ContextualEdgeReach file tokens result.memo correct final key →
        ∃ retained, retained ∈ result.edges ∧ retained.val = key) := by
  let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
    file tokens owned result selected
  refine ⟨final, ?_, ?_⟩
  · intro item reached
    exact closed.reach_complete
      (contextualReach_operational correct final reached)
  · intro key reached
    exact closed.edge_complete
      (contextualEdgeReach_operational correct final reached)

/-- No unconditional backpointer uniqueness is claimed: retained-ledger
consistency becomes declarative uniqueness only after the same operational
closure/fairness premise supplies edge coverage. -/
theorem executeObservedContextualWorklist?_completionBackpointerUnique_of_operationalClosure
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result)
    (correct : PhaseBCorrect file tokens result.memo)
    (closed : Chart.OperationalContextualClosure file tokens result.memo
      result.items result.edges) :
    ∃ final : AllGuardsFinal result.memo,
      CompletionBackpointerUnique file tokens result.memo correct final := by
  let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
    file tokens owned result selected
  refine ⟨final,
    executeObservedContextualWorklist?_completionBackpointerUnique_of_edge_complete
      file tokens owned result selected correct final ?_⟩
  intro key reached
  exact closed.edge_complete
    (contextualEdgeReach_operational correct final reached)

end Solcore.Surface.Multi


namespace Solcore.Surface.Multi

open Grammar

private def observedCloserToSemantic :
    Chart.ObservedDelimiterCloser → DelimiterCloser
  | .rightParen => .rightParen
  | .rightBracket => .rightBracket
  | .rightBrace => .rightBrace

private def semanticCloserToObserved :
    DelimiterCloser → Chart.ObservedDelimiterCloser
  | .rightParen => .rightParen
  | .rightBracket => .rightBracket
  | .rightBrace => .rightBrace

@[simp] private theorem observedCloser_roundTrip
    (closer : Chart.ObservedDelimiterCloser) :
    semanticCloserToObserved (observedCloserToSemantic closer) = closer := by
  cases closer <;> rfl

@[simp] private theorem semanticCloser_roundTrip
    (closer : DelimiterCloser) :
    observedCloserToSemantic (semanticCloserToObserved closer) = closer := by
  cases closer <;> rfl

private theorem observedStackToSemantic_injective :
    Function.Injective (List.map observedCloserToSemantic) := by
  have roundTrip : ∀ values : List Chart.ObservedDelimiterCloser,
      (values.map observedCloserToSemantic).map
          semanticCloserToObserved = values := by
    intro values
    induction values with
    | nil => rfl
    | cons head tail induction =>
        simp [observedCloser_roundTrip, induction]
  intro left right equal
  calc
    left = (left.map observedCloserToSemantic).map
        semanticCloserToObserved := (roundTrip left).symm
    _ = (right.map observedCloserToSemantic).map
        semanticCloserToObserved := congrArg _ equal
    _ = right := roundTrip right

private theorem observedStackToSemantic_surjective :
    Function.Surjective (List.map observedCloserToSemantic) := by
  intro values
  refine ⟨values.map semanticCloserToObserved, ?_⟩
  simp [List.map_map, Function.comp_def]

set_option linter.unusedSimpArgs false in
private theorem observedDelimiterStep?_eq_some_iff
    (before after : Chart.ObservedDelimiterStack)
    (token : TokenKind) :
    Chart.observedDelimiterStep? before token = some after ↔
      DelimiterStep (before.map observedCloserToSemantic) token
        (after.map observedCloserToSemantic) := by
  have mappedEq : ∀ left right : Chart.ObservedDelimiterStack,
      left.map observedCloserToSemantic =
          right.map observedCloserToSemantic ↔ left = right :=
    fun left right => ⟨fun equal =>
        observedStackToSemantic_injective equal,
      congrArg (List.map observedCloserToSemantic)⟩
  have mappedConsEq : ∀ head tail values,
      values.map observedCloserToSemantic =
          observedCloserToSemantic head ::
            tail.map observedCloserToSemantic ↔
        values = head :: tail := by
    intro head tail values
    simpa only [List.map_cons] using mappedEq values (head :: tail)
  have mappedConsEqRev : ∀ head tail values,
      observedCloserToSemantic head ::
          tail.map observedCloserToSemantic =
        values.map observedCloserToSemantic ↔
      head :: tail = values := by
    intro head tail values
    simpa only [List.map_cons] using mappedEq (head :: tail) values
  have valuesEqCons_iff_consMapEq : ∀ head tail values,
      values = head :: tail ↔
        observedCloserToSemantic head ::
            tail.map observedCloserToSemantic =
          values.map observedCloserToSemantic := by
    intro head tail values
    constructor
    · rintro rfl
      rfl
    · intro equal
      apply observedStackToSemantic_injective
      simpa only [List.map_cons] using equal.symm
  have consEqValues_iff_mapEqCons : ∀ head tail values,
      head :: tail = values ↔
        values.map observedCloserToSemantic =
          observedCloserToSemantic head ::
            tail.map observedCloserToSemantic := by
    intro head tail values
    constructor
    · rintro rfl
      rfl
    · intro equal
      apply observedStackToSemantic_injective
      simpa only [List.map_cons] using equal.symm
  cases token <;>
    simp [Chart.observedDelimiterStep?, DelimiterStep, mappedEq,
      mappedConsEq, mappedConsEqRev, observedCloserToSemantic, eq_comm]
  case symbol symbol =>
    cases symbol <;>
      simp [Chart.observedDelimiterStep?, DelimiterStep, mappedEq,
        mappedConsEq, mappedConsEqRev, observedCloserToSemantic, eq_comm]
    all_goals
      cases before with
      | nil =>
          cases after with
          | nil => simp [Chart.observedDelimiterStep?, DelimiterStep,
              mappedEq, mappedConsEq, mappedConsEqRev,
              valuesEqCons_iff_consMapEq, consEqValues_iff_mapEqCons,
              observedCloserToSemantic, eq_comm]
          | cons afterHead afterTail =>
              cases afterHead <;>
                simp [Chart.observedDelimiterStep?, DelimiterStep,
                  mappedEq, mappedConsEq, mappedConsEqRev,
                  valuesEqCons_iff_consMapEq, consEqValues_iff_mapEqCons,
                  observedCloserToSemantic, eq_comm]
      | cons head tail =>
          cases head <;> cases after with
          | nil => simp [Chart.observedDelimiterStep?, DelimiterStep,
              mappedEq, mappedConsEq, mappedConsEqRev,
              valuesEqCons_iff_consMapEq, consEqValues_iff_mapEqCons,
              eq_comm, observedCloserToSemantic]
          | cons afterHead afterTail =>
              cases afterHead <;>
                simp [Chart.observedDelimiterStep?, DelimiterStep,
                  mappedEq, mappedConsEq, mappedConsEqRev,
                  valuesEqCons_iff_consMapEq, consEqValues_iff_mapEqCons,
                  eq_comm, observedCloserToSemantic]

private theorem delimiterRun_uncons
    {tokens : List Token} {before after : DelimiterStack}
    {start finish : Boundary tokens}
    (different : start ≠ finish)
    (run : DelimiterRun tokens before start finish after) :
    ∃ next : DelimiterStack,
    ∃ cursor : TerminalCursor tokens,
    ∃ token : Token,
      cursor.beforeBoundary = start ∧
        tokens[cursor.val]? = some token ∧
        DelimiterStep before token.payload next ∧
        DelimiterRun tokens next cursor.afterBoundary finish after := by
  cases run with
  | nil => exact False.elim (different rfl)
  | cons before next after cursor start finish token atStart lookup step rest =>
      exact ⟨next, cursor, token, atStart, lookup, step, rest⟩

private theorem observedDelimiterRunFrom?_eq_some_iff
    {tokens : List Token}
    (fuel cursor : Nat)
    (before after : Chart.ObservedDelimiterStack)
    (start finish : Boundary tokens)
    (startEq : start.val = cursor)
    (finishEq : finish.val = cursor + fuel) :
    Chart.observedDelimiterRunFrom? tokens fuel cursor before =
        some after ↔
      DelimiterRun tokens (before.map observedCloserToSemantic)
        start finish (after.map observedCloserToSemantic) := by
  induction fuel generalizing cursor before after start finish with
  | zero =>
      have finishStart : finish = start := by
        apply Fin.ext
        omega
      subst finish
      constructor
      · intro computed
        have afterEq : after = before := by
          simpa only [Chart.observedDelimiterRunFrom?,
            Option.some.injEq] using computed.symm
        have mappedAfterEq :=
          congrArg (List.map observedCloserToSemantic) afterEq
        exact Eq.mpr (congrArg (fun final =>
          DelimiterRun tokens (before.map observedCloserToSemantic)
            start start final) mappedAfterEq) (.nil _ _)
      · intro run
        have mappedEq := delimiterRun_functional run
          (.nil (before.map observedCloserToSemantic) start)
        have afterEq : after = before :=
          observedStackToSemantic_injective mappedEq
        change some before = some after
        exact congrArg some afterEq.symm
  | succ fuel induction =>
      constructor
      · intro computed
        unfold Chart.observedDelimiterRunFrom? at computed
        split at computed
        case isFalse => contradiction
        case isTrue inRange =>
          generalize stepEq : Chart.observedDelimiterStep?
            before tokens[cursor].payload = stepResult at computed
          cases stepResult with
          | none => contradiction
          | some next =>
              let terminalCursor : TerminalCursor tokens :=
                ⟨cursor, Nat.lt_trans inRange (Nat.lt_succ_self _)⟩
              let nextStart : Boundary tokens :=
                terminalCursor.afterBoundary
              have atStart : terminalCursor.beforeBoundary = start := by
                apply Fin.ext
                exact startEq.symm
              have nextStartEq : nextStart.val = cursor + 1 := rfl
              have nextFinishEq : finish.val = cursor + 1 + fuel := by
                omega
              have rest := (induction (cursor + 1) next after
                nextStart finish nextStartEq nextFinishEq).mp computed
              exact .cons _ _ _ terminalCursor start finish
                tokens[cursor] atStart
                (List.getElem?_eq_getElem inRange)
                ((observedDelimiterStep?_eq_some_iff _ _ _).mp stepEq)
                rest
      · intro run
        have different : start ≠ finish := by
          intro equal
          have values := congrArg Fin.val equal
          omega
        obtain ⟨relationAfter, terminalCursor, token, atStart,
          lookup, step, rest⟩ := delimiterRun_uncons different run
        have cursorEq : terminalCursor.val = cursor := by
          have rawAtStart := congrArg Fin.val atStart
          change terminalCursor.val = start.val at rawAtStart
          omega
        have inRange : cursor < tokens.length := by
          by_cases candidate : cursor < tokens.length
          · exact candidate
          · have outOfRange : tokens.length ≤ terminalCursor.val := by
              omega
            rw [List.getElem?_eq_none outOfRange] at lookup
            contradiction
        have tokenEq : tokens[cursor] = token := by
          have canonical := List.getElem?_eq_getElem inRange
          rw [cursorEq] at lookup
          exact Option.some.inj (canonical.symm.trans lookup)
        obtain ⟨nextObserved, rfl⟩ :=
          observedStackToSemantic_surjective relationAfter
        unfold Chart.observedDelimiterRunFrom?
        rw [dif_pos inRange]
        rw [(observedDelimiterStep?_eq_some_iff
          before nextObserved _).mpr (tokenEq ▸ step)]
        have nextStartEq :
            terminalCursor.afterBoundary.val = cursor + 1 := by
          change terminalCursor.val + 1 = cursor + 1
          omega
        have nextFinishEq : finish.val = cursor + 1 + fuel := by
          omega
        exact (induction (cursor + 1) nextObserved after
          terminalCursor.afterBoundary finish nextStartEq
          nextFinishEq).mpr rest

private theorem delimiterRun_ordered_for_observed
    {tokens : List Token} {before after : DelimiterStack}
    {start finish : Boundary tokens}
    (run : DelimiterRun tokens before start finish after) :
    start.val ≤ finish.val := by
  induction run with
  | nil => exact Nat.le_refl _
  | cons before after finish cursor start endCursor token atStart lookup
      step rest induction =>
      have atStartValue := congrArg Fin.val atStart
      have beforeValue : cursor.beforeBoundary.val = cursor.val := rfl
      have afterValue : cursor.afterBoundary.val = cursor.val + 1 := rfl
      omega

private theorem observedDelimiterRun?_eq_some_iff
    (tokens : List Token)
    (before after : Chart.ObservedDelimiterStack)
    (start finish : Boundary tokens) :
    Chart.observedDelimiterRun? tokens before start finish = some after ↔
      DelimiterRun tokens (before.map observedCloserToSemantic)
        start finish (after.map observedCloserToSemantic) := by
  unfold Chart.observedDelimiterRun?
  split
  case isFalse notOrdered =>
    constructor
    · intro impossible
      contradiction
    · intro run
      exact False.elim (notOrdered (delimiterRun_ordered_for_observed run))
  case isTrue ordered =>
    exact observedDelimiterRunFrom?_eq_some_iff
      (finish.val - start.val) start.val before after start finish rfl
        (by omega)

theorem observedSameDelimiterDepthBool_exact
    (tokens : List Token) (start finish : Boundary tokens) :
    Chart.observedSameDelimiterDepthBool tokens start finish = true ↔
      SameDelimiterDepth tokens start finish := by
  unfold Chart.observedSameDelimiterDepthBool SameDelimiterDepth
  rw [decide_eq_true_iff,
    observedDelimiterRun?_eq_some_iff tokens [] [] start finish]
  rfl

end Solcore.Surface.Multi

namespace Solcore.Surface.Multi

open Grammar

private theorem observedSymbolAllowedBool_exact
    (symbol : Symbol) (allowed : NonemptyList Symbol) :
    Chart.observedSymbolAllowedBool symbol allowed = true ↔
      symbol = allowed.head ∨ symbol ∈ allowed.tail := by
  simp [Chart.observedSymbolAllowedBool, List.any_eq_true]

private theorem observedAllowedSymbolAtBool_exact
    (tokens : List Token) (cursor : Boundary tokens)
    (allowed : NonemptyList Symbol) :
    Chart.observedAllowedSymbolAtBool cursor allowed = true ↔
      ∃ symbol : Symbol,
        (symbol = allowed.head ∨ symbol ∈ allowed.tail) ∧
        ∃ terminalCursor : TerminalCursor tokens,
        ∃ token : Token,
          terminalCursor.beforeBoundary = cursor ∧
            tokens[terminalCursor.val]? = some token ∧
            token.payload = .symbol symbol := by
  constructor
  · intro accepted
    unfold Chart.observedAllowedSymbolAtBool at accepted
    split at accepted
    case isFalse => simp at accepted
    case isTrue inRange =>
      generalize payloadEq : tokens[cursor.val].payload = payload at accepted
      cases payload <;> simp at accepted
      case symbol symbol =>
        have allowedMember :=
          (observedSymbolAllowedBool_exact symbol allowed).mp accepted
        let terminalCursor : TerminalCursor tokens :=
          ⟨cursor.val, Nat.lt_trans inRange (Nat.lt_succ_self _)⟩
        exact ⟨symbol, allowedMember, terminalCursor,
          tokens[cursor.val], by apply Fin.ext; rfl,
          List.getElem?_eq_getElem inRange, payloadEq⟩
  · rintro ⟨symbol, allowedMember, terminalCursor, token,
      atCursor, lookup, payload⟩
    have cursorEq : terminalCursor.val = cursor.val :=
      congrArg Fin.val atCursor
    have inRange : cursor.val < tokens.length := by
      by_cases candidate : cursor.val < tokens.length
      · exact candidate
      · have outOfRange : tokens.length ≤ terminalCursor.val := by
          omega
        rw [List.getElem?_eq_none outOfRange] at lookup
        contradiction
    have tokenEq : tokens[cursor.val] = token := by
      have canonical := List.getElem?_eq_getElem inRange
      rw [cursorEq] at lookup
      exact Option.some.inj (canonical.symm.trans lookup)
    have payloadAt : tokens[cursor.val].payload = .symbol symbol :=
      tokenEq ▸ payload
    unfold Chart.observedAllowedSymbolAtBool
    rw [dif_pos inRange, payloadAt]
    exact (observedSymbolAllowedBool_exact symbol allowed).mpr allowedMember

/-- The public G06 delimiter bit selects exactly the first allowed delimiter
at the starting depth. -/
theorem observedPatternDelimiterBool_exact
    (tokens : List Token) (start cursor : Boundary tokens) :
    Chart.observedPatternDelimiterBool tokens start cursor = true ↔
      NextSameDepthDelimiter tokens start cursor {
        head := .comma
        tail := [.rightParen, .fatArrow]
      } := by
  let allowed : NonemptyList Symbol := {
    head := .comma
    tail := [.rightParen, .fatArrow]
  }
  change Chart.observedPatternDelimiterBool tokens start cursor = true ↔
    NextSameDepthDelimiter tokens start cursor allowed
  unfold Chart.observedPatternDelimiterBool NextSameDepthDelimiter
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨⟨sameDepth, allowedAtCursor⟩, earliest⟩
    refine ⟨
      (observedSameDelimiterDepthBool_exact tokens start cursor).mp
        sameDepth,
      (observedAllowedSymbolAtBool_exact tokens cursor allowed).mp
        allowedAtCursor,
      ?_⟩
    intro earlier startLe earlierLt earlierDepth earlierAllowed
    rw [List.all_eq_true] at earliest
    have selected := earliest earlier (List.mem_finRange _)
    have depthTrue :=
      (observedSameDelimiterDepthBool_exact tokens start earlier).mpr
        earlierDepth
    have allowedTrue :=
      (observedAllowedSymbolAtBool_exact tokens earlier allowed).mpr
        earlierAllowed
    have allowedTrueAtEarlier : Chart.observedAllowedSymbolAtBool earlier {
        head := .comma
        tail := [.rightParen, .fatArrow]
      } = true := by
      simpa [allowed] using allowedTrue
    rw [allowedTrueAtEarlier] at selected
    simp [startLe, earlierLt, depthTrue] at selected
  · rintro ⟨sameDepth, allowedAtCursor, earliest⟩
    refine ⟨⟨
      (observedSameDelimiterDepthBool_exact tokens start cursor).mpr
        sameDepth,
      (observedAllowedSymbolAtBool_exact tokens cursor allowed).mpr
        allowedAtCursor⟩, ?_⟩
    rw [List.all_eq_true]
    intro earlier _member
    by_cases startLe : start.val ≤ earlier.val
    · by_cases earlierLt : earlier.val < cursor.val
      · by_cases depth : SameDelimiterDepth tokens start earlier
        · have notAllowed := earliest earlier startLe earlierLt depth
          have depthTrue :=
            (observedSameDelimiterDepthBool_exact tokens start earlier).mpr
              depth
          have allowedFalse :
              Chart.observedAllowedSymbolAtBool earlier allowed = false := by
            apply Bool.eq_false_iff.mpr
            intro allowedTrue
            exact notAllowed
              ((observedAllowedSymbolAtBool_exact tokens earlier allowed).mp
                allowedTrue)
          have allowedFalseAtEarlier :
              Chart.observedAllowedSymbolAtBool earlier {
                head := .comma
                tail := [.rightParen, .fatArrow]
              } = false := by
            simpa [allowed] using allowedFalse
          simpa [startLe, earlierLt, depthTrue] using allowedFalseAtEarlier
        · have depthFalse :
              Chart.observedSameDelimiterDepthBool tokens start earlier =
                false := by
            exact Bool.eq_false_iff.mpr fun depthTrue => depth
              ((observedSameDelimiterDepthBool_exact
                tokens start earlier).mp depthTrue)
          simp [startLe, earlierLt, depthFalse]
      · simp [startLe, earlierLt]
    · simp [startLe]

/-- The canonical U01 G06 bit agrees with the constructive semantic oracle. -/
theorem rawPatternDelimiterObservation_eq_semantic
    (tokens : List Token) (start cursor : Boundary tokens) :
    Chart.rawPatternDelimiterObservation tokens start cursor =
      semanticPatternDelimiterObservation tokens start cursor := by
  rw [Chart.rawPatternDelimiterObservation_eq_observed]
  apply Bool.eq_iff_iff.mpr
  rw [observedPatternDelimiterBool_exact,
    semanticPatternDelimiterObservation_exact]

end Solcore.Surface.Multi

namespace Solcore.Surface.Multi

open Grammar

private def observedNonemptyToSemantic
    (values : NonemptyList Chart.ObservedDelimiterCloser) :
    NonemptyList DelimiterCloser := {
  head := observedCloserToSemantic values.head
  tail := values.tail.map observedCloserToSemantic
}

private def nonemptyValues {alpha : Type}
    (values : NonemptyList alpha) : List alpha :=
  values.head :: values.tail

private theorem nonemptyValues_injective {alpha : Type} :
    Function.Injective (@nonemptyValues alpha) := by
  rintro ⟨leftHead, leftTail⟩ ⟨rightHead, rightTail⟩ equal
  simp only [nonemptyValues] at equal
  cases equal
  rfl

private theorem observedNonemptyToSemantic_injective :
    Function.Injective observedNonemptyToSemantic := by
  intro left right equal
  apply nonemptyValues_injective
  apply observedStackToSemantic_injective
  simpa [observedNonemptyToSemantic, nonemptyValues] using
    congrArg nonemptyValues equal

private theorem observedNonemptyToSemantic_surjective :
    Function.Surjective observedNonemptyToSemantic := by
  rintro ⟨head, tail⟩
  refine ⟨⟨semanticCloserToObserved head,
    tail.map semanticCloserToObserved⟩, ?_⟩
  simp [observedNonemptyToSemantic, List.map_map, Function.comp_def]

private theorem observedProtectedDelimiterStep?_eq_some_iff_base
    (before after : NonemptyList Chart.ObservedDelimiterCloser)
    (token : TokenKind) :
    Chart.observedProtectedDelimiterStep? (nonemptyValues before) token =
        some (nonemptyValues after) ↔
      Chart.observedDelimiterStep? (nonemptyValues before) token =
        some (nonemptyValues after) := by
  cases before with
  | mk beforeHead beforeTail =>
      cases after with
      | mk afterHead afterTail =>
          simp only [nonemptyValues]
          unfold Chart.observedProtectedDelimiterStep?
          generalize stepEq : Chart.observedDelimiterStep?
            (beforeHead :: beforeTail) token = result
          cases result with
          | none => simp
          | some stack =>
              cases stack with
              | nil => simp
              | cons head tail => simp

private theorem observedProtectedDelimiterStep?_eq_some_iff
    (before after : NonemptyList Chart.ObservedDelimiterCloser)
    (token : TokenKind) :
    Chart.observedProtectedDelimiterStep? (nonemptyValues before) token =
        some (nonemptyValues after) ↔
      DelimiterStep
        (nonemptyValues (observedNonemptyToSemantic before)) token
        (nonemptyValues (observedNonemptyToSemantic after)) := by
  rw [observedProtectedDelimiterStep?_eq_some_iff_base,
    observedDelimiterStep?_eq_some_iff]
  rfl

private theorem observedProtectedDelimiterStep?_some_ne_nil
    (before : NonemptyList Chart.ObservedDelimiterCloser)
    (token : TokenKind) (after : Chart.ObservedDelimiterStack)
    (selected : Chart.observedProtectedDelimiterStep?
      (nonemptyValues before) token =
      some after) : after ≠ [] := by
  intro afterNil
  subst after
  cases before with
  | mk head tail =>
      simp only [nonemptyValues] at selected
      unfold Chart.observedProtectedDelimiterStep? at selected
      generalize stepEq : Chart.observedDelimiterStep?
        (head :: tail) token = result at selected
      cases result with
      | none => simp at selected
      | some stack =>
          cases stack <;> simp at selected

private theorem protectedDelimiterRun_uncons_for_observed
    {tokens : List Token}
    {before after : NonemptyList DelimiterCloser}
    {start finish : Boundary tokens}
    (different : start ≠ finish)
    (run : ProtectedDelimiterRun tokens before start finish after) :
    ∃ next : NonemptyList DelimiterCloser,
    ∃ cursor : TerminalCursor tokens,
    ∃ token : Token,
      cursor.beforeBoundary = start ∧
        tokens[cursor.val]? = some token ∧
        DelimiterStep (nonemptyValues before) token.payload
          (nonemptyValues next) ∧
        ProtectedDelimiterRun tokens next cursor.afterBoundary
          finish after := by
  cases run with
  | nil => exact False.elim (different rfl)
  | cons before next after cursor start finish token atStart lookup
      step rest =>
      exact ⟨next, cursor, token, atStart, lookup, step, rest⟩

private theorem protectedDelimiterRun_ordered_for_observed
    {tokens : List Token}
    {before after : NonemptyList DelimiterCloser}
    {start finish : Boundary tokens}
    (run : ProtectedDelimiterRun tokens before start finish after) :
    start.val ≤ finish.val := by
  induction run with
  | nil => exact Nat.le_refl _
  | cons before after finish cursor start endCursor token atStart lookup
      step rest induction =>
      have atStartValue := congrArg Fin.val atStart
      have beforeValue : cursor.beforeBoundary.val = cursor.val := rfl
      have afterValue : cursor.afterBoundary.val = cursor.val + 1 := rfl
      omega

private theorem protectedDelimiterRun_same_for_observed
    {tokens : List Token}
    {before after : NonemptyList DelimiterCloser}
    {cursor : Boundary tokens}
    (run : ProtectedDelimiterRun tokens before cursor cursor after) :
    after = before := by
  cases run with
  | nil => rfl
  | cons before next after terminalCursor start finish token atStart lookup
      step rest =>
      have restOrdered := protectedDelimiterRun_ordered_for_observed rest
      have atStartValue := congrArg Fin.val atStart
      have beforeValue :
          terminalCursor.beforeBoundary.val = terminalCursor.val := rfl
      have afterValue :
          terminalCursor.afterBoundary.val = terminalCursor.val + 1 := rfl
      omega

private theorem observedProtectedDelimiterRunFrom?_eq_some_iff
    {tokens : List Token}
    (fuel cursor : Nat)
    (before after : NonemptyList Chart.ObservedDelimiterCloser)
    (start finish : Boundary tokens)
    (startEq : start.val = cursor)
    (finishEq : finish.val = cursor + fuel) :
    Chart.observedProtectedDelimiterRunFrom? tokens fuel cursor
        (nonemptyValues before) = some (nonemptyValues after) ↔
      ProtectedDelimiterRun tokens (observedNonemptyToSemantic before)
        start finish (observedNonemptyToSemantic after) := by
  induction fuel generalizing cursor before after start finish with
  | zero =>
      have finishStart : finish = start := by
        apply Fin.ext
        omega
      subst finish
      constructor
      · intro computed
        have afterEq : after = before := by
          apply nonemptyValues_injective
          simpa only [nonemptyValues,
            Chart.observedProtectedDelimiterRunFrom?,
            Option.some.injEq] using computed.symm
        subst after
        exact .nil _ _
      · intro run
        have mappedEq : observedNonemptyToSemantic after =
            observedNonemptyToSemantic before :=
          protectedDelimiterRun_same_for_observed run
        have afterEq : after = before :=
          observedNonemptyToSemantic_injective mappedEq
        subst after
        rfl
  | succ fuel induction =>
      constructor
      · intro computed
        unfold Chart.observedProtectedDelimiterRunFrom? at computed
        split at computed
        case isFalse => contradiction
        case isTrue inRange =>
          generalize stepEq : Chart.observedProtectedDelimiterStep?
            (nonemptyValues before) tokens[cursor].payload =
              stepResult at computed
          cases stepResult with
          | none => contradiction
          | some nextStack =>
              have nextNonempty :=
                observedProtectedDelimiterStep?_some_ne_nil before
                  tokens[cursor].payload nextStack stepEq
              cases nextStack with
              | nil => contradiction
              | cons nextHead nextTail =>
                  let next : NonemptyList Chart.ObservedDelimiterCloser :=
                    ⟨nextHead, nextTail⟩
                  let terminalCursor : TerminalCursor tokens :=
                    ⟨cursor, Nat.lt_trans inRange (Nat.lt_succ_self _)⟩
                  let nextStart : Boundary tokens :=
                    terminalCursor.afterBoundary
                  have atStart : terminalCursor.beforeBoundary = start := by
                    apply Fin.ext
                    exact startEq.symm
                  have nextStartEq : nextStart.val = cursor + 1 := rfl
                  have nextFinishEq : finish.val = cursor + 1 + fuel := by
                    omega
                  have rest := (induction (cursor + 1) next after
                    nextStart finish nextStartEq nextFinishEq).mp computed
                  exact .cons _ _ _ terminalCursor start finish
                    tokens[cursor] atStart
                    (List.getElem?_eq_getElem inRange)
                    ((observedProtectedDelimiterStep?_eq_some_iff
                      before next _).mp stepEq)
                    rest
      · intro run
        have different : start ≠ finish := by
          intro equal
          have values := congrArg Fin.val equal
          omega
        obtain ⟨relationAfter, terminalCursor, token, atStart,
          lookup, step, rest⟩ :=
          protectedDelimiterRun_uncons_for_observed different run
        obtain ⟨nextObserved, relationAfterEq⟩ :=
          observedNonemptyToSemantic_surjective relationAfter
        subst relationAfter
        have cursorEq : terminalCursor.val = cursor := by
          have rawAtStart := congrArg Fin.val atStart
          change terminalCursor.val = start.val at rawAtStart
          omega
        have inRange : cursor < tokens.length := by
          by_cases candidate : cursor < tokens.length
          · exact candidate
          · have outOfRange : tokens.length ≤ terminalCursor.val := by
              omega
            rw [List.getElem?_eq_none outOfRange] at lookup
            contradiction
        have tokenEq : tokens[cursor] = token := by
          have canonical := List.getElem?_eq_getElem inRange
          rw [cursorEq] at lookup
          exact Option.some.inj (canonical.symm.trans lookup)
        unfold Chart.observedProtectedDelimiterRunFrom?
        rw [dif_pos inRange]
        rw [(observedProtectedDelimiterStep?_eq_some_iff
          before nextObserved _).mpr (tokenEq ▸ step)]
        have nextStartEq :
            terminalCursor.afterBoundary.val = cursor + 1 := by
          change terminalCursor.val + 1 = cursor + 1
          omega
        have nextFinishEq : finish.val = cursor + 1 + fuel := by
          omega
        exact (induction (cursor + 1) nextObserved after
          terminalCursor.afterBoundary finish nextStartEq
          nextFinishEq).mpr rest

private theorem observedProtectedDelimiterRun?_eq_some_iff
    (tokens : List Token)
    (before after : NonemptyList Chart.ObservedDelimiterCloser)
    (start finish : Boundary tokens) :
    Chart.observedProtectedDelimiterRun? tokens (nonemptyValues before)
        start finish = some (nonemptyValues after) ↔
      ProtectedDelimiterRun tokens (observedNonemptyToSemantic before)
        start finish (observedNonemptyToSemantic after) := by
  unfold Chart.observedProtectedDelimiterRun?
  split
  case isFalse notOrdered =>
    constructor
    · intro impossible
      contradiction
    · intro run
      exact False.elim
        (notOrdered (protectedDelimiterRun_ordered_for_observed run))
  case isTrue ordered =>
    exact observedProtectedDelimiterRunFrom?_eq_some_iff
      (finish.val - start.val) start.val before after start finish rfl
        (by omega)

/-- The protected singleton-parenthesis executor is exactly its declarative
run, so G01 cannot consume the closer that it is meant to match. -/
theorem observedProtectedRightParenRun_exact
    (tokens : List Token) (start finish : Boundary tokens) :
    Chart.observedProtectedDelimiterRun? tokens [.rightParen]
        start finish = some [.rightParen] ↔
      ProtectedDelimiterRun tokens
        { head := .rightParen, tail := [] } start finish
        { head := .rightParen, tail := [] } := by
  simpa [nonemptyValues, observedNonemptyToSemantic,
    observedCloserToSemantic] using
    observedProtectedDelimiterRun?_eq_some_iff tokens
      { head := Chart.ObservedDelimiterCloser.rightParen, tail := [] }
      { head := Chart.ObservedDelimiterCloser.rightParen, tail := [] }
      start finish

end Solcore.Surface.Multi

namespace Solcore.Surface.Multi

open Grammar

private theorem observedRawSymbolAtBool_exact
    (tokens : List Token) (cursor : Boundary tokens) (symbol : Symbol) :
    Chart.observedRawSymbolAtBool cursor symbol = true ↔
      ∃ terminalCursor : TerminalCursor tokens,
      ∃ token : Token,
        terminalCursor.beforeBoundary = cursor ∧
          tokens[terminalCursor.val]? = some token ∧
          token.payload = .symbol symbol := by
  constructor
  · intro accepted
    unfold Chart.observedRawSymbolAtBool at accepted
    split at accepted
    case isFalse => simp at accepted
    case isTrue inRange =>
      have payload := of_decide_eq_true accepted
      let terminalCursor : TerminalCursor tokens :=
        ⟨cursor.val, Nat.lt_trans inRange (Nat.lt_succ_self _)⟩
      refine ⟨terminalCursor, tokens[cursor.val], ?_, ?_, payload⟩
      · apply Fin.ext
        rfl
      · exact List.getElem?_eq_getElem inRange
  · rintro ⟨terminalCursor, token, atCursor, lookup, payload⟩
    have cursorEq : terminalCursor.val = cursor.val :=
      congrArg Fin.val atCursor
    have inRange : cursor.val < tokens.length := by
      by_cases candidate : cursor.val < tokens.length
      · exact candidate
      · have outOfRange : tokens.length ≤ terminalCursor.val := by
          omega
        rw [List.getElem?_eq_none outOfRange] at lookup
        contradiction
    have tokenEq : tokens[cursor.val] = token := by
      have canonical := List.getElem?_eq_getElem inRange
      rw [cursorEq] at lookup
      exact Option.some.inj (canonical.symm.trans lookup)
    unfold Chart.observedRawSymbolAtBool
    rw [dif_pos inRange]
    exact decide_eq_true (tokenEq ▸ payload)

/-- The public G01 parenthesis bit recognizes exactly one protected matching
pair in the declarative parser semantics. -/
theorem observedMatchingParenthesisBool_exact
    (tokens : List Token) (openCursor closeCursor : Boundary tokens) :
    Chart.observedMatchingParenthesisBool tokens openCursor closeCursor =
        true ↔
      MatchingDelimiter tokens openCursor closeCursor
        .leftParen .rightParen := by
  unfold Chart.observedMatchingParenthesisBool MatchingDelimiter
  simp only [Bool.and_eq_true, true_and]
  constructor
  · rintro ⟨⟨openAccepted, closeAccepted⟩, runAccepted⟩
    generalize boundaryEq : Chart.observedBoundaryAt? tokens
      (openCursor.val + 1) = result at runAccepted
    cases result with
    | none => simp at runAccepted
    | some interiorStart =>
        have coordinateEq : interiorStart.val = openCursor.val + 1 :=
          (chart_observedBoundaryAt?_eq_some_iff
            (openCursor.val + 1) interiorStart).mp boundaryEq
        rcases (observedRawSymbolAtBool_exact tokens openCursor
          .leftParen).mp openAccepted with
          ⟨terminalCursor, token, atOpen, lookup, payload⟩
        have atInterior : terminalCursor.afterBoundary = interiorStart := by
          apply Fin.ext
          have atOpenValue := congrArg Fin.val atOpen
          change terminalCursor.val = openCursor.val at atOpenValue
          change terminalCursor.val + 1 = interiorStart.val
          omega
        refine ⟨interiorStart,
          ⟨terminalCursor, token, atOpen, atInterior, lookup, payload⟩,
          (observedRawSymbolAtBool_exact tokens closeCursor
            .rightParen).mp closeAccepted,
          ?_⟩
        exact (observedProtectedRightParenRun_exact tokens
          interiorStart closeCursor).mp (of_decide_eq_true runAccepted)
  · rintro ⟨interiorStart,
      ⟨terminalCursor, token, atOpen, atInterior, lookup, payload⟩,
      closeObserved, run⟩
    have coordinateEq : interiorStart.val = openCursor.val + 1 := by
      have atOpenValue := congrArg Fin.val atOpen
      have atInteriorValue := congrArg Fin.val atInterior
      change terminalCursor.val = openCursor.val at atOpenValue
      change terminalCursor.val + 1 = interiorStart.val at atInteriorValue
      omega
    have boundaryEq : Chart.observedBoundaryAt? tokens
        (openCursor.val + 1) = some interiorStart :=
      (chart_observedBoundaryAt?_eq_some_iff
        (openCursor.val + 1) interiorStart).mpr coordinateEq
    refine ⟨⟨
      (observedRawSymbolAtBool_exact tokens openCursor .leftParen).mpr
        ⟨terminalCursor, token, atOpen, lookup, payload⟩,
      (observedRawSymbolAtBool_exact tokens closeCursor .rightParen).mpr
        closeObserved⟩, ?_⟩
    rw [boundaryEq]
    exact decide_eq_true
      ((observedProtectedRightParenRun_exact tokens
        interiorStart closeCursor).mpr run)

/-- The canonical U01 G01 bit agrees with the constructive semantic oracle. -/
theorem rawMatchingParenthesisObservation_eq_semantic
    (tokens : List Token) (openCursor closeCursor : Boundary tokens) :
    Chart.rawMatchingParenthesisObservation tokens openCursor closeCursor =
      semanticMatchingParenthesisObservation tokens openCursor
        closeCursor := by
  rw [Chart.rawMatchingParenthesisObservation_eq_observed]
  apply Bool.eq_iff_iff.mpr
  rw [observedMatchingParenthesisBool_exact,
    semanticMatchingParenthesisObservation_exact]

end Solcore.Surface.Multi

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

/-- The generalized public delimiter view selects exactly the first allowed
symbol at the starting delimiter depth. -/
theorem observedNextSameDepthDelimiterBool_exact
    (tokens : List Token) (start cursor : Boundary tokens)
    (allowed : NonemptyList Symbol) :
    Chart.observedNextSameDepthDelimiterBool tokens start cursor allowed =
        true ↔
      NextSameDepthDelimiter tokens start cursor allowed := by
  unfold Chart.observedNextSameDepthDelimiterBool NextSameDepthDelimiter
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨⟨sameDepth, allowedAtCursor⟩, earliest⟩
    refine ⟨
      (observedSameDelimiterDepthBool_exact tokens start cursor).mp
        sameDepth,
      (observedAllowedSymbolAtBool_exact tokens cursor allowed).mp
        allowedAtCursor,
      ?_⟩
    intro earlier startLe earlierLt earlierDepth earlierAllowed
    rw [List.all_eq_true] at earliest
    have selected := earliest earlier (List.mem_finRange _)
    have depthTrue :=
      (observedSameDelimiterDepthBool_exact tokens start earlier).mpr
        earlierDepth
    have allowedTrue :=
      (observedAllowedSymbolAtBool_exact tokens earlier allowed).mpr
        earlierAllowed
    rw [allowedTrue] at selected
    simp [startLe, earlierLt, depthTrue] at selected
  · rintro ⟨sameDepth, allowedAtCursor, earliest⟩
    refine ⟨⟨
      (observedSameDelimiterDepthBool_exact tokens start cursor).mpr
        sameDepth,
      (observedAllowedSymbolAtBool_exact tokens cursor allowed).mpr
        allowedAtCursor⟩, ?_⟩
    rw [List.all_eq_true]
    intro earlier _member
    by_cases startLe : start.val ≤ earlier.val
    · by_cases earlierLt : earlier.val < cursor.val
      · by_cases depth : SameDelimiterDepth tokens start earlier
        · have notAllowed := earliest earlier startLe earlierLt depth
          have depthTrue :=
            (observedSameDelimiterDepthBool_exact tokens start earlier).mpr
              depth
          have allowedFalse :
              Chart.observedAllowedSymbolAtBool earlier allowed = false := by
            apply Bool.eq_false_iff.mpr
            intro allowedTrue
            exact notAllowed
              ((observedAllowedSymbolAtBool_exact tokens earlier allowed).mp
                allowedTrue)
          simpa [startLe, earlierLt, depthTrue] using allowedFalse
        · have depthFalse :
              Chart.observedSameDelimiterDepthBool tokens start earlier =
                false := by
            exact Bool.eq_false_iff.mpr fun depthTrue => depth
              ((observedSameDelimiterDepthBool_exact
                tokens start earlier).mp depthTrue)
          simp [startLe, earlierLt, depthFalse]
      · simp [startLe, earlierLt]
    · simp [startLe]

private theorem observedRawSymbolAtBool_owned_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (cursor : Boundary tokens) (symbol : Symbol) :
    Chart.observedRawSymbolAtBool cursor symbol = true ↔
      SymbolAtBoundary file tokens cursor symbol := by
  change symbolAtBoundaryBool tokens cursor symbol = true ↔ _
  exact symbolAtBoundaryBool_eq_true_iff owned cursor symbol

private theorem observedImmediatelyAfterRawSymbolBool_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (symbol : Symbol)
    (cursor after : Boundary tokens) :
    Chart.observedImmediatelyAfterRawSymbolBool symbol cursor after = true ↔
      ImmediatelyAfterSymbol file tokens symbol cursor after := by
  change immediatelyAfterSymbolBool tokens symbol cursor after = true ↔ _
  exact immediatelyAfterSymbolBool_eq_true_iff owned symbol cursor after

/-- The proof-free canonical G02 header view is exactly the declarative
match-arm header judgment. -/
theorem observedSaturatedMatchArmHeaderObservation_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (regionStart cursor : Boundary tokens) :
    Chart.observedSaturatedMatchArmHeaderObservation tokens
        regionStart cursor = true ↔
      ArmHeaderAt file tokens regionStart cursor := by
  unfold Chart.observedSaturatedMatchArmHeaderObservation ArmHeaderAt
  simp only [Bool.and_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨⟨⟨ordered, sameDepth⟩, pipeObserved⟩, remainder⟩
    generalize boundaryEq : Chart.observedBoundaryAt? tokens
      (cursor.val + 1) = result at remainder
    cases result with
    | none => simp at remainder
    | some patternStart =>
        simp only [Bool.and_eq_true] at remainder
        rcases remainder with ⟨afterPipe, arrowSelected⟩
        rcases List.any_eq_true.mp arrowSelected with
          ⟨arrowCursor, _member, arrowFacts⟩
        simp only [Bool.and_eq_true] at arrowFacts
        rcases arrowFacts with ⟨delimiter, greatest⟩
        exact ⟨ordered,
          (observedSameDelimiterDepthBool_exact tokens regionStart
            cursor).mp sameDepth,
          (observedRawSymbolAtBool_owned_exact owned cursor .pipe).mp
            pipeObserved,
          patternStart, arrowCursor,
          (observedImmediatelyAfterRawSymbolBool_exact owned .pipe cursor
            patternStart).mp afterPipe,
          (observedNextSameDepthDelimiterBool_exact tokens patternStart
            arrowCursor ⟨.fatArrow, []⟩).mp delimiter,
          (saturatedRawGreatestEndObservation_exact owned
            (.aux Grammar.matchArmPatternListSite.site) patternStart
            arrowCursor arrowCursor).mp greatest⟩
  · rintro ⟨ordered, sameDepth, pipeObserved, patternStart,
      arrowCursor, afterPipe, delimiter, greatest⟩
    rcases afterPipe with
      ⟨terminalCursor, token, atCursor, atPattern, terminalAt, payload⟩
    have patternValue : patternStart.val = cursor.val + 1 := by
      have cursorValue := congrArg Fin.val atCursor
      have patternCursorValue := congrArg Fin.val atPattern
      change terminalCursor.val = cursor.val at cursorValue
      change terminalCursor.val + 1 = patternStart.val at patternCursorValue
      omega
    have boundaryEq : Chart.observedBoundaryAt? tokens
        (cursor.val + 1) = some patternStart :=
      (chart_observedBoundaryAt?_eq_some_iff
        (cursor.val + 1) patternStart).mpr patternValue
    refine ⟨⟨⟨ordered,
      (observedSameDelimiterDepthBool_exact tokens regionStart cursor).mpr
        sameDepth⟩,
      (observedRawSymbolAtBool_owned_exact owned cursor .pipe).mpr
        pipeObserved⟩, ?_⟩
    rw [boundaryEq]
    simp only [Bool.and_eq_true]
    refine ⟨
      (observedImmediatelyAfterRawSymbolBool_exact owned .pipe cursor
        patternStart).mpr
          ⟨terminalCursor, token, atCursor, atPattern, terminalAt, payload⟩,
      ?_⟩
    apply List.any_eq_true.mpr
    refine ⟨arrowCursor, List.mem_finRange _, ?_⟩
    simp only [Bool.and_eq_true]
    exact ⟨
      (observedNextSameDepthDelimiterBool_exact tokens patternStart
        arrowCursor ⟨.fatArrow, []⟩).mpr delimiter,
      (saturatedRawGreatestEndObservation_exact owned
        (.aux Grammar.matchArmPatternListSite.site) patternStart
        arrowCursor arrowCursor).mpr greatest⟩

/-- The canonical U01 G02 header oracle agrees with its semantic adapter. -/
theorem saturatedMatchArmHeaderObservation_eq_semantic
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (regionStart cursor : Boundary tokens) :
    Chart.saturatedMatchArmHeaderObservation tokens regionStart cursor =
      semanticMatchArmHeaderObservation owned regionStart cursor := by
  rw [Chart.saturatedMatchArmHeaderObservation_eq_observed]
  apply Bool.eq_iff_iff.mpr
  rw [observedSaturatedMatchArmHeaderObservation_exact owned,
    semanticMatchArmHeaderObservation_exact owned]

end Solcore.Surface.Multi

namespace Solcore.Surface.Multi

open Solcore.Workspace
open Grammar

/-- A successful observed contextual worklist is semantically complete for
every declarative Phase-C item and checked edge under the supplied Phase-B
correctness bridge. -/
theorem executeObservedContextualWorklist?_complete
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result)
    (correct : PhaseBCorrect file tokens result.memo) :
    ∃ final : AllGuardsFinal result.memo,
      (∀ item, ContextualReach file tokens result.memo correct final item →
        item ∈ result.items) ∧
      (∀ key, ContextualEdgeReach file tokens result.memo correct final key →
        ∃ retained, retained ∈ result.edges ∧ retained.val = key) := by
  exact executeObservedContextualWorklist?_complete_of_operationalClosure
    file tokens owned result selected correct
      (Chart.executeObservedContextualWorklist?_operationalClosure
        file tokens owned result selected)

/-- The completion backpointer is unique for all declaratively reachable
completed edges in every successful observed contextual worklist. -/
theorem executeObservedContextualWorklist?_completionBackpointerUnique
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result)
    (correct : PhaseBCorrect file tokens result.memo) :
    ∃ final : AllGuardsFinal result.memo,
      CompletionBackpointerUnique file tokens result.memo correct final := by
  exact
    executeObservedContextualWorklist?_completionBackpointerUnique_of_operationalClosure
      file tokens owned result selected correct
      (Chart.executeObservedContextualWorklist?_operationalClosure
        file tokens owned result selected)

end Solcore.Surface.Multi

namespace Solcore.Surface.Multi

open Grammar

/-- The protected singleton-brace executor is exactly its declarative run. -/
theorem observedProtectedRightBraceRun_exact
    (tokens : List Token) (start finish : Boundary tokens) :
    Chart.observedProtectedDelimiterRun? tokens [.rightBrace]
        start finish = some [.rightBrace] ↔
      ProtectedDelimiterRun tokens
        { head := .rightBrace, tail := [] } start finish
        { head := .rightBrace, tail := [] } := by
  simpa [nonemptyValues, observedNonemptyToSemantic,
    observedCloserToSemantic] using
    observedProtectedDelimiterRun?_eq_some_iff tokens
      { head := Chart.ObservedDelimiterCloser.rightBrace, tail := [] }
      { head := Chart.ObservedDelimiterCloser.rightBrace, tail := [] }
      start finish

/-- The public matching-brace bit recognizes exactly one protected matching
brace pair in the declarative parser semantics. -/
theorem observedMatchingBraceBool_exact
    (tokens : List Token) (openCursor closeCursor : Boundary tokens) :
    Chart.observedMatchingBraceBool tokens openCursor closeCursor = true ↔
      MatchingDelimiter tokens openCursor closeCursor
        .leftBrace .rightBrace := by
  unfold Chart.observedMatchingBraceBool MatchingDelimiter
  simp only [Bool.and_eq_true, true_and]
  constructor
  · rintro ⟨⟨openAccepted, closeAccepted⟩, runAccepted⟩
    generalize boundaryEq : Chart.observedBoundaryAt? tokens
      (openCursor.val + 1) = result at runAccepted
    cases result with
    | none => simp at runAccepted
    | some interiorStart =>
        have coordinateEq : interiorStart.val = openCursor.val + 1 :=
          (chart_observedBoundaryAt?_eq_some_iff
            (openCursor.val + 1) interiorStart).mp boundaryEq
        rcases (observedRawSymbolAtBool_exact tokens openCursor
          .leftBrace).mp openAccepted with
          ⟨terminalCursor, token, atOpen, lookup, payload⟩
        have atInterior : terminalCursor.afterBoundary = interiorStart := by
          apply Fin.ext
          have atOpenValue := congrArg Fin.val atOpen
          change terminalCursor.val = openCursor.val at atOpenValue
          change terminalCursor.val + 1 = interiorStart.val
          omega
        refine ⟨interiorStart,
          ⟨terminalCursor, token, atOpen, atInterior, lookup, payload⟩,
          (observedRawSymbolAtBool_exact tokens closeCursor
            .rightBrace).mp closeAccepted,
          ?_⟩
        exact (observedProtectedRightBraceRun_exact tokens
          interiorStart closeCursor).mp (of_decide_eq_true runAccepted)
  · rintro ⟨interiorStart,
      ⟨terminalCursor, token, atOpen, atInterior, lookup, payload⟩,
      closeObserved, run⟩
    have coordinateEq : interiorStart.val = openCursor.val + 1 := by
      have atOpenValue := congrArg Fin.val atOpen
      have atInteriorValue := congrArg Fin.val atInterior
      change terminalCursor.val = openCursor.val at atOpenValue
      change terminalCursor.val + 1 = interiorStart.val at atInteriorValue
      omega
    have boundaryEq : Chart.observedBoundaryAt? tokens
        (openCursor.val + 1) = some interiorStart :=
      (chart_observedBoundaryAt?_eq_some_iff
        (openCursor.val + 1) interiorStart).mpr coordinateEq
    refine ⟨⟨
      (observedRawSymbolAtBool_exact tokens openCursor .leftBrace).mpr
        ⟨terminalCursor, token, atOpen, lookup, payload⟩,
      (observedRawSymbolAtBool_exact tokens closeCursor .rightBrace).mpr
        closeObserved⟩, ?_⟩
    rw [boundaryEq]
    exact decide_eq_true
      ((observedProtectedRightBraceRun_exact tokens
        interiorStart closeCursor).mpr run)

private theorem observedContainingBraceFrameBool_exact
    (tokens : List Token) (cursor openCursor closeCursor : Boundary tokens) :
    Chart.observedContainingBraceFrameBool tokens cursor openCursor
        closeCursor = true ↔
      ContainingBraceFrame tokens cursor openCursor closeCursor := by
  unfold Chart.observedContainingBraceFrameBool ContainingBraceFrame
  simp only [Bool.and_eq_true, decide_eq_true_iff,
    observedMatchingBraceBool_exact]
  constructor
  · rintro ⟨⟨openLt, closeLt⟩, matching⟩
    exact ⟨openLt, closeLt, matching⟩
  · rintro ⟨openLt, closeLt, matching⟩
    exact ⟨⟨openLt, closeLt⟩, matching⟩

/-- The proof-free greatest-opening brace-frame bit is exactly the
declarative innermost-frame judgment. -/
theorem observedInnermostContainingBraceFrameBool_exact
    (tokens : List Token) (cursor openCursor closeCursor : Boundary tokens) :
    Chart.observedInnermostContainingBraceFrameBool tokens cursor
        openCursor closeCursor = true ↔
      InnermostContainingBraceFrame tokens cursor openCursor
        closeCursor := by
  unfold Chart.observedInnermostContainingBraceFrameBool
    InnermostContainingBraceFrame
  simp only [Bool.and_eq_true,
    observedContainingBraceFrameBool_exact]
  constructor
  · rintro ⟨containing, greatest⟩
    refine ⟨containing, ?_⟩
    intro otherOpen otherClose otherContaining
    rw [List.all_eq_true] at greatest
    have selectedOpen := greatest otherOpen (List.mem_finRange _)
    rw [List.all_eq_true] at selectedOpen
    have selected := selectedOpen otherClose (List.mem_finRange _)
    have containingTrue :=
      (observedContainingBraceFrameBool_exact tokens cursor
        otherOpen otherClose).mpr otherContaining
    rw [containingTrue] at selected
    simpa using selected
  · rintro ⟨containing, greatest⟩
    refine ⟨containing, ?_⟩
    rw [List.all_eq_true]
    intro otherOpen _memberOpen
    rw [List.all_eq_true]
    intro otherClose _memberClose
    by_cases otherContaining :
        ContainingBraceFrame tokens cursor otherOpen otherClose
    · have containingTrue :=
        (observedContainingBraceFrameBool_exact tokens cursor
          otherOpen otherClose).mpr otherContaining
      have otherLe := greatest otherOpen otherClose otherContaining
      simp [containingTrue, otherLe]
    · have containingFalse :
          Chart.observedContainingBraceFrameBool tokens cursor
              otherOpen otherClose = false := by
        exact Bool.eq_false_iff.mpr fun selected => otherContaining
          ((observedContainingBraceFrameBool_exact tokens cursor
            otherOpen otherClose).mp selected)
      simp [containingFalse]

end Solcore.Surface.Multi

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

/-- The canonical proof-free next-arm-or-close selector is exactly the first
same-frame header or the containing close brace. -/
theorem observedSaturatedNextArmOrCloseBool_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (regionStart closeCursor regionEnd : Boundary tokens) :
    Chart.observedSaturatedNextArmOrCloseBool tokens regionStart
        closeCursor regionEnd = true ↔
      NextArmOrClose file tokens regionStart closeCursor regionEnd := by
  unfold Chart.observedSaturatedNextArmOrCloseBool NextArmOrClose
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_iff,
    observedSameDelimiterDepthBool_exact,
    observedSaturatedMatchArmHeaderObservation_exact owned]
  constructor
  · rintro ⟨⟨⟨⟨startLe, endLe⟩, sameDepth⟩, selectedEnd⟩,
      earliest⟩
    refine ⟨startLe, endLe, sameDepth, selectedEnd, ?_⟩
    intro earlier earlierStartLe earlierLt earlierDepth earlierSelected
    rw [List.all_eq_true] at earliest
    have selected := earliest earlier (List.mem_finRange _)
    have depthTrue :=
      (observedSameDelimiterDepthBool_exact tokens regionStart earlier).mpr
        earlierDepth
    rcases earlierSelected with earlierEq | earlierHeader
    · have earlierValue := congrArg Fin.val earlierEq
      omega
    · have headerTrue :=
        (observedSaturatedMatchArmHeaderObservation_exact owned
          regionStart earlier).mpr earlierHeader
      simp [earlierStartLe, earlierLt, depthTrue, headerTrue] at selected
  · rintro ⟨startLe, endLe, sameDepth, selectedEnd, earliest⟩
    refine ⟨⟨⟨⟨startLe, endLe⟩, sameDepth⟩, selectedEnd⟩, ?_⟩
    rw [List.all_eq_true]
    intro earlier _member
    by_cases earlierStartLe : regionStart.val ≤ earlier.val
    · by_cases earlierLt : earlier.val < regionEnd.val
      · by_cases earlierDepth :
          SameDelimiterDepth tokens regionStart earlier
        · have notSelected :=
            earliest earlier earlierStartLe earlierLt earlierDepth
          have depthTrue :=
            (observedSameDelimiterDepthBool_exact tokens regionStart
              earlier).mpr earlierDepth
          have notClose : earlier ≠ closeCursor :=
            fun equal => notSelected (Or.inl equal)
          have notHeader :
              ¬ ArmHeaderAt file tokens regionStart earlier :=
            fun header => notSelected (Or.inr header)
          have headerFalse :
              Chart.observedSaturatedMatchArmHeaderObservation tokens
                  regionStart earlier = false := by
            exact Bool.eq_false_iff.mpr fun headerTrue => notHeader
              ((observedSaturatedMatchArmHeaderObservation_exact owned
                regionStart earlier).mp headerTrue)
          simp [earlierStartLe, earlierLt, depthTrue, notClose,
            headerFalse]
        · have depthFalse :
              Chart.observedSameDelimiterDepthBool tokens regionStart
                earlier = false := by
            exact Bool.eq_false_iff.mpr fun depthTrue => earlierDepth
              ((observedSameDelimiterDepthBool_exact tokens regionStart
                earlier).mp depthTrue)
          simp [earlierStartLe, earlierLt, depthFalse]
      · simp [earlierStartLe, earlierLt]
    · simp [earlierStartLe]

end Solcore.Surface.Multi

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

/-- The public canonical statement-region view is exactly the declarative
nearest braced-body or match-arm region. -/
theorem observedSaturatedStatementRegionObservation_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (regionStart regionEnd : Boundary tokens) :
    Chart.observedSaturatedStatementRegionObservation tokens
        regionStart regionEnd = true ↔
      NearestStatementRegion file tokens regionStart regionEnd := by
  unfold Chart.observedSaturatedStatementRegionObservation
    NearestStatementRegion
  simp only [Bool.or_eq_true]
  constructor
  · rintro (braced | arm)
    · rcases List.any_eq_true.mp braced with
        ⟨openCursor, _member, facts⟩
      simp only [Bool.and_eq_true] at facts
      exact Or.inl ⟨openCursor,
        (observedImmediatelyAfterRawSymbolBool_exact owned .leftBrace
          openCursor regionStart).mp facts.1,
        (observedMatchingBraceBool_exact tokens openCursor regionEnd).mp
          facts.2⟩
    · rcases List.any_eq_true.mp arm with
        ⟨arrowCursor, _arrowMember, arrowFacts⟩
      simp only [Bool.and_eq_true] at arrowFacts
      rcases List.any_eq_true.mp arrowFacts.2 with
        ⟨openCursor, _openMember, openSelected⟩
      rcases List.any_eq_true.mp openSelected with
        ⟨closeCursor, _closeMember, frameFacts⟩
      simp only [Bool.and_eq_true] at frameFacts
      exact Or.inr ⟨arrowCursor, openCursor, closeCursor,
        (observedImmediatelyAfterRawSymbolBool_exact owned .fatArrow
          arrowCursor regionStart).mp arrowFacts.1,
        (observedInnermostContainingBraceFrameBool_exact tokens arrowCursor
          openCursor closeCursor).mp frameFacts.1,
        (observedSaturatedNextArmOrCloseBool_exact owned regionStart
          closeCursor regionEnd).mp frameFacts.2⟩
  · rintro (braced | arm)
    · apply Or.inl
      apply List.any_eq_true.mpr
      rcases braced with ⟨openCursor, afterOpen, matching⟩
      refine ⟨openCursor, List.mem_finRange _, ?_⟩
      simp only [Bool.and_eq_true]
      exact ⟨
        (observedImmediatelyAfterRawSymbolBool_exact owned .leftBrace
          openCursor regionStart).mpr afterOpen,
        (observedMatchingBraceBool_exact tokens openCursor regionEnd).mpr
          matching⟩
    · apply Or.inr
      apply List.any_eq_true.mpr
      rcases arm with ⟨arrowCursor, openCursor, closeCursor,
        afterArrow, frame, next⟩
      refine ⟨arrowCursor, List.mem_finRange _, ?_⟩
      simp only [Bool.and_eq_true]
      refine ⟨
        (observedImmediatelyAfterRawSymbolBool_exact owned .fatArrow
          arrowCursor regionStart).mpr afterArrow, ?_⟩
      apply List.any_eq_true.mpr
      refine ⟨openCursor, List.mem_finRange _, ?_⟩
      apply List.any_eq_true.mpr
      refine ⟨closeCursor, List.mem_finRange _, ?_⟩
      simp only [Bool.and_eq_true]
      exact ⟨
        (observedInnermostContainingBraceFrameBool_exact tokens arrowCursor
          openCursor closeCursor).mpr frame,
        (observedSaturatedNextArmOrCloseBool_exact owned regionStart
          closeCursor regionEnd).mpr next⟩

/-- The canonical U01 G08 region oracle agrees with its semantic adapter. -/
theorem saturatedStatementRegionObservation_eq_semantic
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (regionStart regionEnd : Boundary tokens) :
    Chart.saturatedStatementRegionObservation tokens regionStart regionEnd =
      semanticStatementRegionObservation owned regionStart regionEnd := by
  rw [Chart.saturatedStatementRegionObservation_eq_observed]
  apply Bool.eq_iff_iff.mpr
  rw [observedSaturatedStatementRegionObservation_exact owned,
    semanticStatementRegionObservation_exact owned]

end Solcore.Surface.Multi

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

/-- The complete canonical U01 positive bit agrees guard-by-guard with the
constructive semantic positive bit. -/
theorem saturatedGuardPositiveObservationBool_eq_semantic
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (key : GuardInstanceKey tokens) :
    Chart.saturatedGuardPositiveObservationBool owned key =
      semanticGuardPositiveObservationBool owned key := by
  have matchingEq : Chart.rawMatchingParenthesisObservation tokens =
      semanticMatchingParenthesisObservation tokens := by
    funext openCursor closeCursor
    exact rawMatchingParenthesisObservation_eq_semantic tokens
      openCursor closeCursor
  have headerEq : Chart.saturatedMatchArmHeaderObservation tokens =
      semanticMatchArmHeaderObservation owned := by
    funext regionStart cursor
    exact saturatedMatchArmHeaderObservation_eq_semantic owned
      regionStart cursor
  have patternEq : Chart.rawPatternDelimiterObservation tokens =
      semanticPatternDelimiterObservation tokens := by
    funext start cursor
    exact rawPatternDelimiterObservation_eq_semantic tokens start cursor
  have regionEq : Chart.saturatedStatementRegionObservation tokens =
      semanticStatementRegionObservation owned := by
    funext regionStart regionEnd
    exact saturatedStatementRegionObservation_eq_semantic owned
      regionStart regionEnd
  have greatestEq : Chart.saturatedRawGreatestEndObservation tokens =
      semanticGreatestEndObservation owned := by
    funext symbol start upperBound finish
    exact saturatedRawGreatestEndObservation_eq_semantic owned symbol
      start upperBound finish
  cases guardEq : key.guard <;>
    simp [Chart.saturatedGuardPositiveObservationBool,
      semanticGuardPositiveObservationBool, guardEq, matchingEq,
      headerEq, patternEq, regionEq, greatestEq]

/-- The fully-final canonical U01 memo is the unified semantic memo. -/
theorem saturatedGuardMemo_eq_semantic
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    Chart.saturatedGuardMemo owned = semanticGuardMemo owned := by
  funext key
  unfold Chart.saturatedGuardMemo semanticGuardMemo
  rw [saturatedGuardPositiveObservationBool_eq_semantic owned key]

end Solcore.Surface.Multi

namespace Solcore.Surface.Multi

open Solcore.Workspace

/-- Every successful observed guard worklist returns the unified semantic
guard memo, without an additional correctness premise. -/
theorem executeObservedGuardWorklist?_memo_eq_semantic
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.GuardWorklistResult tokens)
    (selected : Chart.executeObservedGuardWorklist? file tokens owned =
      some result) :
    result.memo = semanticGuardMemo owned :=
  (Chart.executeObservedGuardWorklist?_memo_eq_saturated
    file tokens owned result selected).trans
      (saturatedGuardMemo_eq_semantic owned)

/-- Every successful observed Phase-A/Phase-B worklist is declaratively
correct, unconditionally. -/
theorem executeObservedGuardWorklist?_phaseBCorrect
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.GuardWorklistResult tokens)
    (selected : Chart.executeObservedGuardWorklist? file tokens owned =
      some result) :
    PhaseBCorrect file tokens result.memo := by
  rw [executeObservedGuardWorklist?_memo_eq_semantic
    file tokens owned result selected]
  exact semanticGuardMemo_correct owned

/-- Phase C preserves the same unified semantic guard memo exposed by its
successful observed Phase-A/Phase-B prefix. -/
theorem executeObservedContextualWorklist?_memo_eq_semantic
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result) :
    result.memo = semanticGuardMemo owned :=
  (Chart.executeObservedContextualWorklist?_memo_eq_saturated
    file tokens owned result selected).trans
      (saturatedGuardMemo_eq_semantic owned)

/-- Every successful observed contextual worklist carries an unconditionally
correct Phase-B memo. -/
theorem executeObservedContextualWorklist?_phaseBCorrect
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result) :
    PhaseBCorrect file tokens result.memo := by
  rw [executeObservedContextualWorklist?_memo_eq_semantic
    file tokens owned result selected]
  exact semanticGuardMemo_correct owned

end Solcore.Surface.Multi

namespace Solcore.Surface.Multi

open Solcore.Workspace
open Grammar

/-- One successful observed contextual execution is an exact declarative
correspondence: its item and edge ledgers are sound and complete, and its
completion backpointer is unique.  Correctness and finality are selected from
the execution itself rather than required as caller-supplied proofs. -/
theorem executeObservedContextualWorklist?_correspondence
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result) :
    let correct := executeObservedContextualWorklist?_phaseBCorrect
      file tokens owned result selected
    let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
      file tokens owned result selected
    (∀ item, item ∈ result.items ↔
      ContextualReach file tokens result.memo correct final item) ∧
    (∀ key, (∃ retained, retained ∈ result.edges ∧ retained.val = key) ↔
      ContextualEdgeReach file tokens result.memo correct final key) ∧
    CompletionBackpointerUnique file tokens result.memo correct final := by
  let correct := executeObservedContextualWorklist?_phaseBCorrect
    file tokens owned result selected
  let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
    file tokens owned result selected
  change
    (∀ item, item ∈ result.items ↔
      ContextualReach file tokens result.memo correct final item) ∧
    (∀ key, (∃ retained, retained ∈ result.edges ∧ retained.val = key) ↔
      ContextualEdgeReach file tokens result.memo correct final key) ∧
    CompletionBackpointerUnique file tokens result.memo correct final
  have operational :=
    Chart.executeObservedContextualWorklist?_operational_sound
      file tokens owned result selected
  have closed := Chart.executeObservedContextualWorklist?_operationalClosure
    file tokens owned result selected
  have itemSound : ∀ item, item ∈ result.items →
      ContextualReach file tokens result.memo correct final item := by
    intro item member
    exact operationalContextualReach_sound correct final
      (operational.1 item member)
  have itemComplete : ∀ item,
      ContextualReach file tokens result.memo correct final item →
        item ∈ result.items := by
    intro item reached
    exact closed.reach_complete
      (contextualReach_operational correct final reached)
  have edgeSound : ∀ retained, retained ∈ result.edges →
      ContextualEdgeReach file tokens result.memo correct final
        retained.val := by
    intro retained member
    exact operationalContextualEdgeReach_sound correct final
      (operational.2 retained member)
  have edgeComplete : ∀ key,
      ContextualEdgeReach file tokens result.memo correct final key →
        ∃ retained, retained ∈ result.edges ∧ retained.val = key := by
    intro key reached
    exact closed.edge_complete
      (contextualEdgeReach_operational correct final reached)
  refine ⟨?_, ?_, ?_⟩
  · intro item
    exact ⟨itemSound item, itemComplete item⟩
  · intro key
    constructor
    · rintro ⟨retained, member, rfl⟩
      exact edgeSound retained member
    · exact edgeComplete key
  · exact
      executeObservedContextualWorklist?_completionBackpointerUnique_of_edge_complete
        file tokens owned result selected correct final edgeComplete

end Solcore.Surface.Multi

namespace Solcore.Surface.Multi

open Solcore.Workspace
open Grammar

/-- Auxiliary action execution is accepted by the exact declarative action
reduction relation at every chart interval. -/
theorem executeAuxiliaryAction_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (production : ProductionId)
    (auxiliary : AuxiliaryProduction production)
    (origin finish : Boundary tokens)
    (input : GrammarSymbolValues file tokens production.rhs) :
    ActionReduces file tokens (.actionFor production) origin finish input
      (executeAuxiliaryAction production auxiliary input) := by
  cases production with
  | root rule => contradiction
  | atom site => exact .atom site origin finish input
  | seq site => exact .seq site origin finish input
  | group site => exact .group site origin finish input
  | choice site branch => exact .choice site branch origin finish input
  | opt site branch => exact .opt site branch origin finish input
  | star site branch => exact .star site branch origin finish input
  | plus site branch => exact .plus site branch origin finish input
  | list0 site branch => exact .list0 site branch origin finish input
  | list1 site => exact .list1 site origin finish input
  | tail site branch => exact .tail site branch origin finish input

/-- The executable auxiliary result is the unique result admitted by the
action relation. -/
theorem ActionReduces.eq_executeAuxiliaryAction
    {file : WorkspaceFile} {tokens : List Token}
    {production : ProductionId}
    (auxiliary : AuxiliaryProduction production)
    {origin finish : Boundary tokens}
    {input : GrammarSymbolValues file tokens production.rhs}
    {output : NonterminalValue file tokens production.lhs}
    (reduces : ActionReduces file tokens (.actionFor production)
      origin finish input output) :
    output = executeAuxiliaryAction production auxiliary input :=
  ActionReduces.functional reduces
    (executeAuxiliaryAction_reduces production auxiliary origin finish input)

end Solcore.Surface.Multi

namespace Solcore.Surface.Multi

open Solcore.Workspace
open Grammar

/-- Every value returned by the optional auxiliary executor satisfies the
exact declarative action relation at any chart interval. -/
theorem executeAuxiliaryAction?_sound
    {file : WorkspaceFile} {tokens : List Token}
    (production : ProductionId)
    (origin finish : Boundary tokens)
    (input : GrammarSymbolValues file tokens production.rhs)
    (output : NonterminalValue file tokens production.lhs)
    (selected : executeAuxiliaryAction? production input = some output) :
    ActionReduces file tokens (.actionFor production) origin finish input
      output := by
  cases production with
  | root rule => simp [executeAuxiliaryAction?] at selected
  | atom site =>
      simp only [executeAuxiliaryAction?] at selected
      cases selected
      exact executeAuxiliaryAction_reduces (.atom site) trivial
        origin finish input
  | seq site =>
      simp only [executeAuxiliaryAction?] at selected
      cases selected
      exact executeAuxiliaryAction_reduces (.seq site) trivial
        origin finish input
  | group site =>
      simp only [executeAuxiliaryAction?] at selected
      cases selected
      exact executeAuxiliaryAction_reduces (.group site) trivial
        origin finish input
  | choice site branch =>
      simp only [executeAuxiliaryAction?] at selected
      cases selected
      exact executeAuxiliaryAction_reduces (.choice site branch) trivial
        origin finish input
  | opt site branch =>
      simp only [executeAuxiliaryAction?] at selected
      cases selected
      exact executeAuxiliaryAction_reduces (.opt site branch) trivial
        origin finish input
  | star site branch =>
      simp only [executeAuxiliaryAction?] at selected
      cases selected
      exact executeAuxiliaryAction_reduces (.star site branch) trivial
        origin finish input
  | plus site branch =>
      simp only [executeAuxiliaryAction?] at selected
      cases selected
      exact executeAuxiliaryAction_reduces (.plus site branch) trivial
        origin finish input
  | list0 site branch =>
      simp only [executeAuxiliaryAction?] at selected
      cases selected
      exact executeAuxiliaryAction_reduces (.list0 site branch) trivial
        origin finish input
  | list1 site =>
      simp only [executeAuxiliaryAction?] at selected
      cases selected
      exact executeAuxiliaryAction_reduces (.list1 site) trivial
        origin finish input
  | tail site branch =>
      simp only [executeAuxiliaryAction?] at selected
      cases selected
      exact executeAuxiliaryAction_reduces (.tail site branch) trivial
        origin finish input

end Solcore.Surface.Multi
namespace Solcore.Surface.Multi

open Solcore.Workspace
open Grammar

/-- The greatest retained current boundary of a successful observed contextual
execution is exactly the greatest cursor of the saturated declarative reach
relation selected by that execution. -/
theorem executeObservedContextualWorklist?_greatestCurrent?_eq_some_iff
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result)
    (cursor : Boundary tokens) :
    result.greatestCurrent? = some cursor ↔
      let correct := executeObservedContextualWorklist?_phaseBCorrect
        file tokens owned result selected
      let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
        file tokens owned result selected
      GreatestReachableCursor file tokens result.memo correct final cursor := by
  let correct := executeObservedContextualWorklist?_phaseBCorrect
    file tokens owned result selected
  let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
    file tokens owned result selected
  change result.greatestCurrent? = some cursor ↔
    GreatestReachableCursor file tokens result.memo correct final cursor
  rw [Chart.ContextualWorklistResult.greatestCurrent?_eq_some_iff]
  have correspondence :=
    executeObservedContextualWorklist?_correspondence
      file tokens owned result selected
  change
    (∀ item, item ∈ result.items ↔
      ContextualReach file tokens result.memo correct final item) ∧ _ ∧ _
      at correspondence
  constructor
  · rintro ⟨⟨item, member, currentEq⟩, greatest⟩
    refine ⟨⟨item, (correspondence.1 item).mp member, currentEq⟩, ?_⟩
    intro other reached
    exact greatest other ((correspondence.1 other).mpr reached)
  · rintro ⟨⟨item, reached, currentEq⟩, greatest⟩
    refine ⟨⟨item, (correspondence.1 item).mpr reached, currentEq⟩, ?_⟩
    intro other member
    exact greatest other ((correspondence.1 other).mp member)

/-- Successful observed contextual execution always exposes a greatest
retained current boundary. -/
theorem executeObservedContextualWorklist?_greatestCurrent?_exists
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result) :
    ∃ cursor, result.greatestCurrent? = some cursor := by
  let correct := executeObservedContextualWorklist?_phaseBCorrect
    file tokens owned result selected
  let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
    file tokens owned result selected
  rcases chart_greatest_cursor_exists owned correct final with
    ⟨cursor, greatest⟩
  exact ⟨cursor,
    (executeObservedContextualWorklist?_greatestCurrent?_eq_some_iff
      file tokens owned result selected cursor).mpr greatest⟩

/-- The empty-ledger branch of greatest-boundary selection is unreachable for
a successful observed contextual execution. -/
theorem executeObservedContextualWorklist?_greatestCurrent?_ne_none
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result) :
    result.greatestCurrent? ≠ none := by
  rcases executeObservedContextualWorklist?_greatestCurrent?_exists
    file tokens owned result selected with ⟨cursor, cursorEq⟩
  intro noneEq
  rw [noneEq] at cursorEq
  contradiction

end Solcore.Surface.Multi

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace
open Grammar

/-- The optional-comma executor realizes the exact source-rule reduction. -/
theorem executeOptionalCommaRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (_ready : RuleReductionReady file tokens .optionalComma origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .optionalComma)) :
    RuleReduction file tokens .optionalComma origin finish input
      (executeOptionalCommaRoot input) := by
  change EbnfValue file tokens
    (.optional (.atom (.terminal (.symbol .comma)))) at input
  generalize viewEq : EbnfValue.optionalView
    (.atom (.terminal (.symbol .comma))) input = viewed
  cases viewed with
  | none =>
      have inputEq : EbnfValue.optional
          (.atom (.terminal (.symbol .comma))) none = input := by
        calc
          _ = EbnfValue.optional _
              (EbnfValue.optionalView _ input) := by rw [viewEq]
          _ = input := EbnfValue.optional_of_view _ input
      have resultEq : executeOptionalCommaRoot input = .absent := by
        simp [executeOptionalCommaRoot, viewEq]
      rw [resultEq, ← inputEq]
      exact .optionalCommaAbsent origin finish
  | some rawComma =>
      let comma := EbnfValue.terminalView (.symbol .comma) rawComma
      have rawCommaEq : EbnfValue.terminalAtom (.symbol .comma) comma =
          rawComma := EbnfValue.terminal_of_view _ rawComma
      have inputEq : EbnfValue.optional
          (.atom (.terminal (.symbol .comma)))
          (some (EbnfValue.terminalAtom (.symbol .comma) comma)) = input := by
        calc
          _ = EbnfValue.optional _ (some rawComma) := by rw [rawCommaEq]
          _ = EbnfValue.optional _
              (EbnfValue.optionalView _ input) := by rw [viewEq]
          _ = input := EbnfValue.optional_of_view _ input
      have resultEq : executeOptionalCommaRoot input = .present comma.span := by
        simp [executeOptionalCommaRoot, viewEq, comma]
      rw [resultEq, ← inputEq]
      exact .optionalCommaPresent origin finish comma

/-- The top-item executor realizes the exact source-rule reduction. -/
theorem executeTopItemRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .topItem origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .topItem)) :
    RuleReduction file tokens .topItem origin finish input
      (executeTopItemRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let branches : List EbnfExpr := [
    .atom (.nonterminal .importDecl), .atom (.nonterminal .exportDecl),
    .atom (.nonterminal .pragmaDecl), .atom (.nonterminal .dataDecl),
    .atom (.nonterminal .typeAliasDecl), .atom (.nonterminal .classDecl),
    .atom (.nonterminal .instanceDecl), .atom (.nonterminal .contractDecl),
    .atom (.nonterminal .functionDecl)]
  change EbnfValue file tokens (.choice branches) at input
  generalize viewEq : EbnfValue.choiceView branches input = viewed
  rcases viewed with ⟨branch, raw⟩
  have inputEq : EbnfValue.choice branches ⟨branch, raw⟩ = input := by
    calc
      _ = EbnfValue.choice branches
          (EbnfValue.choiceView branches input) := by rw [viewEq]
      _ = input := EbnfValue.choice_of_view branches input
  have branchCases : branch = 0 ∨ branch = 1 ∨ branch = 2 ∨
      branch = 3 ∨ branch = 4 ∨ branch = 5 ∨ branch = 6 ∨
      branch = 7 ∨ branch = 8 := by
    have branchesLength : branches.length = 9 := by rfl
    have bound : branch.val < 9 := by
      calc
        branch.val < branches.length := branch.isLt
        _ = 9 := branchesLength
    have valueCases : branch.val = 0 ∨ branch.val = 1 ∨
        branch.val = 2 ∨ branch.val = 3 ∨ branch.val = 4 ∨
        branch.val = 5 ∨ branch.val = 6 ∨ branch.val = 7 ∨
        branch.val = 8 := by omega
    rcases valueCases with valueEq | valueEq | valueEq | valueEq |
      valueEq | valueEq | valueEq | valueEq | valueEq
    all_goals first
      | exact Or.inl (Fin.ext valueEq)
      | exact Or.inr (Or.inl (Fin.ext valueEq))
      | exact Or.inr (Or.inr (Or.inl (Fin.ext valueEq)))
      | exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext valueEq))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl (Fin.ext valueEq)))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl (Fin.ext valueEq))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl (Fin.ext valueEq)))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl (Fin.ext valueEq))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Fin.ext valueEq))))))))
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  rcases branchCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · let declaration := EbnfValue.ruleView .importDecl raw
    have rawEq := EbnfValue.rule_of_view .importDecl raw
    have resultEq : executeTopItemRoot file tokens origin finish
        ready.1 ready.2.1 input =
          sourceLoc witness (.importDecl declaration) := by
      rw [executeTopItemRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .topItemImport origin finish declaration witness
  · let declaration := EbnfValue.ruleView .exportDecl raw
    have rawEq := EbnfValue.rule_of_view .exportDecl raw
    have resultEq : executeTopItemRoot file tokens origin finish
        ready.1 ready.2.1 input =
          sourceLoc witness (.exportDecl declaration) := by
      rw [executeTopItemRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .topItemExport origin finish declaration witness
  · let declaration := EbnfValue.ruleView .pragmaDecl raw
    have rawEq := EbnfValue.rule_of_view .pragmaDecl raw
    have resultEq : executeTopItemRoot file tokens origin finish
        ready.1 ready.2.1 input =
          sourceLoc witness (.pragmaDecl declaration) := by
      rw [executeTopItemRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .topItemPragma origin finish declaration witness
  · let declaration := EbnfValue.ruleView .dataDecl raw
    have rawEq := EbnfValue.rule_of_view .dataDecl raw
    have resultEq : executeTopItemRoot file tokens origin finish
        ready.1 ready.2.1 input =
          sourceLoc witness (.dataDecl declaration) := by
      rw [executeTopItemRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .topItemData origin finish declaration witness
  · let declaration := EbnfValue.ruleView .typeAliasDecl raw
    have rawEq := EbnfValue.rule_of_view .typeAliasDecl raw
    have resultEq : executeTopItemRoot file tokens origin finish
        ready.1 ready.2.1 input =
          sourceLoc witness (.typeAliasDecl declaration) := by
      rw [executeTopItemRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .topItemTypeAlias origin finish declaration witness
  · let declaration := EbnfValue.ruleView .classDecl raw
    have rawEq := EbnfValue.rule_of_view .classDecl raw
    have resultEq : executeTopItemRoot file tokens origin finish
        ready.1 ready.2.1 input =
          sourceLoc witness (.classDecl declaration) := by
      rw [executeTopItemRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .topItemClass origin finish declaration witness
  · let declaration := EbnfValue.ruleView .instanceDecl raw
    have rawEq := EbnfValue.rule_of_view .instanceDecl raw
    have resultEq : executeTopItemRoot file tokens origin finish
        ready.1 ready.2.1 input =
          sourceLoc witness (.instanceDecl declaration) := by
      rw [executeTopItemRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .topItemInstance origin finish declaration witness
  · let declaration := EbnfValue.ruleView .contractDecl raw
    have rawEq := EbnfValue.rule_of_view .contractDecl raw
    have resultEq : executeTopItemRoot file tokens origin finish
        ready.1 ready.2.1 input =
          sourceLoc witness (.contractDecl declaration) := by
      rw [executeTopItemRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .topItemContract origin finish declaration witness
  · let declaration := EbnfValue.ruleView .functionDecl raw
    have rawEq := EbnfValue.rule_of_view .functionDecl raw
    have resultEq : executeTopItemRoot file tokens origin finish
        ready.1 ready.2.1 input =
          sourceLoc witness (.functionDecl declaration) := by
      rw [executeTopItemRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .topItemFunction origin finish declaration witness

private theorem ruleAtoms_of_views
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId)
    (inputs : List
      (EbnfValue file tokens (.atom (.nonterminal rule)))) :
    (inputs.map (EbnfValue.ruleView rule)).map
        (EbnfValue.ruleAtom rule) = inputs := by
  induction inputs with
  | nil => rfl
  | cons head tail induction =>
      simp [EbnfValue.rule_of_view, induction]

/-- The module executor realizes the exact complete-file source-rule
reduction. -/
theorem executeModuleRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .module origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .module)) :
    RuleReduction file tokens .module origin finish input
      (executeModuleRoot file input) := by
  let itemAtom : EbnfExpr := .atom (.nonterminal .topItem)
  let eofAtom : EbnfExpr := .atom (.terminal .endOfFile)
  let children : List EbnfExpr := [.star itemAtom, eofAtom]
  change EbnfValue file tokens (.sequence children) at input
  let values := EbnfValue.sequenceView children input
  let first := EbnfValues.consView (.star itemAtom) [eofAtom] values
  let rawStar := first.1
  let tail := first.2
  let second := EbnfValues.consView eofAtom [] tail
  let rawEof := second.1
  let nilTail := second.2
  let rawItems := EbnfValue.starView itemAtom rawStar
  let items := rawItems.map (EbnfValue.ruleView .topItem)
  let eof := EbnfValue.terminalView .endOfFile rawEof
  have itemsEq : items.map (EbnfValue.ruleAtom .topItem) = rawItems :=
    ruleAtoms_of_views .topItem rawItems
  have rawStarEq : EbnfValue.star itemAtom rawItems = rawStar :=
    EbnfValue.star_of_view itemAtom rawStar
  have rawEofEq : EbnfValue.terminalAtom .endOfFile eof = rawEof :=
    EbnfValue.terminal_of_view .endOfFile rawEof
  have nilEq : EbnfValues.nil = nilTail :=
    EbnfValues.nil_unique nilTail
  have tailEq : EbnfValues.cons eofAtom []
      (EbnfValue.terminalAtom .endOfFile eof) EbnfValues.nil = tail := by
    calc
      _ = EbnfValues.cons eofAtom [] rawEof nilTail := by
        rw [rawEofEq, nilEq]
      _ = EbnfValues.cons eofAtom [] second.1 second.2 := rfl
      _ = tail := EbnfValues.cons_of_view eofAtom [] tail
  have valuesEq : EbnfValues.cons (.star itemAtom) [eofAtom]
      (EbnfValue.star itemAtom
        (items.map (EbnfValue.ruleAtom .topItem)))
      (EbnfValues.cons eofAtom []
        (EbnfValue.terminalAtom .endOfFile eof) EbnfValues.nil) = values := by
    calc
      _ = EbnfValues.cons (.star itemAtom) [eofAtom] rawStar tail := by
        rw [itemsEq, rawStarEq, tailEq]
      _ = EbnfValues.cons (.star itemAtom) [eofAtom] first.1 first.2 := rfl
      _ = values := EbnfValues.cons_of_view (.star itemAtom) [eofAtom] values
  have inputEq : EbnfValue.sequence children
      (EbnfValues.cons (.star itemAtom) [eofAtom]
        (EbnfValue.star itemAtom
          (items.map (EbnfValue.ruleAtom .topItem)))
        (EbnfValues.cons eofAtom []
          (EbnfValue.terminalAtom .endOfFile eof) EbnfValues.nil)) = input := by
    calc
      _ = EbnfValue.sequence children values := by rw [valuesEq]
      _ = input := EbnfValue.sequence_of_view children input
  have resultEq : executeModuleRoot file input =
      executableModuleValue file items := by rfl
  have endpoints := ready.2.2 rfl
  rw [resultEq, ← inputEq]
  exact .module origin finish items eof endpoints.1 endpoints.2
    (matchedTerminal_eof_empty_span eof).2.1

private theorem ruleNonemptyAtoms_of_views
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId)
    (inputs : NonemptyList
      (EbnfValue file tokens (.atom (.nonterminal rule)))) :
    (inputs.map (EbnfValue.ruleView rule)).map
        (EbnfValue.ruleAtom rule) = inputs := by
  cases inputs with
  | mk head tail =>
      simp only [NonemptyList.map, NonemptyList.mk.injEq]
      constructor
      · exact EbnfValue.rule_of_view rule head
      · induction tail with
        | nil => rfl
        | cons next rest induction =>
            simp [EbnfValue.rule_of_view, induction]

/-- The predicate-list executor realizes its exact root reduction. -/
theorem executePredicateListRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (_ready : RuleReductionReady file tokens .predicateList origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .predicateList)) :
    RuleReduction file tokens .predicateList origin finish input
      (executePredicateListRoot input) := by
  change EbnfValue file tokens
    (.list1 (.atom (.nonterminal .predicate))) at input
  let raw := EbnfValue.list1View
    (.atom (.nonterminal .predicate)) input
  let predicates := raw.map (EbnfValue.ruleView .predicate)
  have mappedEq : predicates.map (EbnfValue.ruleAtom .predicate) = raw :=
    ruleNonemptyAtoms_of_views .predicate raw
  have inputEq : EbnfValue.list1 (.atom (.nonterminal .predicate))
      (predicates.map (EbnfValue.ruleAtom .predicate)) = input := by
    rw [mappedEq]
    exact EbnfValue.list1_of_view _ input
  have resultEq : executePredicateListRoot input = predicates := by rfl
  rw [resultEq, ← inputEq]
  exact .predicateList origin finish predicates

/-- The instance-method executor realizes its transparent root reduction. -/
theorem executeInstanceMethodRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (_ready : RuleReductionReady file tokens .instanceMethod origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .instanceMethod)) :
    RuleReduction file tokens .instanceMethod origin finish input
      (executeInstanceMethodRoot input) := by
  change EbnfValue file tokens (.atom (.nonterminal .functionDecl)) at input
  let value := EbnfValue.ruleView .functionDecl input
  have inputEq := EbnfValue.rule_of_view .functionDecl input
  have resultEq : executeInstanceMethodRoot input = value := by rfl
  rw [resultEq, ← inputEq]
  exact .instanceMethod origin finish value

/-- The arm-statement executor realizes its transparent root reduction. -/
theorem executeArmStatementRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (_ready : RuleReductionReady file tokens .armStatement origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .armStatement)) :
    RuleReduction file tokens .armStatement origin finish input
      (executeArmStatementRoot input) := by
  change EbnfValue file tokens (.atom (.nonterminal .statement)) at input
  let statement := EbnfValue.ruleView .statement input
  have inputEq := EbnfValue.rule_of_view .statement input
  have resultEq : executeArmStatementRoot input = statement := by rfl
  rw [resultEq, ← inputEq]
  exact .armStatement origin finish statement

/-- The terminal-expression executor realizes its transparent reduction. -/
theorem executeTerminalExpressionRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (_ready : RuleReductionReady file tokens .terminalExpression
      origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .terminalExpression)) :
    RuleReduction file tokens .terminalExpression origin finish input
      (executeTerminalExpressionRoot input) := by
  change EbnfValue file tokens (.atom (.nonterminal .expression)) at input
  let expression := EbnfValue.ruleView .expression input
  have inputEq := EbnfValue.rule_of_view .expression input
  have resultEq : executeTerminalExpressionRoot input = expression := by rfl
  rw [resultEq, ← inputEq]
  exact .terminalExpression origin finish expression

/-- The expression executor realizes its transparent annotation reduction. -/
theorem executeExpressionRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (_ready : RuleReductionReady file tokens .expression origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .expression)) :
    RuleReduction file tokens .expression origin finish input
      (executeExpressionRoot input) := by
  change EbnfValue file tokens (.atom (.nonterminal .annotation)) at input
  let expression := EbnfValue.ruleView .annotation input
  have inputEq := EbnfValue.rule_of_view .annotation input
  have resultEq : executeExpressionRoot input = expression := by rfl
  rw [resultEq, ← inputEq]
  exact .expression origin finish expression

/-- The block-statement executor realizes its exact root reduction. -/
theorem executeBlockStatementRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .blockStatement origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .blockStatement)) :
    RuleReduction file tokens .blockStatement origin finish input
      (executeBlockStatementRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  change EbnfValue file tokens (.atom (.nonterminal .body)) at input
  let body := EbnfValue.ruleView .body input
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have inputEq := EbnfValue.rule_of_view .body input
  have resultEq : executeBlockStatementRoot file tokens origin finish
      ready.1 ready.2.1 input = sourceLoc witness (.block body) := by rfl
  rw [resultEq, ← inputEq]
  exact .blockStatement origin finish body witness

/-- The function-declaration executor realizes its exact root reduction. -/
theorem executeFunctionDeclRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .functionDecl origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .functionDecl)) :
    RuleReduction file tokens .functionDecl origin finish input
      (executeFunctionDeclRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let signatureAtom : EbnfExpr := .atom (.nonterminal .functionSignature)
  let bodyAtom : EbnfExpr := .atom (.nonterminal .body)
  change EbnfValue file tokens (.sequence [signatureAtom, bodyAtom]) at input
  let viewed := EbnfValue.sequence2View signatureAtom bodyAtom input
  let signature := EbnfValue.ruleView .functionSignature viewed.1
  let body := EbnfValue.ruleView .body viewed.2
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have inputEq := EbnfValue.sequence2_of_view signatureAtom bodyAtom input
  have signatureEq := EbnfValue.rule_of_view .functionSignature viewed.1
  have bodyEq := EbnfValue.rule_of_view .body viewed.2
  have resultEq : executeFunctionDeclRoot file tokens origin finish
      ready.1 ready.2.1 input = sourceLoc witness {
        signature := signature
        body := body
      } := by rfl
  rw [resultEq, ← inputEq, ← signatureEq, ← bodyEq]
  exact .functionDecl origin finish signature body witness

/-- The class-method executor realizes its exact root reduction. -/
theorem executeClassMethodRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .classMethod origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .classMethod)) :
    RuleReduction file tokens .classMethod origin finish input
      (executeClassMethodRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let signatureAtom : EbnfExpr := .atom (.nonterminal .functionSignature)
  let semicolonAtom : EbnfExpr := .atom (.terminal (.symbol .semicolon))
  change EbnfValue file tokens
    (.sequence [signatureAtom, semicolonAtom]) at input
  let viewed := EbnfValue.sequence2View signatureAtom semicolonAtom input
  let signature := EbnfValue.ruleView .functionSignature viewed.1
  let semicolon := EbnfValue.terminalView (.symbol .semicolon) viewed.2
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have inputEq := EbnfValue.sequence2_of_view signatureAtom semicolonAtom input
  have signatureEq := EbnfValue.rule_of_view .functionSignature viewed.1
  have semicolonEq := EbnfValue.terminal_of_view (.symbol .semicolon) viewed.2
  have resultEq : executeClassMethodRoot file tokens origin finish
      ready.1 ready.2.1 input = sourceLoc witness {
        signature := signature
        terminator := semicolon.span
      } := by rfl
  rw [resultEq, ← inputEq, ← signatureEq, ← semicolonEq]
  exact .classMethod origin finish signature semicolon witness

/-- The let-statement executor realizes its exact root reduction. -/
theorem executeLetStatementRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .letStatement origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .letStatement)) :
    RuleReduction file tokens .letStatement origin finish input
      (executeLetStatementRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let bindingAtom : EbnfExpr := .atom (.nonterminal .letBinding)
  let semicolonAtom : EbnfExpr := .atom (.terminal (.symbol .semicolon))
  change EbnfValue file tokens (.sequence [bindingAtom, semicolonAtom]) at input
  let viewed := EbnfValue.sequence2View bindingAtom semicolonAtom input
  let binding := EbnfValue.ruleView .letBinding viewed.1
  let semicolon := EbnfValue.terminalView (.symbol .semicolon) viewed.2
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have inputEq := EbnfValue.sequence2_of_view bindingAtom semicolonAtom input
  have bindingEq := EbnfValue.rule_of_view .letBinding viewed.1
  have semicolonEq := EbnfValue.terminal_of_view (.symbol .semicolon) viewed.2
  have resultEq : executeLetStatementRoot file tokens origin finish
      ready.1 ready.2.1 input = sourceLoc witness (.letBinding binding) := by
    rfl
  rw [resultEq, ← inputEq, ← bindingEq, ← semicolonEq]
  exact .letStatement origin finish binding semicolon witness

/-- The break-statement executor realizes its exact root reduction. -/
theorem executeBreakStatementRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .breakStatement origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .breakStatement)) :
    RuleReduction file tokens .breakStatement origin finish input
      (executeBreakStatementRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let keywordAtom : EbnfExpr := .atom (.terminal (.hardKeyword .breakKw))
  let semicolonAtom : EbnfExpr := .atom (.terminal (.symbol .semicolon))
  change EbnfValue file tokens (.sequence [keywordAtom, semicolonAtom]) at input
  let viewed := EbnfValue.sequence2View keywordAtom semicolonAtom input
  let keyword := EbnfValue.terminalView (.hardKeyword .breakKw) viewed.1
  let semicolon := EbnfValue.terminalView (.symbol .semicolon) viewed.2
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have inputEq := EbnfValue.sequence2_of_view keywordAtom semicolonAtom input
  have keywordEq := EbnfValue.terminal_of_view (.hardKeyword .breakKw) viewed.1
  have semicolonEq := EbnfValue.terminal_of_view (.symbol .semicolon) viewed.2
  have resultEq : executeBreakStatementRoot file tokens origin finish
      ready.1 ready.2.1 input = sourceLoc witness (.break semicolon.span) := by
    rfl
  rw [resultEq, ← inputEq, ← keywordEq, ← semicolonEq]
  exact .breakStatement origin finish keyword semicolon witness

/-- The continue-statement executor realizes its exact root reduction. -/
theorem executeContinueStatementRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .continueStatement origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .continueStatement)) :
    RuleReduction file tokens .continueStatement origin finish input
      (executeContinueStatementRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let keywordAtom : EbnfExpr := .atom (.terminal (.hardKeyword .continueKw))
  let semicolonAtom : EbnfExpr := .atom (.terminal (.symbol .semicolon))
  change EbnfValue file tokens (.sequence [keywordAtom, semicolonAtom]) at input
  let viewed := EbnfValue.sequence2View keywordAtom semicolonAtom input
  let keyword := EbnfValue.terminalView (.hardKeyword .continueKw) viewed.1
  let semicolon := EbnfValue.terminalView (.symbol .semicolon) viewed.2
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have inputEq := EbnfValue.sequence2_of_view keywordAtom semicolonAtom input
  have keywordEq :=
    EbnfValue.terminal_of_view (.hardKeyword .continueKw) viewed.1
  have semicolonEq := EbnfValue.terminal_of_view (.symbol .semicolon) viewed.2
  have resultEq : executeContinueStatementRoot file tokens origin finish
      ready.1 ready.2.1 input = sourceLoc witness (.continue semicolon.span) := by
    rfl
  rw [resultEq, ← inputEq, ← keywordEq, ← semicolonEq]
  exact .continueStatement origin finish keyword semicolon witness

/-- Every supported root executor realizes its exact source-rule reduction. -/
theorem executeRootRule_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId)
    (executable : ExecutableRootRule rule)
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens rule origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs rule)) :
    RuleReduction file tokens rule origin finish input
      (executeRootRule file tokens origin finish rule executable
        ready.1 ready.2.1 input) := by
  cases executable with
  | module => exact executeModuleRoot_reduces origin finish ready input
  | topItem => exact executeTopItemRoot_reduces origin finish ready input
  | optionalComma =>
      exact executeOptionalCommaRoot_reduces origin finish ready input
  | predicateList =>
      exact executePredicateListRoot_reduces origin finish ready input
  | instanceMethod =>
      exact executeInstanceMethodRoot_reduces origin finish ready input
  | armStatement =>
      exact executeArmStatementRoot_reduces origin finish ready input
  | terminalExpression =>
      exact executeTerminalExpressionRoot_reduces origin finish ready input
  | expression =>
      exact executeExpressionRoot_reduces origin finish ready input
  | blockStatement =>
      exact executeBlockStatementRoot_reduces origin finish ready input
  | functionDecl =>
      exact executeFunctionDeclRoot_reduces origin finish ready input
  | classMethod =>
      exact executeClassMethodRoot_reduces origin finish ready input
  | letStatement =>
      exact executeLetStatementRoot_reduces origin finish ready input
  | breakStatement =>
      exact executeBreakStatementRoot_reduces origin finish ready input
  | continueStatement =>
      exact executeContinueStatementRoot_reduces origin finish ready input

end Solcore.Surface.Multi

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace
open Grammar

/-- Every supported root action tuple computes the exact result admitted by
the declarative action relation. -/
theorem executeRootAction_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId)
    (executable : ExecutableRootRule rule)
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens rule origin finish)
    (input : GrammarSymbolValues file tokens (ProductionId.root rule).rhs) :
    ActionReduces file tokens (.actionFor (.root rule)) origin finish input
      (executeRootAction file tokens origin finish rule executable
        ready.1 ready.2.1 input) := by
  exact .root rule origin finish input _
    (executeRootRule_reduces rule executable origin finish ready
      (RootAction.unpack rule input))

/-- The executable root result is the unique declarative action result. -/
theorem ActionReduces.eq_executeRootAction
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId}
    (executable : ExecutableRootRule rule)
    {origin finish : Boundary tokens}
    (ready : RuleReductionReady file tokens rule origin finish)
    {input : GrammarSymbolValues file tokens (ProductionId.root rule).rhs}
    {output : NonterminalValue file tokens (ProductionId.root rule).lhs}
    (reduces : ActionReduces file tokens (.actionFor (.root rule))
      origin finish input output) :
    output = executeRootAction file tokens origin finish rule executable
      ready.1 ready.2.1 input :=
  ActionReduces.functional reduces
    (executeRootAction_reduces rule executable origin finish ready input)

end Solcore.Surface.Multi
namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

private theorem contextualReach_enabledProductionInstance
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {item : ContextualItemKey tokens}
    (reached : ContextualReach file tokens memo correct final item) :
    EnabledProductionInstance file tokens memo correct final {
      production := item.raw.production
      origin := item.raw.origin
      context := item.context
    } := by
  induction reached with
  | root =>
      intro guard polarity member
      simp [guardOf] at member
  | predict waiting predicted reached next enabled induction =>
      exact enabled
  | scan before after cursor reached structural induction =>
      rcases structural.1 with
        ⟨terminal, value, span, next, atCurrent, terminalAt,
          matched, advance⟩
      rw [advance.1, advance.2.2.1, ← structural.2]
      exact induction
  | complete waiting finished after shared waitingReached finishedReached
      structural waitingInduction finishedInduction =>
      rcases structural.1 with
        ⟨symbol, next, complete, lhs, waitingAt, finishedAt, advance⟩
      rw [advance.1, advance.2.2.1, structural.2.2]
      exact waitingInduction

/-- At the greatest boundary selected by a successful observed execution,
Chart's proof-free membership bit is exactly declarative expected-frontier
membership. -/
theorem executeObservedContextualWorklist?_expectedAtCurrentMemberBool_eq_true_iff
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result)
    (cursor : Boundary tokens)
    (greatestSelected : result.greatestCurrent? = some cursor)
    (expected : Expected) :
    result.expectedAtCurrentMemberBool cursor expected = true ↔
      let correct := executeObservedContextualWorklist?_phaseBCorrect
        file tokens owned result selected
      let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
        file tokens owned result selected
      ExpectedMember file tokens result.memo correct final cursor expected := by
  let correct := executeObservedContextualWorklist?_phaseBCorrect
    file tokens owned result selected
  let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
    file tokens owned result selected
  change result.expectedAtCurrentMemberBool cursor expected = true ↔
    ExpectedMember file tokens result.memo correct final cursor expected
  have greatest : GreatestReachableCursor
      file tokens result.memo correct final cursor :=
    (executeObservedContextualWorklist?_greatestCurrent?_eq_some_iff
      file tokens owned result selected cursor).mp greatestSelected
  have correspondence :=
    executeObservedContextualWorklist?_correspondence
      file tokens owned result selected
  change
    (∀ item, item ∈ result.items ↔
      ContextualReach file tokens result.memo correct final item) ∧ _ ∧ _
      at correspondence
  rw [Chart.ContextualWorklistResult.expectedAtCurrentMemberBool_eq_true_iff]
  constructor
  · rintro ⟨item, member, currentEq, terminal, next, equality⟩
    have reached := (correspondence.1 item).mp member
    exact ⟨item, terminal, ⟨greatest, reached, currentEq⟩,
      next, contextualReach_enabledProductionInstance reached, equality⟩
  · rintro ⟨item, terminal, frontier, next, enabled, equality⟩
    exact ⟨item, (correspondence.1 item).mpr frontier.2.1,
      frontier.2.2, terminal, next, equality⟩

/-- Membership in Chart's stable expected list is exactly declarative
expected-frontier membership. -/
theorem executeObservedContextualWorklist?_expectedAtCurrent_mem_iff
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result)
    (cursor : Boundary tokens)
    (greatestSelected : result.greatestCurrent? = some cursor)
    (expected : Expected) :
    expected ∈ result.expectedAtCurrent cursor ↔
      let correct := executeObservedContextualWorklist?_phaseBCorrect
        file tokens owned result selected
      let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
        file tokens owned result selected
      ExpectedMember file tokens result.memo correct final cursor expected := by
  simp only [Chart.ContextualWorklistResult.expectedAtCurrent,
    List.mem_filter, allExpected_complete, true_and]
  exact executeObservedContextualWorklist?_expectedAtCurrentMemberBool_eq_true_iff
      file tokens owned result selected cursor greatestSelected expected

/-- A selected proof-free expected frontier is exactly the greatest
declarative cursor paired with its complete expected-terminal union. -/
theorem executeObservedContextualWorklist?_expectedFrontier?_eq_some_iff
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result)
    (frontier : Chart.ExpectedFrontier tokens) :
    result.expectedFrontier? = some frontier ↔
      let correct := executeObservedContextualWorklist?_phaseBCorrect
        file tokens owned result selected
      let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
        file tokens owned result selected
      ∃ greatest : GreatestReachableCursor
          file tokens result.memo correct final frontier.cursor,
        frontier.expected = canonicalExpectedValues
          owned correct final frontier.cursor greatest := by
  let correct := executeObservedContextualWorklist?_phaseBCorrect
    file tokens owned result selected
  let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
    file tokens owned result selected
  change result.expectedFrontier? = some frontier ↔
    ∃ greatest : GreatestReachableCursor
        file tokens result.memo correct final frontier.cursor,
      frontier.expected = canonicalExpectedValues
        owned correct final frontier.cursor greatest
  rw [Chart.ContextualWorklistResult.expectedFrontier?_eq_some_iff]
  constructor
  · rintro ⟨greatestSelected, expectedEq⟩
    let greatest :=
      (executeObservedContextualWorklist?_greatestCurrent?_eq_some_iff
        file tokens owned result selected frontier.cursor).mp greatestSelected
    have computedEq : result.expectedAtCurrent frontier.cursor =
        canonicalExpectedValues
          owned correct final frontier.cursor greatest := by
      unfold Chart.ContextualWorklistResult.expectedAtCurrent
      unfold canonicalExpectedValues
      apply List.filter_congr
      intro expected _member
      letI : Decidable (ExpectedMember file tokens result.memo correct final
          frontier.cursor expected) :=
        expectedMemberDecision
          owned correct final frontier.cursor greatest expected
      apply Bool.eq_iff_iff.mpr
      rw [executeObservedContextualWorklist?_expectedAtCurrentMemberBool_eq_true_iff
          file tokens owned result selected frontier.cursor
            greatestSelected expected]
      rw [decide_eq_true_iff]
    exact ⟨greatest, expectedEq.trans computedEq⟩
  · rintro ⟨greatest, expectedEq⟩
    have greatestSelected : result.greatestCurrent? =
        some frontier.cursor :=
      (executeObservedContextualWorklist?_greatestCurrent?_eq_some_iff
        file tokens owned result selected frontier.cursor).mpr greatest
    have computedEq : result.expectedAtCurrent frontier.cursor =
        canonicalExpectedValues
          owned correct final frontier.cursor greatest := by
      unfold Chart.ContextualWorklistResult.expectedAtCurrent
      unfold canonicalExpectedValues
      apply List.filter_congr
      intro expected _member
      letI : Decidable (ExpectedMember file tokens result.memo correct final
          frontier.cursor expected) :=
        expectedMemberDecision
          owned correct final frontier.cursor greatest expected
      apply Bool.eq_iff_iff.mpr
      rw [executeObservedContextualWorklist?_expectedAtCurrentMemberBool_eq_true_iff
          file tokens owned result selected frontier.cursor
            greatestSelected expected]
      rw [decide_eq_true_iff]
    exact ⟨greatestSelected, expectedEq.trans computedEq.symm⟩

end Solcore.Surface.Multi

namespace Solcore.Surface.Multi

open Solcore.Workspace

/-- Every successful observed contextual execution exposes its computed
expected frontier. -/
theorem executeObservedContextualWorklist?_expectedFrontier?_exists
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result) :
    ∃ frontier, result.expectedFrontier? = some frontier := by
  rcases executeObservedContextualWorklist?_greatestCurrent?_exists
    file tokens owned result selected with ⟨cursor, cursorEq⟩
  let frontier : Chart.ExpectedFrontier tokens := {
    cursor := cursor
    expected := result.expectedAtCurrent cursor
  }
  exact ⟨frontier,
    (Chart.ContextualWorklistResult.expectedFrontier?_eq_some_iff
      result frontier).mpr ⟨cursorEq, rfl⟩⟩

/-- The absent expected-frontier branch is unreachable after successful
observed contextual execution. -/
theorem executeObservedContextualWorklist?_expectedFrontier?_ne_none
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result) :
    result.expectedFrontier? ≠ none := by
  rcases executeObservedContextualWorklist?_expectedFrontier?_exists
    file tokens owned result selected with ⟨frontier, frontierEq⟩
  intro noneEq
  rw [noneEq] at frontierEq
  contradiction

end Solcore.Surface.Multi
namespace Solcore.Surface.Multi

open Solcore.Workspace

/-- Chart's proof-free found observation is exactly the declarative retained
token-or-EOF relation. -/
theorem chart_observedFoundAt?_eq_some_iff
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (boundary : Boundary tokens)
    (observation : Chart.FoundObservation) :
    Chart.observedFoundAt? file tokens boundary = some observation ↔
      FoundAt file tokens boundary observation.span observation.found := by
  unfold Chart.observedFoundAt?
  split <;> rename_i inRange
  · let cursor : TerminalCursor tokens := ⟨boundary.val, by omega⟩
    have atBoundary : cursor.beforeBoundary = boundary := by
      exact Fin.ext rfl
    let token := tokens[boundary.val]
    let candidate : Chart.FoundObservation := {
      span := token.span
      found := .token token.payload
    }
    have candidateAt : FoundAt file tokens boundary
        candidate.span candidate.found := by
      exact .retained cursor boundary token atBoundary
        (.retained cursor token inRange
          (List.getElem?_eq_getElem inRange)
          (owned token (List.getElem_mem inRange)))
    constructor
    · intro selected
      have same : candidate = observation := Option.some.inj selected
      simpa only [same] using candidateAt
    · intro applies
      rcases FoundAt.functional candidateAt applies with
        ⟨spanEq, foundEq⟩
      apply congrArg some
      cases candidate
      cases observation
      simp only at spanEq foundEq ⊢
      cases spanEq
      cases foundEq
      rfl
  · split <;> rename_i atEnd
    · let cursor : TerminalCursor tokens := ⟨boundary.val, by omega⟩
      have atBoundary : cursor.beforeBoundary = boundary := by
        exact Fin.ext rfl
      let candidate : Chart.FoundObservation := {
        span := {
          source := file.id
          startByte := file.content.utf8ByteSize
          endByte := file.content.utf8ByteSize
        }
        found := .endOfFile
      }
      have candidateAt : FoundAt file tokens boundary
          candidate.span candidate.found := by
        exact .endOfFile cursor boundary atBoundary atEnd
      constructor
      · intro selected
        have same : candidate = observation := Option.some.inj selected
        simpa only [same] using candidateAt
      · intro applies
        rcases FoundAt.functional candidateAt applies with
          ⟨spanEq, foundEq⟩
        apply congrArg some
        cases candidate
        cases observation
        simp only at spanEq foundEq ⊢
        cases spanEq
        cases foundEq
        rfl
    · constructor
      · intro impossible
        contradiction
      · intro applies
        have atMost := FoundAt.boundary_le_logicalEOF applies
        omega

/-- A selected observed frontier carries exactly the greatest declarative
cursor, its canonical expected list, and its found token relation. -/
theorem executeObservedContextualWorklist?_observedFrontier?_eq_some_iff
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result)
    (frontier : Chart.ObservedFrontier tokens) :
    result.observedFrontier? file = some frontier ↔
      let correct := executeObservedContextualWorklist?_phaseBCorrect
        file tokens owned result selected
      let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
        file tokens owned result selected
      ∃ greatest : GreatestReachableCursor
          file tokens result.memo correct final frontier.cursor,
        frontier.expected = canonicalExpectedValues
          owned correct final frontier.cursor greatest ∧
          FoundAt file tokens frontier.cursor frontier.span frontier.found := by
  let correct := executeObservedContextualWorklist?_phaseBCorrect
    file tokens owned result selected
  let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
    file tokens owned result selected
  change result.observedFrontier? file = some frontier ↔
    ∃ greatest : GreatestReachableCursor
        file tokens result.memo correct final frontier.cursor,
      frontier.expected = canonicalExpectedValues
        owned correct final frontier.cursor greatest ∧
        FoundAt file tokens frontier.cursor frontier.span frontier.found
  unfold Chart.ContextualWorklistResult.observedFrontier?
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨expectedFrontier, expectedEq, observation,
      observationEq, frontierEq⟩
    cases frontierEq
    rcases
        (executeObservedContextualWorklist?_expectedFrontier?_eq_some_iff
          file tokens owned result selected expectedFrontier).mp expectedEq with
      ⟨greatest, canonical⟩
    exact ⟨greatest, canonical,
      (chart_observedFoundAt?_eq_some_iff
        owned expectedFrontier.cursor observation).mp observationEq⟩
  · rintro ⟨greatest, canonical, foundAt⟩
    let expectedFrontier : Chart.ExpectedFrontier tokens := {
      cursor := frontier.cursor
      expected := frontier.expected
    }
    let observation : Chart.FoundObservation := {
      span := frontier.span
      found := frontier.found
    }
    refine ⟨expectedFrontier, ?_, observation, ?_, ?_⟩
    · exact
        (executeObservedContextualWorklist?_expectedFrontier?_eq_some_iff
          file tokens owned result selected expectedFrontier).mpr
            ⟨greatest, canonical⟩
    · exact (chart_observedFoundAt?_eq_some_iff
        owned frontier.cursor observation).mpr foundAt
    · cases frontier
      rfl

end Solcore.Surface.Multi
namespace Solcore.Surface.Multi

open Solcore.Workspace

private theorem canonicalExpected_list_eq_values
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (cursor : Boundary tokens)
    (greatest : GreatestReachableCursor
      file tokens memo correct final cursor)
    (expected : NonemptyList Expected)
    (canonical : CanonicalExpected
      file tokens memo correct final cursor expected) :
    expected.head :: expected.tail =
      canonicalExpectedValues owned correct final cursor greatest := by
  cases selected : canonicalExpectedValues
      owned correct final cursor greatest with
  | nil =>
      have headMember : ExpectedMember
          file tokens memo correct final cursor expected.head :=
        (canonical.1 expected.head).mp (by simp)
      have selectedMember :=
        (chart_expected_is_frontier_union
          owned correct final cursor greatest expected.head).mpr headMember
      rw [selected] at selectedMember
      contradiction
  | cons head tail =>
      let other : NonemptyList Expected := { head := head, tail := tail }
      have valuesNodup :
          (canonicalExpectedValues
            owned correct final cursor greatest).Nodup := by
        unfold canonicalExpectedValues
        exact List.Pairwise.filter _ allExpected_nodup
      have valuesSorted :
          (canonicalExpectedValues owned correct final cursor greatest).Pairwise
            (fun left right => Expected.compare left right = .lt) := by
        unfold canonicalExpectedValues
        exact List.Pairwise.filter _ allExpected_sorted
      have otherCanonical : CanonicalExpected
          file tokens memo correct final cursor other := by
        unfold CanonicalExpected
        constructor
        · intro candidate
          have exact := chart_expected_is_frontier_union
            owned correct final cursor greatest candidate
          simpa only [other, selected] using exact
        · constructor
          · simpa only [other, selected] using valuesNodup
          · simpa only [other, selected] using valuesSorted
      have same := canonicalExpected_sorted_nodup_unique
        canonical otherCanonical
      have listSame := congrArg
        (fun values : NonemptyList Expected => values.head :: values.tail)
        same
      simpa only [other, selected] using listSame

/-- The executable unexpected-token candidate is exactly a greatest cursor
with canonical nonempty expectations and the declarative found observation.
Root absence and repeated-nonassociative exclusion remain later premises. -/
theorem executeObservedContextualWorklist?_unexpectedDiagnosticCandidate?_eq_some_iff
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result)
    (span : SourceSpan) (found : Found)
    (expected : NonemptyList Expected) :
    result.unexpectedDiagnosticCandidate? file =
        some (.unexpected span found expected) ↔
      let correct := executeObservedContextualWorklist?_phaseBCorrect
        file tokens owned result selected
      let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
        file tokens owned result selected
      ∃ cursor : Boundary tokens,
        GreatestReachableCursor
            file tokens result.memo correct final cursor ∧
          CanonicalExpected
            file tokens result.memo correct final cursor expected ∧
          FoundAt file tokens cursor span found := by
  let correct := executeObservedContextualWorklist?_phaseBCorrect
    file tokens owned result selected
  let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
    file tokens owned result selected
  change result.unexpectedDiagnosticCandidate? file =
      some (.unexpected span found expected) ↔
    ∃ cursor : Boundary tokens,
      GreatestReachableCursor
          file tokens result.memo correct final cursor ∧
        CanonicalExpected
          file tokens result.memo correct final cursor expected ∧
        FoundAt file tokens cursor span found
  unfold Chart.ContextualWorklistResult.unexpectedDiagnosticCandidate?
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨frontier, frontierEq, unexpectedEq⟩
    rcases (Chart.ObservedFrontier.unexpected?_eq_some_iff
      frontier span found expected).mp unexpectedEq with
      ⟨spanEq, foundEq, expectedEq⟩
    rcases
        (executeObservedContextualWorklist?_observedFrontier?_eq_some_iff
          file tokens owned result selected frontier).mp frontierEq with
      ⟨greatest, canonicalValuesEq, foundAt⟩
    have listEq : expected.head :: expected.tail =
        canonicalExpectedValues owned correct final frontier.cursor greatest :=
      expectedEq.symm.trans canonicalValuesEq
    have canonical : CanonicalExpected file tokens result.memo correct final
        frontier.cursor expected := by
      unfold CanonicalExpected
      constructor
      · intro candidate
        have exact := chart_expected_is_frontier_union
          owned correct final frontier.cursor greatest candidate
        rw [← listEq] at exact
        exact exact
      · constructor
        · rw [listEq]
          unfold canonicalExpectedValues
          exact List.Pairwise.filter _ allExpected_nodup
        · rw [listEq]
          unfold canonicalExpectedValues
          exact List.Pairwise.filter _ allExpected_sorted
    refine ⟨frontier.cursor, greatest, canonical, ?_⟩
    simpa only [spanEq, foundEq] using foundAt
  · rintro ⟨cursor, greatest, canonical, foundAt⟩
    have expectedEq := canonicalExpected_list_eq_values
      owned correct final cursor greatest expected canonical
    let frontier : Chart.ObservedFrontier tokens := {
      cursor := cursor
      span := span
      found := found
      expected := expected.head :: expected.tail
    }
    refine ⟨frontier, ?_, ?_⟩
    · exact
        (executeObservedContextualWorklist?_observedFrontier?_eq_some_iff
          file tokens owned result selected frontier).mpr
            ⟨greatest, by simpa only [frontier] using expectedEq, by
              simpa only [frontier] using foundAt⟩
    · exact (Chart.ObservedFrontier.unexpected?_eq_some_iff
        frontier span found expected).mpr (by simp [frontier])

end Solcore.Surface.Multi
