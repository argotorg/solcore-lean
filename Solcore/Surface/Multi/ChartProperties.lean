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


end Solcore.Surface.Multi
