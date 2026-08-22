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
