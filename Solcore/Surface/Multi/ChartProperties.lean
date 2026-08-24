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

open Grammar
open Solcore.Workspace

private theorem memoEnablesProduction_iff_enabled_multi
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

private theorem operationalContextualReach_sound_multi
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
        ((memoEnablesProduction_iff_enabled_multi correct final _).mp enabled)
  | scan before after cursor _ structural beforeInduction =>
      exact ContextualReach.scan before after cursor beforeInduction structural
  | complete waiting finished after shared _ _ structural
      waitingInduction finishedInduction =>
      exact ContextualReach.complete waiting finished after shared
        waitingInduction finishedInduction structural

private theorem operationalContextualEdgeReach_sound_multi
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
        exact ⟨operationalContextualReach_sound_multi correct final endpoints.1,
          operationalContextualReach_sound_multi correct final endpoints.2⟩
    | completed waiting finished after shared =>
        exact ⟨operationalContextualReach_sound_multi correct final endpoints.1,
          operationalContextualReach_sound_multi correct final endpoints.2.1,
          operationalContextualReach_sound_multi correct final endpoints.2.2⟩

private theorem contextualReach_operational_multi
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
          ((memoEnablesProduction_iff_enabled_multi correct final _).mpr enabled)
  | scan before after cursor _ structural beforeInduction =>
      exact Chart.OperationalContextualReach.scan before after cursor
        beforeInduction structural
  | complete waiting finished after shared _ _ structural
      waitingInduction finishedInduction =>
      exact Chart.OperationalContextualReach.complete waiting finished after
        shared waitingInduction finishedInduction structural

private theorem contextualEdgeReach_operational_multi
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
        exact ⟨contextualReach_operational_multi correct final endpoints.1,
          contextualReach_operational_multi correct final endpoints.2⟩
    | completed waiting finished after shared =>
        exact ⟨contextualReach_operational_multi correct final endpoints.1,
          contextualReach_operational_multi correct final endpoints.2.1,
          contextualReach_operational_multi correct final endpoints.2.2⟩

/-- The total multi-ledger executor preserves the unified semantic memo. -/
theorem executeObservedContextualWorklistMulti?_memo_eq_semantic
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklistMulti?
      file tokens owned = some result) :
    result.memo = semanticGuardMemo owned :=
  (Chart.executeObservedContextualWorklistMulti?_memo_eq_saturated
    file tokens owned result selected).trans
      (saturatedGuardMemo_eq_semantic owned)

/-- Every total multi-ledger result carries a correct Phase-B memo. -/
theorem executeObservedContextualWorklistMulti?_phaseBCorrect
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklistMulti?
      file tokens owned = some result) :
    PhaseBCorrect file tokens result.memo := by
  rw [executeObservedContextualWorklistMulti?_memo_eq_semantic
    file tokens owned result selected]
  exact semanticGuardMemo_correct owned

/-- Multi-ledger execution is declaratively sound without any backpointer
uniqueness premise. -/
theorem executeObservedContextualWorklistMulti?_sound
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklistMulti?
      file tokens owned = some result) :
    let correct := executeObservedContextualWorklistMulti?_phaseBCorrect
      file tokens owned result selected
    let final := Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
      file tokens owned result selected
    (forall item, item ∈ result.items ->
      ContextualReach file tokens result.memo correct final item) ∧
    (forall edge, edge ∈ result.edges ->
      ContextualEdgeReach file tokens result.memo correct final edge.val) := by
  let correct := executeObservedContextualWorklistMulti?_phaseBCorrect
    file tokens owned result selected
  let final := Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
    file tokens owned result selected
  have operational :=
    Chart.executeObservedContextualWorklistMulti?_operational_sound
      file tokens owned result selected
  exact ⟨fun item member =>
      operationalContextualReach_sound_multi correct final
        (operational.1 item member),
    fun edge member =>
      operationalContextualEdgeReach_sound_multi correct final
        (operational.2 edge member)⟩

/-- Operational closure upgrades the multi-ledger result to exact item/edge
correspondence.  Multiple completed edges for one target remain represented;
no completion-backpointer uniqueness conclusion is made. -/
theorem
    executeObservedContextualWorklistMulti?_correspondence_of_operationalClosure
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklistMulti?
      file tokens owned = some result)
    (closed : Chart.OperationalContextualClosure file tokens result.memo
      result.items result.edges) :
    let correct := executeObservedContextualWorklistMulti?_phaseBCorrect
      file tokens owned result selected
    let final := Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
      file tokens owned result selected
    (forall item, item ∈ result.items <->
      ContextualReach file tokens result.memo correct final item) ∧
    (forall key, (∃ retained, retained ∈ result.edges ∧
        retained.val = key) <->
      ContextualEdgeReach file tokens result.memo correct final key) := by
  let correct := executeObservedContextualWorklistMulti?_phaseBCorrect
    file tokens owned result selected
  let final := Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
    file tokens owned result selected
  have sound := executeObservedContextualWorklistMulti?_sound
    file tokens owned result selected
  refine ⟨?_, ?_⟩
  · intro item
    exact ⟨sound.1 item, fun reached => closed.reach_complete
      (contextualReach_operational_multi correct final reached)⟩
  · intro key
    constructor
    · rintro ⟨retained, member, rfl⟩
      exact sound.2 retained member
    · intro reached
      exact closed.edge_complete
        (contextualEdgeReach_operational_multi correct final reached)

/-- Total multi-ledger execution has exact declarative item/edge
correspondence.  This deliberately does not assert a unique completion
backpointer for edges sharing one target. -/
theorem executeObservedContextualWorklistMulti?_correspondence
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklistMulti?
      file tokens owned = some result) :
    let correct := executeObservedContextualWorklistMulti?_phaseBCorrect
      file tokens owned result selected
    let final := Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
      file tokens owned result selected
    (forall item, item ∈ result.items <->
      ContextualReach file tokens result.memo correct final item) ∧
    (forall key, (∃ retained, retained ∈ result.edges ∧
        retained.val = key) <->
      ContextualEdgeReach file tokens result.memo correct final key) :=
  executeObservedContextualWorklistMulti?_correspondence_of_operationalClosure
    file tokens owned result selected
      (Chart.executeObservedContextualWorklistMulti?_operationalClosure
        file tokens owned result selected)

end Solcore.Surface.Multi

namespace Solcore.Surface.Multi

open Solcore.Workspace

/-- The total multi-ledger executor's completed-module-root bit is exactly
declarative reachability of the canonical whole-file module item. -/
theorem
    executeObservedContextualWorklistMulti?_containsCompleteModuleRootItem_eq_true_iff
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklistMulti?
      file tokens owned = some result) :
    result.containsCompleteModuleRootItem = true ↔
      ContextualReach file tokens result.memo
        (executeObservedContextualWorklistMulti?_phaseBCorrect
          file tokens owned result selected)
        (Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
          file tokens owned result selected)
        (CanonicalCompleteRootItem tokens .module
          (Boundary.start tokens) (Boundary.afterLogicalEOF tokens) .plain) := by
  rw [Chart.ContextualWorklistResult.containsCompleteModuleRootItem_eq_true_iff]
  exact (executeObservedContextualWorklistMulti?_correspondence
    file tokens owned result selected).1 _

/-- Every declarative source-backed module forces the proof-free completed
module-root bit in the total multi-ledger result. -/
theorem
    executeObservedContextualWorklistMulti?_containsCompleteModuleRootItem_eq_true_of_sourceBackedRoot
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklistMulti?
      file tokens owned = some result)
    (module : ParsedModuleV1)
    (sourceRoot : SourceBackedRoot file tokens module) :
    result.containsCompleteModuleRootItem = true := by
  rcases sourceRoot with
    ⟨memo, correct, final, reached, _complete, _coherent⟩
  let resultCorrect :=
    executeObservedContextualWorklistMulti?_phaseBCorrect
      file tokens owned result selected
  let resultFinal :=
    Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
      file tokens owned result selected
  have memoEq : memo = result.memo :=
    phaseBCorrect_final_memo_unique
      correct final resultCorrect resultFinal
  subst memo
  have reachedResult : ContextualReach file tokens result.memo
      resultCorrect resultFinal
      (CanonicalCompleteRootItem tokens .module
        (Boundary.start tokens) (Boundary.afterLogicalEOF tokens) .plain) :=
    reached
  exact
    (executeObservedContextualWorklistMulti?_containsCompleteModuleRootItem_eq_true_iff
      file tokens owned result selected).mpr reachedResult

/-- A false completed-module-root bit rules out every declarative
source-backed module in the total multi-ledger result. -/
theorem
    executeObservedContextualWorklistMulti?_noSourceBackedRoot_of_completeModuleRootItem_eq_false
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklistMulti?
      file tokens owned = some result)
    (absent : result.containsCompleteModuleRootItem = false) :
    ¬ ∃ module, SourceBackedRoot file tokens module := by
  rintro ⟨module, sourceRoot⟩
  have present :=
    executeObservedContextualWorklistMulti?_containsCompleteModuleRootItem_eq_true_of_sourceBackedRoot
      file tokens owned result selected module sourceRoot
  rw [absent] at present
  contradiction

/-- Every final public parser success judgment forces the proof-free
completed-module-root bit. -/
theorem
    executeObservedContextualWorklistMulti?_containsCompleteModuleRootItem_eq_true_of_parses
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklistMulti?
      file tokens owned = some result)
    (module : ParsedModuleV1)
    (parsed : Parses file tokens module) :
    result.containsCompleteModuleRootItem = true := by
  cases parsed with
  | sourceBackedRoot _ sourceRoot =>
      exact
        executeObservedContextualWorklistMulti?_containsCompleteModuleRootItem_eq_true_of_sourceBackedRoot
          file tokens owned result selected module sourceRoot

/-- A selected coherent module value is the only additional interface needed
to upgrade the proof-free completed-root bit to the final parser judgment. -/
theorem
    executeObservedContextualWorklistMulti?_parses_of_completeModuleRootItem_eq_true_of_coherentReduction
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklistMulti?
      file tokens owned = some result)
    (present : result.containsCompleteModuleRootItem = true)
    (module : ParsedModuleV1)
    (coherent : CoherentReduction file tokens result.memo
      (executeObservedContextualWorklistMulti?_phaseBCorrect
        file tokens owned result selected)
      (Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
        file tokens owned result selected)
      (CanonicalCompleteRootItem tokens .module
        (Boundary.start tokens) (Boundary.afterLogicalEOF tokens) .plain)
      module) :
    Parses file tokens module := by
  let correct := executeObservedContextualWorklistMulti?_phaseBCorrect
    file tokens owned result selected
  let final := Chart.executeObservedContextualWorklistMulti?_allGuardsFinal
    file tokens owned result selected
  have reached : ContextualReach file tokens result.memo correct final
      (CanonicalCompleteRootItem tokens .module
        (Boundary.start tokens) (Boundary.afterLogicalEOF tokens) .plain) :=
    (executeObservedContextualWorklistMulti?_containsCompleteModuleRootItem_eq_true_iff
      file tokens owned result selected).mp present
  exact .sourceBackedRoot file tokens module owned
    ⟨result.memo, correct, final, reached,
      canonicalCompleteRootItem_complete .module
        (Boundary.start tokens) (Boundary.afterLogicalEOF tokens) .plain,
      coherent⟩

/-- The same proof-free root-absence bit rules out the final public parser
success judgment, without assuming a unique completion backpointer. -/
theorem
    executeObservedContextualWorklistMulti?_noParses_of_completeModuleRootItem_eq_false
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklistMulti?
      file tokens owned = some result)
    (absent : result.containsCompleteModuleRootItem = false) :
    ¬ ∃ module, Parses file tokens module := by
  rintro ⟨module, parsed⟩
  cases parsed with
  | sourceBackedRoot _ sourceRoot =>
      exact
        (executeObservedContextualWorklistMulti?_noSourceBackedRoot_of_completeModuleRootItem_eq_false
          file tokens owned result selected absent)
          ⟨module, sourceRoot⟩

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

/-- The predicate executor realizes its exact root reduction. -/
theorem executePredicateRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .predicate origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .predicate)) :
    RuleReduction file tokens .predicate origin finish input
      (executePredicateRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let typeAtom : EbnfExpr := .atom (.nonterminal .type)
  let openAtom : EbnfExpr :=
    .atom (.terminal (.symbol .leftParen))
  let typesAtom : EbnfExpr := .list1 typeAtom
  let closeAtom : EbnfExpr :=
    .atom (.terminal (.symbol .rightParen))
  let argumentChildren : List EbnfExpr :=
    [openAtom, typesAtom, closeAtom]
  let argumentChild : EbnfExpr := .sequence argumentChildren
  let children : List EbnfExpr := [
    .atom (.nonterminal .typeAtom),
    .atom (.terminal (.symbol .colon)),
    .atom (.nonterminal .qualifiedName), .optional argumentChild]
  change EbnfValue file tokens (.sequence children) at input
  generalize rootEq : EbnfValue.sequenceFlatView children input = root
  rcases root with ⟨rawMain, rawColon, rawClass, rawOptional, ⟨⟩⟩
  let main := EbnfValue.ruleView .typeAtom rawMain
  let colon := EbnfValue.terminalView (.symbol .colon) rawColon
  let className := EbnfValue.ruleView .qualifiedName rawClass
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  generalize optionalEq : EbnfValue.optionalView
    argumentChild rawOptional = arguments
  cases arguments with
  | none =>
      have resultEq : executePredicateRoot file tokens origin finish
          ready.1 ready.2.1 input = sourceLoc witness {
            main := main
            className := className
            parameters := none
          } := by
        simp [executePredicateRoot, rootEq, optionalEq,
          typeAtom, openAtom, typesAtom, closeAtom, argumentChildren,
          argumentChild, children, main, className, witness]
        congr 1
      have rawOptionalEq : EbnfValue.optional argumentChild none =
          rawOptional := by
        calc
          _ = EbnfValue.optional argumentChild
              (EbnfValue.optionalView argumentChild rawOptional) := by
                rw [optionalEq]
          _ = rawOptional := EbnfValue.optional_of_view
            argumentChild rawOptional
      rw [resultEq, ← EbnfValue.sequence_of_flat_view children input,
        rootEq, ← EbnfValue.rule_of_view .typeAtom rawMain,
        ← EbnfValue.terminal_of_view (.symbol .colon) rawColon,
        ← EbnfValue.rule_of_view .qualifiedName rawClass,
        ← rawOptionalEq]
      exact .predicateWithoutArguments origin finish
        main colon className witness
  | some rawArguments =>
      generalize argumentsEq : EbnfValue.sequenceFlatView
        argumentChildren rawArguments = argumentValues
      rcases argumentValues with ⟨rawOpen, rawTypes, rawClose, ⟨⟩⟩
      let openParen := EbnfValue.terminalView
        (.symbol .leftParen) rawOpen
      let rawTypeValues := EbnfValue.list1View typeAtom rawTypes
      let parameters := rawTypeValues.map (EbnfValue.ruleView .type)
      let closeParen := EbnfValue.terminalView
        (.symbol .rightParen) rawClose
      have parametersMapEq : parameters.map
          (EbnfValue.ruleAtom .type) = rawTypeValues :=
        ruleNonemptyAtoms_of_views .type rawTypeValues
      have parametersEq : EbnfValue.list1 typeAtom
          (parameters.map (EbnfValue.ruleAtom .type)) = rawTypes := by
        rw [parametersMapEq]
        exact EbnfValue.list1_of_view typeAtom rawTypes
      have resultEq : executePredicateRoot file tokens origin finish
          ready.1 ready.2.1 input = sourceLoc witness {
            main := main
            className := className
            parameters := some parameters
          } := by
        simp [executePredicateRoot, rootEq, optionalEq, argumentsEq,
          typeAtom, openAtom, typesAtom, closeAtom, argumentChildren,
          argumentChild, children, main, className, rawTypeValues,
          parameters, witness]
        congr 1
      have rawOptionalEq : EbnfValue.optional argumentChild
          (some rawArguments) = rawOptional := by
        calc
          _ = EbnfValue.optional argumentChild
              (EbnfValue.optionalView argumentChild rawOptional) := by
                rw [optionalEq]
          _ = rawOptional := EbnfValue.optional_of_view
            argumentChild rawOptional
      rw [resultEq, ← EbnfValue.sequence_of_flat_view children input,
        rootEq, ← EbnfValue.rule_of_view .typeAtom rawMain,
        ← EbnfValue.terminal_of_view (.symbol .colon) rawColon,
        ← EbnfValue.rule_of_view .qualifiedName rawClass,
        ← rawOptionalEq,
        ← EbnfValue.sequence_of_flat_view argumentChildren rawArguments,
        argumentsEq,
        ← EbnfValue.terminal_of_view (.symbol .leftParen) rawOpen,
        ← parametersEq,
        ← EbnfValue.terminal_of_view (.symbol .rightParen) rawClose]
      exact .predicateWithArguments origin finish main colon className
        openParen parameters closeParen witness

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

/-- The statement executor realizes its selected subtype reduction. -/
theorem executeStatementRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (_ready : RuleReductionReady file tokens .statement origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .statement)) :
    RuleReduction file tokens .statement origin finish input
      (executeStatementRoot input) := by
  let branches : List EbnfExpr := [
    .atom (.nonterminal .letStatement),
    .atom (.nonterminal .returnStatement),
    .atom (.nonterminal .matchStatement),
    .atom (.nonterminal .ifStatement),
    .atom (.nonterminal .forStatement),
    .atom (.nonterminal .assemblyStatement),
    .atom (.nonterminal .blockStatement),
    .atom (.nonterminal .breakStatement),
    .atom (.nonterminal .continueStatement),
    .atom (.nonterminal .assignmentStatement),
    .atom (.nonterminal .expressionStatement)]
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
      branch = 7 ∨ branch = 8 ∨ branch = 9 ∨ branch = 10 := by
    have branchesLength : branches.length = 11 := by rfl
    have bound : branch.val < 11 := by
      simpa [branchesLength] using branch.isLt
    have valueCases : branch.val = 0 ∨ branch.val = 1 ∨
        branch.val = 2 ∨ branch.val = 3 ∨ branch.val = 4 ∨
        branch.val = 5 ∨ branch.val = 6 ∨ branch.val = 7 ∨
        branch.val = 8 ∨ branch.val = 9 ∨ branch.val = 10 := by
      omega
    rcases valueCases with valueEq | valueEq | valueEq | valueEq |
      valueEq | valueEq | valueEq | valueEq | valueEq | valueEq | valueEq
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
          (Or.inr (Or.inr (Or.inl (Fin.ext valueEq)))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext valueEq))))))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext valueEq))))))))))
  rcases branchCases with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · let value := EbnfValue.ruleView .letStatement raw
    have rawEq := EbnfValue.rule_of_view .letStatement raw
    have resultEq : executeStatementRoot input = value := by
      rw [executeStatementRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .statementLet origin finish value
  · let value := EbnfValue.ruleView .returnStatement raw
    have rawEq := EbnfValue.rule_of_view .returnStatement raw
    have resultEq : executeStatementRoot input = value := by
      rw [executeStatementRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .statementReturn origin finish value
  · let value := EbnfValue.ruleView .matchStatement raw
    have rawEq := EbnfValue.rule_of_view .matchStatement raw
    have resultEq : executeStatementRoot input = value := by
      rw [executeStatementRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .statementMatch origin finish value
  · let value := EbnfValue.ruleView .ifStatement raw
    have rawEq := EbnfValue.rule_of_view .ifStatement raw
    have resultEq : executeStatementRoot input = value := by
      rw [executeStatementRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .statementIf origin finish value
  · let value := EbnfValue.ruleView .forStatement raw
    have rawEq := EbnfValue.rule_of_view .forStatement raw
    have resultEq : executeStatementRoot input = value := by
      rw [executeStatementRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .statementFor origin finish value
  · let value := EbnfValue.ruleView .assemblyStatement raw
    have rawEq := EbnfValue.rule_of_view .assemblyStatement raw
    have resultEq : executeStatementRoot input = value := by
      rw [executeStatementRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .statementAssembly origin finish value
  · let value := EbnfValue.ruleView .blockStatement raw
    have rawEq := EbnfValue.rule_of_view .blockStatement raw
    have resultEq : executeStatementRoot input = value := by
      rw [executeStatementRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .statementBlock origin finish value
  · let value := EbnfValue.ruleView .breakStatement raw
    have rawEq := EbnfValue.rule_of_view .breakStatement raw
    have resultEq : executeStatementRoot input = value := by
      rw [executeStatementRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .statementBreak origin finish value
  · let value := EbnfValue.ruleView .continueStatement raw
    have rawEq := EbnfValue.rule_of_view .continueStatement raw
    have resultEq : executeStatementRoot input = value := by
      rw [executeStatementRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .statementContinue origin finish value
  · let value := EbnfValue.ruleView .assignmentStatement raw
    have rawEq := EbnfValue.rule_of_view .assignmentStatement raw
    have resultEq : executeStatementRoot input = value := by
      rw [executeStatementRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .statementAssignment origin finish value
  · let value := EbnfValue.ruleView .expressionStatement raw
    have rawEq := EbnfValue.rule_of_view .expressionStatement raw
    have resultEq : executeStatementRoot input = value := by
      rw [executeStatementRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .statementExpression origin finish value

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

/-- The annotation executor realizes both optional-suffix reductions. -/
theorem executeAnnotationRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .annotation origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .annotation)) :
    RuleReduction file tokens .annotation origin finish input
      (executeAnnotationRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let expressionAtom : EbnfExpr := .atom (.nonterminal .conditional)
  let colonAtom : EbnfExpr := .atom (.terminal (.symbol .colon))
  let typeAtom : EbnfExpr := .atom (.nonterminal .type)
  let suffix : EbnfExpr := .sequence [colonAtom, typeAtom]
  change EbnfValue file tokens
    (.sequence [expressionAtom, .optional suffix]) at input
  let viewed := EbnfValue.sequence2View
    expressionAtom (.optional suffix) input
  let expression := EbnfValue.ruleView .conditional viewed.1
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have inputEq := EbnfValue.sequence2_of_view
    expressionAtom (.optional suffix) input
  have expressionEq := EbnfValue.rule_of_view .conditional viewed.1
  have optionalEq := EbnfValue.optional_of_view suffix viewed.2
  generalize selectedEq : EbnfValue.optionalView suffix viewed.2 = selected
  cases selected with
  | none =>
      have resultEq : executeAnnotationRoot file tokens origin finish
          ready.1 ready.2.1 input = expression := by
        simp only [executeAnnotationRoot, expressionAtom, colonAtom,
          typeAtom, suffix, viewed, expression, selectedEq]
      have optionalEq' : EbnfValue.optional suffix none = viewed.2 := by
        rw [← selectedEq]
        exact optionalEq
      rw [resultEq, ← inputEq, ← expressionEq, ← optionalEq']
      exact .annotationNone origin finish expression
  | some rawSuffix =>
      let suffixView := EbnfValue.sequence2View
        colonAtom typeAtom rawSuffix
      let colon := EbnfValue.terminalView (.symbol .colon) suffixView.1
      let typeValue := EbnfValue.ruleView .type suffixView.2
      have suffixEq := EbnfValue.sequence2_of_view
        colonAtom typeAtom rawSuffix
      have colonEq := EbnfValue.terminal_of_view
        (.symbol .colon) suffixView.1
      have typeEq := EbnfValue.rule_of_view .type suffixView.2
      have resultEq : executeAnnotationRoot file tokens origin finish
          ready.1 ready.2.1 input =
            sourceLoc witness (.annotation expression typeValue) := by
        simp only [executeAnnotationRoot, expressionAtom, colonAtom,
          typeAtom, suffix, viewed, expression, selectedEq,
          suffixView, typeValue, witness]
      have optionalEq' :
          EbnfValue.optional suffix (some rawSuffix) = viewed.2 := by
        rw [← selectedEq]
        exact optionalEq
      rw [resultEq, ← inputEq, ← expressionEq, ← optionalEq',
        ← suffixEq, ← colonEq, ← typeEq]
      exact .annotationSome origin finish expression colon typeValue witness

/-- The conditional executor realizes all exact conditional reductions. -/
theorem executeConditionalRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .conditional origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .conditional)) :
    RuleReduction file tokens .conditional origin finish input
      (executeConditionalRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let keywordChildren : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .ifKw)),
    .atom (.nonterminal .conditional),
    .atom (.terminal (.contextualKeyword .thenKw)),
    .atom (.nonterminal .conditional),
    .atom (.terminal (.hardKeyword .elseKw)),
    .atom (.nonterminal .conditional)]
  let ternaryChildren : List EbnfExpr := [
    .atom (.terminal (.symbol .question)),
    .atom (.nonterminal .conditional),
    .atom (.terminal (.symbol .colon)),
    .atom (.nonterminal .conditional)]
  let logicalOrAtom : EbnfExpr := .atom (.nonterminal .logicalOr)
  let ternaryBranch : EbnfExpr := .sequence ternaryChildren
  let logicalBranch : EbnfExpr :=
    .sequence [logicalOrAtom, .optional ternaryBranch]
  let keywordBranch : EbnfExpr := .sequence keywordChildren
  change EbnfValue file tokens
    (.choice [keywordBranch, logicalBranch]) at input
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  generalize selectedEq : EbnfValue.choice2View
    keywordBranch logicalBranch input = selected
  have inputEq := EbnfValue.choice2_of_view
    keywordBranch logicalBranch input
  rw [selectedEq] at inputEq
  cases selected with
  | inl rawKeyword =>
      generalize valuesEq : EbnfValue.sequenceFlatView
        keywordChildren rawKeyword = values
      rcases values with
        ⟨rawIf, rawCondition, rawThenKeyword, rawThen,
          rawElseKeyword, rawElse, ⟨⟩⟩
      have rawEq := EbnfValue.sequence_of_flat_view
        keywordChildren rawKeyword
      rw [valuesEq] at rawEq
      let ifKeyword := EbnfValue.terminalView
        (.hardKeyword .ifKw) rawIf
      let condition := EbnfValue.ruleView .conditional rawCondition
      let thenKeyword := EbnfValue.terminalView
        (.contextualKeyword .thenKw) rawThenKeyword
      let thenBranch := EbnfValue.ruleView .conditional rawThen
      let elseKeyword := EbnfValue.terminalView
        (.hardKeyword .elseKw) rawElseKeyword
      let elseBranch := EbnfValue.ruleView .conditional rawElse
      have resultEq : executeConditionalRoot file tokens origin finish
          ready.1 ready.2.1 input = sourceLoc witness
            (.keywordConditional condition thenBranch elseBranch) := by
        simp [executeConditionalRoot, keywordChildren, ternaryChildren,
          logicalOrAtom, ternaryBranch, logicalBranch, keywordBranch,
          selectedEq, valuesEq, condition, thenBranch, elseBranch,
          witness]
      rw [resultEq, ← inputEq, ← rawEq,
        ← EbnfValue.terminal_of_view (.hardKeyword .ifKw) rawIf,
        ← EbnfValue.rule_of_view .conditional rawCondition,
        ← EbnfValue.terminal_of_view
          (.contextualKeyword .thenKw) rawThenKeyword,
        ← EbnfValue.rule_of_view .conditional rawThen,
        ← EbnfValue.terminal_of_view
          (.hardKeyword .elseKw) rawElseKeyword,
        ← EbnfValue.rule_of_view .conditional rawElse]
      exact .conditionalKeyword origin finish ifKeyword condition
        thenKeyword thenBranch elseKeyword elseBranch witness
  | inr rawLogical =>
      let viewed := EbnfValue.sequence2View
        logicalOrAtom (.optional ternaryBranch) rawLogical
      let condition := EbnfValue.ruleView .logicalOr viewed.1
      have rawEq := EbnfValue.sequence2_of_view
        logicalOrAtom (.optional ternaryBranch) rawLogical
      have conditionEq := EbnfValue.rule_of_view .logicalOr viewed.1
      generalize optionalEq : EbnfValue.optionalView
        ternaryBranch viewed.2 = optionalValue
      have optionalRebuild := EbnfValue.optional_of_view
        ternaryBranch viewed.2
      cases optionalValue with
      | none =>
          have optionalValueEq :
              EbnfValue.optional ternaryBranch none = viewed.2 := by
            rw [← optionalEq]
            exact optionalRebuild
          have resultEq : executeConditionalRoot file tokens origin finish
              ready.1 ready.2.1 input = condition := by
            simp [executeConditionalRoot, keywordChildren, ternaryChildren,
              logicalOrAtom, ternaryBranch, logicalBranch, keywordBranch,
              selectedEq, viewed, condition, optionalEq]
          rw [resultEq, ← inputEq, ← rawEq,
            ← conditionEq, ← optionalValueEq]
          exact .conditionalLogical origin finish condition
      | some rawTernary =>
          let questionAtom : EbnfExpr :=
            .atom (.terminal (.symbol .question))
          let conditionalAtom : EbnfExpr :=
            .atom (.nonterminal .conditional)
          let colonAtom : EbnfExpr :=
            .atom (.terminal (.symbol .colon))
          let values := EbnfValue.sequence4View questionAtom
            conditionalAtom colonAtom conditionalAtom rawTernary
          let question := EbnfValue.terminalView
            (.symbol .question) values.1
          let thenBranch := EbnfValue.ruleView .conditional values.2.1
          let colon := EbnfValue.terminalView (.symbol .colon) values.2.2.1
          let elseBranch := EbnfValue.ruleView .conditional values.2.2.2
          have ternaryEq := EbnfValue.sequence4_of_view questionAtom
            conditionalAtom colonAtom conditionalAtom rawTernary
          have optionalValueEq :
              EbnfValue.optional ternaryBranch (some rawTernary) =
                viewed.2 := by
            rw [← optionalEq]
            exact optionalRebuild
          have resultEq : executeConditionalRoot file tokens origin finish
              ready.1 ready.2.1 input = sourceLoc witness
                (.ternaryConditional condition thenBranch elseBranch) := by
            simp [executeConditionalRoot, keywordChildren, ternaryChildren,
              logicalOrAtom, ternaryBranch, logicalBranch, keywordBranch,
              selectedEq, viewed, condition, optionalEq, values,
              questionAtom, conditionalAtom, colonAtom, thenBranch,
              elseBranch, witness]
          rw [resultEq, ← inputEq, ← rawEq, ← conditionEq,
            ← optionalValueEq, ← ternaryEq,
            ← EbnfValue.terminal_of_view (.symbol .question) values.1,
            ← EbnfValue.rule_of_view .conditional values.2.1,
            ← EbnfValue.terminal_of_view (.symbol .colon) values.2.2.1,
            ← EbnfValue.rule_of_view .conditional values.2.2.2]
          exact .conditionalTernary origin finish condition question
            thenBranch colon elseBranch witness

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

/-- The let-binding executor realizes its exact root reduction. -/
theorem executeLetBindingRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .letBinding origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .letBinding)) :
    RuleReduction file tokens .letBinding origin finish input
      (executeLetBindingRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let letAtom : EbnfExpr := .atom (.terminal (.hardKeyword .letKw))
  let nameAtom : EbnfExpr := .atom (.terminal (.category .identifier))
  let colonAtom : EbnfExpr := .atom (.terminal (.symbol .colon))
  let comptimeAtom : EbnfExpr :=
    .atom (.terminal (.contextualKeyword .comptimeKw))
  let typeAtom : EbnfExpr := .atom (.nonterminal .type)
  let typeSeq : EbnfExpr := .sequence [colonAtom, .optional comptimeAtom,
    typeAtom]
  let equalAtom : EbnfExpr := .atom (.terminal (.symbol .equal))
  let expressionAtom : EbnfExpr := .atom (.nonterminal .expression)
  let initSeq : EbnfExpr := .sequence [equalAtom, expressionAtom]
  let children := [letAtom, nameAtom, .optional typeSeq, .optional initSeq]
  change EbnfValue file tokens (.sequence children) at input
  generalize rootEq : EbnfValue.sequenceFlatView children input = root
  rcases root with ⟨rawLet, rawName, rawType, rawInit, ⟨⟩⟩
  let keyword := EbnfValue.terminalView (.hardKeyword .letKw) rawLet
  let name := EbnfValue.terminalView (.category .identifier) rawName
  let decodeInit (raw : EbnfValue file tokens initSeq) :=
    let values := EbnfValue.sequenceFlatView
      [equalAtom, expressionAtom] raw
    (EbnfValue.terminalView (.symbol .equal) values.1,
      EbnfValue.ruleView .expression values.2.1)
  let encodeInit (value : MatchedTerminal file tokens (.symbol .equal) ×
      Expression) : EbnfValue file tokens initSeq :=
    EbnfValue.sequence [equalAtom, expressionAtom]
      (EbnfValue.sequenceValuesBuild [equalAtom, expressionAtom]
        (EbnfValue.terminalAtom (.symbol .equal) value.1,
          EbnfValue.ruleAtom .expression value.2, ()))
  have initRoundtrip : ∀ raw, encodeInit (decodeInit raw) = raw := by
    intro raw
    generalize initEq : EbnfValue.sequenceFlatView
      [equalAtom, expressionAtom] raw = pair
    rcases pair with ⟨rawEqual, rawExpression, ⟨⟩⟩
    simp only [decodeInit, encodeInit, initEq]
    rw [EbnfValue.terminal_of_view (.symbol .equal) rawEqual,
      EbnfValue.rule_of_view .expression rawExpression]
    have rebuild := EbnfValue.sequence_of_flat_view
      [equalAtom, expressionAtom] raw
    rw [initEq] at rebuild
    exact rebuild
  let initializer := (EbnfValue.optionalView initSeq rawInit).map decodeInit
  have initializerEq : EbnfValue.optional initSeq
      (initializer.map encodeInit) = rawInit := by
    calc
      _ = EbnfValue.optional initSeq
          ((EbnfValue.optionalView initSeq rawInit).map decodeInit |>.map
            encodeInit) := by rfl
      _ = EbnfValue.optional initSeq
          (EbnfValue.optionalView initSeq rawInit) := by
            cases selected : EbnfValue.optionalView initSeq rawInit with
            | none => rfl
            | some raw =>
                change EbnfValue.optional initSeq
                  (some (encodeInit (decodeInit raw))) =
                    EbnfValue.optional initSeq (some raw)
                rw [initRoundtrip raw]
      _ = rawInit := EbnfValue.optional_of_view initSeq rawInit
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  generalize typeEq : EbnfValue.optionalView typeSeq rawType = typeViewed
  cases typeViewed with
  | none =>
      have typeRebuild := EbnfValue.optional_of_view typeSeq rawType
      rw [typeEq] at typeRebuild
      have normalizedRootEq := rootEq
      simp only [children, letAtom, nameAtom, typeSeq, colonAtom,
        comptimeAtom, typeAtom, initSeq, equalAtom, expressionAtom] at normalizedRootEq
      have normalizedTypeEq := typeEq
      simp only [typeSeq, colonAtom, comptimeAtom, typeAtom] at normalizedTypeEq
      have resultEq : executeLetBindingRoot file tokens origin finish
          ready.1 ready.2.1 input = sourceLoc witness {
            comptime := none
            name := executableTerminalLoc name name.identifierProjection.2
            type := none
            initializer := initializer.map Prod.snd
          } := by
        simp [executeLetBindingRoot, normalizedRootEq, normalizedTypeEq,
          initializer, decodeInit, witness, name]
        rfl
      rw [resultEq, ← EbnfValue.sequence_of_flat_view children input,
        rootEq,
        ← EbnfValue.terminal_of_view (.hardKeyword .letKw) rawLet,
        ← EbnfValue.terminal_of_view (.category .identifier) rawName,
        ← typeRebuild, ← initializerEq]
      exact .letBindingUntyped origin finish keyword name
        name.identifierProjection.1 name.identifierProjection.2
        name.identifierProjection_projects initializer witness
  | some rawTypeSeq =>
      have typeRebuild := EbnfValue.optional_of_view typeSeq rawType
      rw [typeEq] at typeRebuild
      generalize sequenceEq : EbnfValue.sequenceFlatView
        [colonAtom, .optional comptimeAtom, typeAtom] rawTypeSeq = values
      rcases values with ⟨rawColon, rawComptimeOpt, rawTypeValue, ⟨⟩⟩
      let colon := EbnfValue.terminalView (.symbol .colon) rawColon
      let typeValue := EbnfValue.ruleView .type rawTypeValue
      generalize comptimeEq : EbnfValue.optionalView comptimeAtom
        rawComptimeOpt = viewed
      cases viewed with
      | none =>
          have comptimeRebuild :=
            EbnfValue.optional_of_view comptimeAtom rawComptimeOpt
          rw [comptimeEq] at comptimeRebuild
          have normalizedRootEq := rootEq
          simp only [children, letAtom, nameAtom, typeSeq, colonAtom,
            comptimeAtom, typeAtom, initSeq, equalAtom, expressionAtom] at normalizedRootEq
          have normalizedTypeEq := typeEq
          simp only [typeSeq, colonAtom, comptimeAtom, typeAtom] at normalizedTypeEq
          have normalizedSequenceEq := sequenceEq
          simp only [colonAtom, comptimeAtom, typeAtom] at normalizedSequenceEq
          have normalizedComptimeEq := comptimeEq
          simp only [comptimeAtom] at normalizedComptimeEq
          have resultEq : executeLetBindingRoot file tokens origin finish
              ready.1 ready.2.1 input = sourceLoc witness {
                comptime := none
                name := executableTerminalLoc name
                  name.identifierProjection.2
                type := some typeValue
                initializer := initializer.map Prod.snd
              } := by
            simp [executeLetBindingRoot, normalizedRootEq,
              normalizedTypeEq, normalizedSequenceEq,
              normalizedComptimeEq, initializer, decodeInit, witness,
              name, typeValue]
            rfl
          rw [resultEq, ← EbnfValue.sequence_of_flat_view children input,
            rootEq,
            ← EbnfValue.terminal_of_view (.hardKeyword .letKw) rawLet,
            ← EbnfValue.terminal_of_view (.category .identifier) rawName,
            ← typeRebuild,
            ← EbnfValue.sequence_of_flat_view
              [colonAtom, .optional comptimeAtom, typeAtom] rawTypeSeq,
            sequenceEq,
            ← EbnfValue.terminal_of_view (.symbol .colon) rawColon,
            ← comptimeRebuild,
            ← EbnfValue.rule_of_view .type rawTypeValue,
            ← initializerEq]
          exact .letBindingTyped origin finish keyword name
            name.identifierProjection.1 name.identifierProjection.2
            name.identifierProjection_projects colon typeValue initializer
            witness
      | some rawComptime =>
          have comptimeRebuild :=
            EbnfValue.optional_of_view comptimeAtom rawComptimeOpt
          rw [comptimeEq] at comptimeRebuild
          let comptime := EbnfValue.terminalView
            (.contextualKeyword .comptimeKw) rawComptime
          have normalizedRootEq := rootEq
          simp only [children, letAtom, nameAtom, typeSeq, colonAtom,
            comptimeAtom, typeAtom, initSeq, equalAtom, expressionAtom] at normalizedRootEq
          have normalizedTypeEq := typeEq
          simp only [typeSeq, colonAtom, comptimeAtom, typeAtom] at normalizedTypeEq
          have normalizedSequenceEq := sequenceEq
          simp only [colonAtom, comptimeAtom, typeAtom] at normalizedSequenceEq
          have normalizedComptimeEq := comptimeEq
          simp only [comptimeAtom] at normalizedComptimeEq
          have resultEq : executeLetBindingRoot file tokens origin finish
              ready.1 ready.2.1 input = sourceLoc witness {
                comptime := some (executableTerminalLoc
                  comptime .comptimeModifier)
                name := executableTerminalLoc name
                  name.identifierProjection.2
                type := some typeValue
                initializer := initializer.map Prod.snd
              } := by
            simp [executeLetBindingRoot, normalizedRootEq,
              normalizedTypeEq, normalizedSequenceEq,
              normalizedComptimeEq, initializer, decodeInit, witness,
              name, typeValue, comptime]
            rfl
          rw [resultEq, ← EbnfValue.sequence_of_flat_view children input,
            rootEq,
            ← EbnfValue.terminal_of_view (.hardKeyword .letKw) rawLet,
            ← EbnfValue.terminal_of_view (.category .identifier) rawName,
            ← typeRebuild,
            ← EbnfValue.sequence_of_flat_view
              [colonAtom, .optional comptimeAtom, typeAtom] rawTypeSeq,
            sequenceEq,
            ← EbnfValue.terminal_of_view (.symbol .colon) rawColon,
            ← comptimeRebuild,
            ← EbnfValue.terminal_of_view
              (.contextualKeyword .comptimeKw) rawComptime,
            ← EbnfValue.rule_of_view .type rawTypeValue,
            ← initializerEq]
          exact .letBindingComptime origin finish keyword name
            name.identifierProjection.1 name.identifierProjection.2
            name.identifierProjection_projects colon comptime typeValue
            initializer witness

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

/-- The assembly-statement executor realizes its exact root reduction. -/
theorem executeAssemblyStatementRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .assemblyStatement origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .assemblyStatement)) :
    RuleReduction file tokens .assemblyStatement origin finish input
      (executeAssemblyStatementRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let keywordAtom : EbnfExpr :=
    .atom (.terminal (.hardKeyword .assemblyKw))
  let assemblyAtom : EbnfExpr :=
    .atom (.terminal (.category .assemblyBlock))
  change EbnfValue file tokens (.sequence [keywordAtom, assemblyAtom]) at input
  let viewed := EbnfValue.sequence2View keywordAtom assemblyAtom input
  let keyword := EbnfValue.terminalView (.hardKeyword .assemblyKw) viewed.1
  let assembly := EbnfValue.terminalView (.category .assemblyBlock) viewed.2
  let slice := assembly.assemblyProjection
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have inputEq := EbnfValue.sequence2_of_view keywordAtom assemblyAtom input
  have keywordEq :=
    EbnfValue.terminal_of_view (.hardKeyword .assemblyKw) viewed.1
  have assemblyEq :=
    EbnfValue.terminal_of_view (.category .assemblyBlock) viewed.2
  have resultEq : executeAssemblyStatementRoot file tokens origin finish
      ready.1 ready.2.1 input = sourceLoc witness (.assembly slice) := by
    rfl
  rw [resultEq, ← inputEq, ← keywordEq, ← assemblyEq]
  exact .assemblyStatement origin finish keyword assembly slice
    assembly.assemblyProjection_projects witness

/-- The if-statement executor realizes both optional-else reductions. -/
theorem executeIfStatementRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .ifStatement origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .ifStatement)) :
    RuleReduction file tokens .ifStatement origin finish input
      (executeIfStatementRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let ifAtom : EbnfExpr := .atom (.terminal (.hardKeyword .ifKw))
  let openAtom : EbnfExpr := .atom (.terminal (.symbol .leftParen))
  let expressionAtom : EbnfExpr := .atom (.nonterminal .expression)
  let closeAtom : EbnfExpr := .atom (.terminal (.symbol .rightParen))
  let bodyAtom : EbnfExpr := .atom (.nonterminal .body)
  let elseAtom : EbnfExpr := .atom (.terminal (.hardKeyword .elseKw))
  let elseChildren : List EbnfExpr := [elseAtom, bodyAtom]
  let elseSeq : EbnfExpr := .sequence elseChildren
  let children : List EbnfExpr := [ifAtom, openAtom, expressionAtom,
    closeAtom, bodyAtom, .optional elseSeq]
  change EbnfValue file tokens (.sequence children) at input
  generalize rootEq : EbnfValue.sequenceFlatView children input = root
  rcases root with ⟨rawIf, rawOpen, rawCondition, rawClose, rawThen,
    rawElse, ⟨⟩⟩
  let ifKeyword := EbnfValue.terminalView (.hardKeyword .ifKw) rawIf
  let openParen := EbnfValue.terminalView (.symbol .leftParen) rawOpen
  let condition := EbnfValue.ruleView .expression rawCondition
  let closeParen := EbnfValue.terminalView (.symbol .rightParen) rawClose
  let thenBody := EbnfValue.ruleView .body rawThen
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  generalize optionalEq : EbnfValue.optionalView elseSeq rawElse = viewed
  cases viewed with
  | none =>
      have optionalRebuild := EbnfValue.optional_of_view elseSeq rawElse
      rw [optionalEq] at optionalRebuild
      have resultEq : executeIfStatementRoot file tokens origin finish
          ready.1 ready.2.1 input =
            sourceLoc witness (.ifThenElse condition thenBody none) := by
        simp [executeIfStatementRoot, children, elseChildren, elseSeq,
          ifAtom, openAtom, expressionAtom, closeAtom, bodyAtom, elseAtom,
          rootEq, optionalEq, condition, thenBody, witness]
        rfl
      rw [resultEq, ← EbnfValue.sequence_of_flat_view children input,
        rootEq,
        ← EbnfValue.terminal_of_view (.hardKeyword .ifKw) rawIf,
        ← EbnfValue.terminal_of_view (.symbol .leftParen) rawOpen,
        ← EbnfValue.rule_of_view .expression rawCondition,
        ← EbnfValue.terminal_of_view (.symbol .rightParen) rawClose,
        ← EbnfValue.rule_of_view .body rawThen, ← optionalRebuild]
      exact .ifStatementWithoutElse origin finish ifKeyword openParen
        condition closeParen thenBody witness
  | some rawElseSeq =>
      generalize elseEq : EbnfValue.sequence2View
        elseAtom bodyAtom rawElseSeq = elseView
      rcases elseView with ⟨rawElseKeyword, rawElseBody⟩
      let elseKeyword := EbnfValue.terminalView
        (.hardKeyword .elseKw) rawElseKeyword
      let elseBody := EbnfValue.ruleView .body rawElseBody
      have elseRebuild := EbnfValue.sequence2_of_view
        elseAtom bodyAtom rawElseSeq
      rw [elseEq] at elseRebuild
      have optionalRebuild := EbnfValue.optional_of_view elseSeq rawElse
      rw [optionalEq] at optionalRebuild
      have resultEq : executeIfStatementRoot file tokens origin finish
          ready.1 ready.2.1 input = sourceLoc witness
            (.ifThenElse condition thenBody (some elseBody)) := by
        simp [executeIfStatementRoot, children, elseChildren, elseSeq,
          ifAtom, openAtom, expressionAtom, closeAtom, bodyAtom, elseAtom,
          rootEq, optionalEq, elseEq, condition, thenBody, elseBody,
          witness]
        rfl
      rw [resultEq, ← EbnfValue.sequence_of_flat_view children input,
        rootEq,
        ← EbnfValue.terminal_of_view (.hardKeyword .ifKw) rawIf,
        ← EbnfValue.terminal_of_view (.symbol .leftParen) rawOpen,
        ← EbnfValue.rule_of_view .expression rawCondition,
        ← EbnfValue.terminal_of_view (.symbol .rightParen) rawClose,
        ← EbnfValue.rule_of_view .body rawThen, ← optionalRebuild,
        ← elseRebuild,
        ← EbnfValue.terminal_of_view
          (.hardKeyword .elseKw) rawElseKeyword,
        ← EbnfValue.rule_of_view .body rawElseBody]
      exact .ifStatementWithElse origin finish ifKeyword openParen
        condition closeParen thenBody elseKeyword elseBody witness

/-- The match-statement executor realizes its exact source-rule reduction. -/
theorem executeMatchStatementRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .matchStatement origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .matchStatement)) :
    RuleReduction file tokens .matchStatement origin finish input
      (executeMatchStatementRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let matchAtom : EbnfExpr :=
    .atom (.terminal (.hardKeyword .matchKw))
  let expressionAtom : EbnfExpr := .atom (.nonterminal .expression)
  let openAtom : EbnfExpr :=
    .atom (.terminal (.symbol .leftBrace))
  let armAtom : EbnfExpr := .atom (.nonterminal .matchArm)
  let closeAtom : EbnfExpr :=
    .atom (.terminal (.symbol .rightBrace))
  let semicolonAtom : EbnfExpr :=
    .atom (.terminal (.symbol .semicolon))
  let children : List EbnfExpr := [matchAtom, .list1 expressionAtom,
    openAtom, .plus armAtom, closeAtom, .optional semicolonAtom]
  change EbnfValue file tokens (.sequence children) at input
  generalize viewEq : EbnfValue.sequenceFlatView children input = viewed
  rcases viewed with ⟨rawMatch, rawScrutinees, rawOpen, rawArms,
    rawClose, rawTerminator, ⟨⟩⟩
  let matchKeyword := EbnfValue.terminalView
    (.hardKeyword .matchKw) rawMatch
  let rawScrutineeValues :=
    EbnfValue.list1View expressionAtom rawScrutinees
  let scrutinees := rawScrutineeValues.map
    (EbnfValue.ruleView .expression)
  let openBrace := EbnfValue.terminalView
    (.symbol .leftBrace) rawOpen
  let rawArmValues := EbnfValue.plusView armAtom rawArms
  let arms := rawArmValues.map (EbnfValue.ruleView .matchArm)
  let closeBrace := EbnfValue.terminalView
    (.symbol .rightBrace) rawClose
  let rawTerminatorValue := EbnfValue.optionalView
    semicolonAtom rawTerminator
  let terminator := rawTerminatorValue.map
    (EbnfValue.terminalView (.symbol .semicolon))
  have scrutineesRebuild : EbnfValue.list1 expressionAtom
      (scrutinees.map (EbnfValue.ruleAtom .expression)) =
        rawScrutinees := by
    rw [show scrutinees.map (EbnfValue.ruleAtom .expression) =
        rawScrutineeValues from
      ruleNonemptyAtoms_of_views .expression rawScrutineeValues]
    exact EbnfValue.list1_of_view expressionAtom rawScrutinees
  have armsRebuild : EbnfValue.plus armAtom
      (arms.map (EbnfValue.ruleAtom .matchArm)) = rawArms := by
    rw [show arms.map (EbnfValue.ruleAtom .matchArm) =
        rawArmValues from
      ruleNonemptyAtoms_of_views .matchArm rawArmValues]
    exact EbnfValue.plus_of_view armAtom rawArms
  have terminatorValuesRebuild : terminator.map
      (EbnfValue.terminalAtom (.symbol .semicolon)) =
        rawTerminatorValue := by
    cases selected : rawTerminatorValue with
    | none => simp [terminator, selected]
    | some raw =>
        simp [terminator, selected,
          EbnfValue.terminal_of_view]
  have terminatorRebuild : EbnfValue.optional semicolonAtom
      (terminator.map
        (EbnfValue.terminalAtom (.symbol .semicolon))) =
        rawTerminator := by
    rw [terminatorValuesRebuild]
    exact EbnfValue.optional_of_view semicolonAtom rawTerminator
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have resultEq : executeMatchStatementRoot file tokens origin finish
      ready.1 ready.2.1 input = sourceLoc witness
        (.match scrutinees arms
          (terminator.map MatchedTerminal.span)) := by
    simp only [executeMatchStatementRoot, children, matchAtom,
      expressionAtom, openAtom, armAtom, closeAtom, semicolonAtom,
      viewEq, scrutinees, rawScrutineeValues, arms, rawArmValues,
      terminator, rawTerminatorValue, witness]
  rw [resultEq, ← EbnfValue.sequence_of_flat_view children input,
    viewEq,
    ← EbnfValue.terminal_of_view (.hardKeyword .matchKw) rawMatch,
    ← scrutineesRebuild,
    ← EbnfValue.terminal_of_view (.symbol .leftBrace) rawOpen,
    ← armsRebuild,
    ← EbnfValue.terminal_of_view (.symbol .rightBrace) rawClose,
    ← terminatorRebuild]
  exact .matchStatement origin finish matchKeyword scrutinees openBrace
    arms closeBrace terminator witness

private theorem shortRuleAtoms_of_views
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

private theorem functionSignature_marker_fields_eq
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (genericPrefix : Option GenericPrefix)
    (publicToken : Option (MatchedTerminal file tokens
      (.hardKeyword .publicKw)))
    (payableToken : Option (MatchedTerminal file tokens
      (.hardKeyword .payableKw)))
    (name : MatchedTerminal file tokens (.category .identifier))
    (parameters : List Parameter) (returnType : Option TypeExpr)
    (publicProjects : ∀ matched, publicToken = some matched →
      RuleReduction.MarkerProjects file tokens matched .publicModifier)
    (payableProjects : ∀ matched, payableToken = some matched →
      RuleReduction.MarkerProjects file tokens matched .payableModifier)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    sourceLoc witness ({
      genericPrefix := genericPrefix
      «public» := match publicToken with
        | none => none
        | some terminal => some (RuleReduction.marker terminal
            (publicProjects terminal rfl))
      payable := match payableToken with
        | none => none
        | some terminal => some (RuleReduction.marker terminal
            (payableProjects terminal rfl))
      name := RuleReduction.terminalLoc name name.identifierProjection.2
      parameters := parameters
      returnType := returnType
    } : FunctionSignaturePayload) = sourceLoc witness ({
      genericPrefix := genericPrefix
      «public» := publicToken.map fun terminal =>
        RuleReduction.terminalLoc terminal .publicModifier
      payable := payableToken.map fun terminal =>
        RuleReduction.terminalLoc terminal .payableModifier
      name := RuleReduction.terminalLoc name name.identifierProjection.2
      parameters := parameters
      returnType := returnType
    } : FunctionSignaturePayload) := by
  cases publicToken <;> cases payableToken <;> rfl

/-- The function-signature executor realizes its exact root reduction. -/
theorem executeFunctionSignatureRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .functionSignature origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .functionSignature)) :
    RuleReduction file tokens .functionSignature origin finish input
      (executeFunctionSignatureRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let genericAtom : EbnfExpr := .atom (.nonterminal .genericPrefix)
  let publicAtom : EbnfExpr :=
    .atom (.terminal (.hardKeyword .publicKw))
  let payableAtom : EbnfExpr :=
    .atom (.terminal (.hardKeyword .payableKw))
  let functionAtom : EbnfExpr :=
    .atom (.terminal (.hardKeyword .functionKw))
  let nameAtom : EbnfExpr := .atom (.terminal (.category .identifier))
  let openAtom : EbnfExpr := .atom (.terminal (.symbol .leftParen))
  let parameterAtom : EbnfExpr := .atom (.nonterminal .parameter)
  let closeAtom : EbnfExpr := .atom (.terminal (.symbol .rightParen))
  let returnChild : EbnfExpr := .sequence [
    .atom (.terminal (.symbol .arrow)), .atom (.nonterminal .type)]
  let children : List EbnfExpr := [.optional genericAtom,
    .optional publicAtom, .optional payableAtom, functionAtom, nameAtom,
    openAtom, .list0 parameterAtom, closeAtom, .optional returnChild]
  change EbnfValue file tokens (.sequence children) at input
  generalize sequenceEq : EbnfValue.sequenceFlatView children input = values
  rcases values with ⟨rawGeneric, rawPublic, rawPayable, rawFunction,
    rawName, rawOpen, rawParameters, rawClose, rawReturn, ⟨⟩⟩
  have inputEq := EbnfValue.sequence_of_flat_view children input
  rw [sequenceEq] at inputEq
  let rawGenericValue := EbnfValue.optionalView genericAtom rawGeneric
  let genericPrefix := rawGenericValue.map
    (EbnfValue.ruleView .genericPrefix)
  let rawPublicValue := EbnfValue.optionalView publicAtom rawPublic
  let publicToken := rawPublicValue.map
    (EbnfValue.terminalView (.hardKeyword .publicKw))
  let rawPayableValue := EbnfValue.optionalView payableAtom rawPayable
  let payableToken := rawPayableValue.map
    (EbnfValue.terminalView (.hardKeyword .payableKw))
  let functionKw := EbnfValue.terminalView
    (.hardKeyword .functionKw) rawFunction
  let name := EbnfValue.terminalView (.category .identifier) rawName
  let openParen := EbnfValue.terminalView (.symbol .leftParen) rawOpen
  let rawParameterValues := EbnfValue.list0View parameterAtom rawParameters
  let parameters := rawParameterValues.map (EbnfValue.ruleView .parameter)
  let closeParen := EbnfValue.terminalView (.symbol .rightParen) rawClose
  let rawReturnValue := EbnfValue.optionalView returnChild rawReturn
  let returnValue := rawReturnValue.map fun raw =>
    let pair := EbnfValue.sequence2View
      (.atom (.terminal (.symbol .arrow)))
      (.atom (.nonterminal .type)) raw
    (EbnfValue.terminalView (.symbol .arrow) pair.1,
      EbnfValue.ruleView .type pair.2, ())
  have genericEq : EbnfValue.optional genericAtom
      (genericPrefix.map (EbnfValue.ruleAtom .genericPrefix)) =
        rawGeneric := by
    calc
      _ = EbnfValue.optional genericAtom rawGenericValue := by
        congr 1
        cases selected : rawGenericValue with
        | none => simp [genericPrefix, selected]
        | some raw => simp [genericPrefix, selected,
            EbnfValue.rule_of_view]
      _ = rawGeneric := EbnfValue.optional_of_view genericAtom rawGeneric
  have publicEq : EbnfValue.optional publicAtom
      (publicToken.map (EbnfValue.terminalAtom
        (.hardKeyword .publicKw))) = rawPublic := by
    calc
      _ = EbnfValue.optional publicAtom rawPublicValue := by
        congr 1
        cases selected : rawPublicValue with
        | none => simp [publicToken, selected]
        | some raw => simp [publicToken, selected,
            EbnfValue.terminal_of_view]
      _ = rawPublic := EbnfValue.optional_of_view publicAtom rawPublic
  have payableEq : EbnfValue.optional payableAtom
      (payableToken.map (EbnfValue.terminalAtom
        (.hardKeyword .payableKw))) = rawPayable := by
    calc
      _ = EbnfValue.optional payableAtom rawPayableValue := by
        congr 1
        cases selected : rawPayableValue with
        | none => simp [payableToken, selected]
        | some raw => simp [payableToken, selected,
            EbnfValue.terminal_of_view]
      _ = rawPayable := EbnfValue.optional_of_view payableAtom rawPayable
  have parameterMapEq : parameters.map
      (EbnfValue.ruleAtom .parameter) = rawParameterValues :=
    shortRuleAtoms_of_views .parameter rawParameterValues
  have parametersEq : EbnfValue.list0 parameterAtom
      (parameters.map (EbnfValue.ruleAtom .parameter)) = rawParameters := by
    rw [parameterMapEq]
    exact EbnfValue.list0_of_view parameterAtom rawParameters
  have returnValuesEq : (returnValue.map fun value =>
      EbnfValue.sequence [
          .atom (.terminal (.symbol .arrow)),
          .atom (.nonterminal .type)]
        (EbnfValues.cons (.atom (.terminal (.symbol .arrow)))
          [.atom (.nonterminal .type)]
          (EbnfValue.terminalAtom (.symbol .arrow) value.1)
          (EbnfValues.cons (.atom (.nonterminal .type)) []
            (EbnfValue.ruleAtom .type value.2.1) EbnfValues.nil))) =
        rawReturnValue := by
    cases selected : rawReturnValue with
    | none => simp [returnValue, selected]
    | some raw =>
        let pair := EbnfValue.sequence2View
          (.atom (.terminal (.symbol .arrow)))
          (.atom (.nonterminal .type)) raw
        simp only [returnValue, selected, Option.map]
        apply congrArg some
        rw [EbnfValue.terminal_of_view (.symbol .arrow) pair.1,
          EbnfValue.rule_of_view .type pair.2]
        exact EbnfValue.sequence2_of_view
          (.atom (.terminal (.symbol .arrow)))
          (.atom (.nonterminal .type)) raw
  have returnEq : EbnfValue.optional returnChild
      (returnValue.map fun value =>
        EbnfValue.sequence [
            .atom (.terminal (.symbol .arrow)),
            .atom (.nonterminal .type)]
          (EbnfValues.cons (.atom (.terminal (.symbol .arrow)))
            [.atom (.nonterminal .type)]
            (EbnfValue.terminalAtom (.symbol .arrow) value.1)
            (EbnfValues.cons (.atom (.nonterminal .type)) []
              (EbnfValue.ruleAtom .type value.2.1) EbnfValues.nil))) =
        rawReturn := by
    rw [returnValuesEq]
    exact EbnfValue.optional_of_view returnChild rawReturn
  let publicProjects : ∀ terminal, publicToken = some terminal →
      RuleReduction.MarkerProjects file tokens terminal
        .publicModifier := fun terminal _ => .publicModifier terminal
  let payableProjects : ∀ terminal, payableToken = some terminal →
      RuleReduction.MarkerProjects file tokens terminal
        .payableModifier := fun terminal _ => .payableModifier terminal
  let nameData : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier := {
    matched := name
    spelling := name.identifierProjection.1
    parsed := name.identifierProjection.2
  }
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have resultEq : executeFunctionSignatureRoot file tokens origin finish
      ready.1 ready.2.1 input = sourceLoc witness {
        genericPrefix := genericPrefix
        «public» := publicToken.map fun terminal =>
          RuleReduction.terminalLoc terminal .publicModifier
        payable := payableToken.map fun terminal =>
          RuleReduction.terminalLoc terminal .payableModifier
        name := RuleReduction.terminalLoc name name.identifierProjection.2
        parameters := parameters
        returnType := returnValue.map fun value => value.2.1
      } := by
    have sequenceEq' := sequenceEq
    simp only [children, genericAtom, publicAtom, payableAtom, functionAtom,
      nameAtom, openAtom, parameterAtom, closeAtom, returnChild] at sequenceEq'
    simp [executeFunctionSignatureRoot, sequenceEq', genericPrefix,
      publicToken, payableToken, name, parameters, returnValue, witness]
    rfl
  rw [resultEq, ← inputEq, ← genericEq, ← publicEq, ← payableEq,
    ← EbnfValue.terminal_of_view (.hardKeyword .functionKw) rawFunction,
    ← EbnfValue.terminal_of_view (.category .identifier) rawName,
    ← EbnfValue.terminal_of_view (.symbol .leftParen) rawOpen,
    ← parametersEq,
    ← EbnfValue.terminal_of_view (.symbol .rightParen) rawClose,
    ← returnEq]
  have reduces := RuleReduction.functionSignature origin finish
    genericPrefix publicToken payableToken functionKw nameData openParen
    parameters closeParen returnValue publicProjects payableProjects
    name.identifierProjection_projects witness
  have outputEq := functionSignature_marker_fields_eq genericPrefix
    publicToken payableToken name parameters
    (returnValue.map fun value => value.2.1) publicProjects payableProjects
    witness
  exact outputEq ▸ reduces

/-- The return-statement executor realizes its exact root reduction. -/
theorem executeReturnStatementRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .returnStatement origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .returnStatement)) :
    RuleReduction file tokens .returnStatement origin finish input
      (executeReturnStatementRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let keywordAtom : EbnfExpr :=
    .atom (.terminal (.hardKeyword .returnKw))
  let expressionAtom : EbnfExpr := .atom (.nonterminal .expression)
  let optionalAtom : EbnfExpr := .optional expressionAtom
  let semicolonAtom : EbnfExpr := .atom (.terminal (.symbol .semicolon))
  change EbnfValue file tokens
    (.sequence [keywordAtom, optionalAtom, semicolonAtom]) at input
  let viewed := EbnfValue.sequence3View
    keywordAtom optionalAtom semicolonAtom input
  let keyword := EbnfValue.terminalView (.hardKeyword .returnKw) viewed.1
  let rawValue := EbnfValue.optionalView expressionAtom viewed.2.1
  let value := rawValue.map (EbnfValue.ruleView .expression)
  let semicolon := EbnfValue.terminalView (.symbol .semicolon) viewed.2.2
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have inputEq := EbnfValue.sequence3_of_view
    keywordAtom optionalAtom semicolonAtom input
  have keywordEq := EbnfValue.terminal_of_view
    (.hardKeyword .returnKw) viewed.1
  have valueEq : EbnfValue.optional expressionAtom
      (value.map (EbnfValue.ruleAtom .expression)) = viewed.2.1 := by
    calc
      _ = EbnfValue.optional expressionAtom rawValue := by
        congr 1
        cases selected : rawValue with
        | none => simp [value, selected]
        | some raw =>
            simp only [value, selected, Option.map]
            exact congrArg some (EbnfValue.rule_of_view .expression raw)
      _ = viewed.2.1 := EbnfValue.optional_of_view expressionAtom viewed.2.1
  have semicolonEq :=
    EbnfValue.terminal_of_view (.symbol .semicolon) viewed.2.2
  have resultEq : executeReturnStatementRoot file tokens origin finish
      ready.1 ready.2.1 input =
        sourceLoc witness (.return value semicolon.span) := by rfl
  rw [resultEq, ← inputEq, ← keywordEq, ← valueEq, ← semicolonEq]
  exact .returnStatement origin finish keyword value semicolon witness

/-- The assignment-statement executor realizes its exact root reduction. -/
theorem executeAssignmentStatementRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .assignmentStatement origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .assignmentStatement)) :
    RuleReduction file tokens .assignmentStatement origin finish input
      (executeAssignmentStatementRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let expressionAtom : EbnfExpr := .atom (.nonterminal .expression)
  let operatorAtom : EbnfExpr := .atom (.nonterminal .assignmentOperator)
  let semicolonAtom : EbnfExpr := .atom (.terminal (.symbol .semicolon))
  change EbnfValue file tokens (.sequence [
    expressionAtom, operatorAtom, expressionAtom, semicolonAtom]) at input
  let viewed := EbnfValue.sequence4View
    expressionAtom operatorAtom expressionAtom semicolonAtom input
  let left := EbnfValue.ruleView .expression viewed.1
  let operator := EbnfValue.ruleView .assignmentOperator viewed.2.1
  let right := EbnfValue.ruleView .expression viewed.2.2.1
  let semicolon := EbnfValue.terminalView (.symbol .semicolon) viewed.2.2.2
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have inputEq := EbnfValue.sequence4_of_view
    expressionAtom operatorAtom expressionAtom semicolonAtom input
  have leftEq := EbnfValue.rule_of_view .expression viewed.1
  have operatorEq := EbnfValue.rule_of_view .assignmentOperator viewed.2.1
  have rightEq := EbnfValue.rule_of_view .expression viewed.2.2.1
  have semicolonEq :=
    EbnfValue.terminal_of_view (.symbol .semicolon) viewed.2.2.2
  have resultEq : executeAssignmentStatementRoot file tokens origin finish
      ready.1 ready.2.1 input =
        sourceLoc witness (.assignment operator left right) := by rfl
  rw [resultEq, ← inputEq, ← leftEq, ← operatorEq, ← rightEq,
    ← semicolonEq]
  exact .assignmentStatement origin finish left operator right semicolon witness

/-- The body executor realizes its exact braced root reduction. -/
theorem executeBodyRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .body origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .body)) :
    RuleReduction file tokens .body origin finish input
      (executeBodyRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let statementAtom : EbnfExpr := .atom (.nonterminal .statement)
  let openAtom : EbnfExpr := .atom (.terminal (.symbol .leftBrace))
  let statementsAtom : EbnfExpr := .star statementAtom
  let closeAtom : EbnfExpr := .atom (.terminal (.symbol .rightBrace))
  change EbnfValue file tokens
    (.sequence [openAtom, statementsAtom, closeAtom]) at input
  let viewed := EbnfValue.sequence3View
    openAtom statementsAtom closeAtom input
  let openBrace := EbnfValue.terminalView (.symbol .leftBrace) viewed.1
  let rawStatements := EbnfValue.starView statementAtom viewed.2.1
  let statements := rawStatements.map (EbnfValue.ruleView .statement)
  let closeBrace := EbnfValue.terminalView (.symbol .rightBrace) viewed.2.2
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have inputEq := EbnfValue.sequence3_of_view
    openAtom statementsAtom closeAtom input
  have openEq := EbnfValue.terminal_of_view (.symbol .leftBrace) viewed.1
  have statementsMapEq :
      statements.map (EbnfValue.ruleAtom .statement) = rawStatements :=
    shortRuleAtoms_of_views .statement rawStatements
  have statementsEq : EbnfValue.star statementAtom
      (statements.map (EbnfValue.ruleAtom .statement)) = viewed.2.1 := by
    rw [statementsMapEq]
    exact EbnfValue.star_of_view statementAtom viewed.2.1
  have closeEq := EbnfValue.terminal_of_view
    (.symbol .rightBrace) viewed.2.2
  have resultEq : executeBodyRoot file tokens origin finish
      ready.1 ready.2.1 input = sourceLoc witness {
        origin := .braced openBrace.span closeBrace.span
        statements := statements
      } := by rfl
  rw [resultEq, ← inputEq, ← openEq, ← statementsEq, ← closeEq]
  exact .body origin finish openBrace statements closeBrace witness

/-- The `for`-statement executor realizes its exact root reduction. -/
theorem executeForStatementRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .forStatement origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .forStatement)) :
    RuleReduction file tokens .forStatement origin finish input
      (executeForStatementRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let initAtom : EbnfExpr := .atom (.nonterminal .forInitItem)
  let postAtom : EbnfExpr := .atom (.nonterminal .forPostItem)
  let children : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .forKw)),
    .atom (.terminal (.symbol .leftParen)), .list0 initAtom,
    .atom (.terminal (.symbol .semicolon)),
    .atom (.nonterminal .expression),
    .atom (.terminal (.symbol .semicolon)), .list0 postAtom,
    .atom (.terminal (.symbol .rightParen)),
    .atom (.nonterminal .body)]
  change EbnfValue file tokens (.sequence children) at input
  generalize viewEq : EbnfValue.sequenceFlatView children input = viewed
  rcases viewed with ⟨rawFor, rawOpen, rawInit, rawFirstSemi, rawCondition,
    rawSecondSemi, rawPost, rawClose, rawBody, ⟨⟩⟩
  have inputEq := EbnfValue.sequence_of_flat_view children input
  rw [viewEq] at inputEq
  let rawInitializers := EbnfValue.list0View initAtom rawInit
  let initializers := rawInitializers.map (EbnfValue.ruleView .forInitItem)
  let rawPostItems := EbnfValue.list0View postAtom rawPost
  let post := rawPostItems.map (EbnfValue.ruleView .forPostItem)
  have initializersMapEq : initializers.map
      (EbnfValue.ruleAtom .forInitItem) = rawInitializers :=
    shortRuleAtoms_of_views .forInitItem rawInitializers
  have initializersEq : EbnfValue.list0 initAtom
      (initializers.map (EbnfValue.ruleAtom .forInitItem)) = rawInit := by
    rw [initializersMapEq]
    exact EbnfValue.list0_of_view initAtom rawInit
  have postMapEq : post.map (EbnfValue.ruleAtom .forPostItem) =
      rawPostItems :=
    shortRuleAtoms_of_views .forPostItem rawPostItems
  have postEq : EbnfValue.list0 postAtom
      (post.map (EbnfValue.ruleAtom .forPostItem)) = rawPost := by
    rw [postMapEq]
    exact EbnfValue.list0_of_view postAtom rawPost
  let forKeyword := EbnfValue.terminalView (.hardKeyword .forKw) rawFor
  let openParen := EbnfValue.terminalView (.symbol .leftParen) rawOpen
  let firstSemicolon :=
    EbnfValue.terminalView (.symbol .semicolon) rawFirstSemi
  let condition := EbnfValue.ruleView .expression rawCondition
  let secondSemicolon :=
    EbnfValue.terminalView (.symbol .semicolon) rawSecondSemi
  let closeParen := EbnfValue.terminalView (.symbol .rightParen) rawClose
  let body := EbnfValue.ruleView .body rawBody
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have resultEq : executeForStatementRoot file tokens origin finish
      ready.1 ready.2.1 input =
        sourceLoc witness (.forLoop initializers condition post body) := by
    rw [executeForStatementRoot, viewEq]
  rw [resultEq, ← inputEq,
    ← EbnfValue.terminal_of_view (.hardKeyword .forKw) rawFor,
    ← EbnfValue.terminal_of_view (.symbol .leftParen) rawOpen,
    ← initializersEq,
    ← EbnfValue.terminal_of_view (.symbol .semicolon) rawFirstSemi,
    ← EbnfValue.rule_of_view .expression rawCondition,
    ← EbnfValue.terminal_of_view (.symbol .semicolon) rawSecondSemi,
    ← postEq,
    ← EbnfValue.terminal_of_view (.symbol .rightParen) rawClose,
    ← EbnfValue.rule_of_view .body rawBody]
  exact .forStatement origin finish forKeyword openParen initializers
    firstSemicolon condition secondSemicolon post closeParen body witness

/-- The `for` initializer executor realizes its selected root reduction. -/
theorem executeForInitItemRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .forInitItem origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .forInitItem)) :
    RuleReduction file tokens .forInitItem origin finish input
      (executeForInitItemRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let expressionAtom : EbnfExpr := .atom (.nonterminal .expression)
  let operatorAtom : EbnfExpr := .atom (.nonterminal .assignmentOperator)
  let branches : List EbnfExpr := [
    .atom (.nonterminal .letBinding),
    .sequence [expressionAtom, operatorAtom, expressionAtom], expressionAtom]
  change EbnfValue file tokens (.choice branches) at input
  generalize viewEq : EbnfValue.choiceView branches input = viewed
  rcases viewed with ⟨branch, raw⟩
  have inputEq : EbnfValue.choice branches ⟨branch, raw⟩ = input := by
    calc
      _ = EbnfValue.choice branches
          (EbnfValue.choiceView branches input) := by rw [viewEq]
      _ = input := EbnfValue.choice_of_view branches input
  have branchCases : branch = 0 ∨ branch = 1 ∨ branch = 2 := by
    have lengthEq : branches.length = 3 := by rfl
    have bound : branch.val < 3 := by simpa [lengthEq] using branch.isLt
    have valueCases : branch.val = 0 ∨ branch.val = 1 ∨
        branch.val = 2 := by omega
    rcases valueCases with valueEq | valueEq | valueEq
    · exact Or.inl (Fin.ext valueEq)
    · exact Or.inr (Or.inl (Fin.ext valueEq))
    · exact Or.inr (Or.inr (Fin.ext valueEq))
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  rcases branchCases with rfl | rfl | rfl
  · let binding := EbnfValue.ruleView .letBinding raw
    have rawEq := EbnfValue.rule_of_view .letBinding raw
    have resultEq : executeForInitItemRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness (.letBinding binding) := by
      rw [executeForInitItemRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .forInitItemLet origin finish binding witness
  · let viewed := EbnfValue.sequence3View
      expressionAtom operatorAtom expressionAtom raw
    let left := EbnfValue.ruleView .expression viewed.1
    let operator := EbnfValue.ruleView .assignmentOperator viewed.2.1
    let right := EbnfValue.ruleView .expression viewed.2.2
    have rawEq := EbnfValue.sequence3_of_view
      expressionAtom operatorAtom expressionAtom raw
    have leftEq := EbnfValue.rule_of_view .expression viewed.1
    have operatorEq :=
      EbnfValue.rule_of_view .assignmentOperator viewed.2.1
    have rightEq := EbnfValue.rule_of_view .expression viewed.2.2
    have resultEq : executeForInitItemRoot file tokens origin finish
        ready.1 ready.2.1 input =
          sourceLoc witness (.assignment operator left right) := by
      rw [executeForInitItemRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq, ← leftEq, ← operatorEq, ← rightEq]
    exact .forInitItemAssignment origin finish left operator right witness
  · let expression := EbnfValue.ruleView .expression raw
    have rawEq := EbnfValue.rule_of_view .expression raw
    have resultEq : executeForInitItemRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness (.expression expression) := by
      rw [executeForInitItemRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .forInitItemExpression origin finish expression witness

/-- The `for` post-item executor realizes its selected root reduction. -/
theorem executeForPostItemRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .forPostItem origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .forPostItem)) :
    RuleReduction file tokens .forPostItem origin finish input
      (executeForPostItemRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let expressionAtom : EbnfExpr := .atom (.nonterminal .expression)
  let operatorAtom : EbnfExpr := .atom (.nonterminal .assignmentOperator)
  let branches : List EbnfExpr := [
    .sequence [expressionAtom, operatorAtom, expressionAtom], expressionAtom]
  change EbnfValue file tokens (.choice branches) at input
  generalize viewEq : EbnfValue.choiceView branches input = viewed
  rcases viewed with ⟨branch, raw⟩
  have inputEq : EbnfValue.choice branches ⟨branch, raw⟩ = input := by
    calc
      _ = EbnfValue.choice branches
          (EbnfValue.choiceView branches input) := by rw [viewEq]
      _ = input := EbnfValue.choice_of_view branches input
  have branchCases : branch = 0 ∨ branch = 1 := by
    have lengthEq : branches.length = 2 := by rfl
    have bound : branch.val < 2 := by simpa [lengthEq] using branch.isLt
    have valueCases : branch.val = 0 ∨ branch.val = 1 := by omega
    rcases valueCases with valueEq | valueEq
    · exact Or.inl (Fin.ext valueEq)
    · exact Or.inr (Fin.ext valueEq)
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  rcases branchCases with rfl | rfl
  · let viewed := EbnfValue.sequence3View
      expressionAtom operatorAtom expressionAtom raw
    let left := EbnfValue.ruleView .expression viewed.1
    let operator := EbnfValue.ruleView .assignmentOperator viewed.2.1
    let right := EbnfValue.ruleView .expression viewed.2.2
    have rawEq := EbnfValue.sequence3_of_view
      expressionAtom operatorAtom expressionAtom raw
    have leftEq := EbnfValue.rule_of_view .expression viewed.1
    have operatorEq :=
      EbnfValue.rule_of_view .assignmentOperator viewed.2.1
    have rightEq := EbnfValue.rule_of_view .expression viewed.2.2
    have resultEq : executeForPostItemRoot file tokens origin finish
        ready.1 ready.2.1 input =
          sourceLoc witness (.assignment operator left right) := by
      rw [executeForPostItemRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq, ← leftEq, ← operatorEq, ← rightEq]
    exact .forPostItemAssignment origin finish left operator right witness
  · let expression := EbnfValue.ruleView .expression raw
    have rawEq := EbnfValue.rule_of_view .expression raw
    have resultEq : executeForPostItemRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness (.expression expression) := by
      rw [executeForPostItemRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .forPostItemExpression origin finish expression witness

/-- The expression-statement executor realizes its selected root reduction. -/
theorem executeExpressionStatementRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .expressionStatement origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .expressionStatement)) :
    RuleReduction file tokens .expressionStatement origin finish input
      (executeExpressionStatementRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let expressionAtom : EbnfExpr := .atom (.nonterminal .expression)
  let semicolonAtom : EbnfExpr := .atom (.terminal (.symbol .semicolon))
  let branches : List EbnfExpr := [
    .sequence [expressionAtom, semicolonAtom],
    .atom (.nonterminal .terminalExpression)]
  change EbnfValue file tokens (.choice branches) at input
  generalize viewEq : EbnfValue.choiceView branches input = viewed
  rcases viewed with ⟨branch, raw⟩
  have inputEq : EbnfValue.choice branches ⟨branch, raw⟩ = input := by
    calc
      _ = EbnfValue.choice branches
          (EbnfValue.choiceView branches input) := by rw [viewEq]
      _ = input := EbnfValue.choice_of_view branches input
  have branchCases : branch = 0 ∨ branch = 1 := by
    have lengthEq : branches.length = 2 := by rfl
    have bound : branch.val < 2 := by simpa [lengthEq] using branch.isLt
    have valueCases : branch.val = 0 ∨ branch.val = 1 := by omega
    rcases valueCases with valueEq | valueEq
    · exact Or.inl (Fin.ext valueEq)
    · exact Or.inr (Fin.ext valueEq)
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  rcases branchCases with rfl | rfl
  · let viewed := EbnfValue.sequence2View expressionAtom semicolonAtom raw
    let expression := EbnfValue.ruleView .expression viewed.1
    let semicolon := EbnfValue.terminalView (.symbol .semicolon) viewed.2
    have rawEq := EbnfValue.sequence2_of_view
      expressionAtom semicolonAtom raw
    have expressionEq := EbnfValue.rule_of_view .expression viewed.1
    have semicolonEq :=
      EbnfValue.terminal_of_view (.symbol .semicolon) viewed.2
    have resultEq : executeExpressionStatementRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness
          (.expression expression (some semicolon.span)) := by
      rw [executeExpressionStatementRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq, ← expressionEq, ← semicolonEq]
    exact .expressionStatementTerminated
      origin finish expression semicolon witness
  · let expression := EbnfValue.ruleView .terminalExpression raw
    have rawEq := EbnfValue.rule_of_view .terminalExpression raw
    have resultEq : executeExpressionStatementRoot file tokens origin finish
        ready.1 ready.2.1 input =
          sourceLoc witness (.expression expression none) := by
      rw [executeExpressionStatementRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .expressionStatementTerminal origin finish expression witness

/-- The contract-member executor realizes its selected declaration root. -/
theorem executeContractMemberRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .contractMember origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .contractMember)) :
    RuleReduction file tokens .contractMember origin finish input
      (executeContractMemberRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let branches : List EbnfExpr := [
    .atom (.nonterminal .dataDecl),
    .atom (.nonterminal .typeAliasDecl),
    .atom (.nonterminal .fieldDecl),
    .atom (.nonterminal .functionDecl),
    .atom (.nonterminal .fallbackDecl),
    .atom (.nonterminal .contractConstructorDecl)]
  change EbnfValue file tokens (.choice branches) at input
  generalize viewEq : EbnfValue.choiceView branches input = viewed
  rcases viewed with ⟨branch, raw⟩
  have inputEq : EbnfValue.choice branches ⟨branch, raw⟩ = input := by
    calc
      _ = EbnfValue.choice branches
          (EbnfValue.choiceView branches input) := by rw [viewEq]
      _ = input := EbnfValue.choice_of_view branches input
  have branchCases : branch = 0 ∨ branch = 1 ∨ branch = 2 ∨
      branch = 3 ∨ branch = 4 ∨ branch = 5 := by
    have lengthEq : branches.length = 6 := by rfl
    have bound : branch.val < 6 := by simpa [lengthEq] using branch.isLt
    have valueCases : branch.val = 0 ∨ branch.val = 1 ∨
        branch.val = 2 ∨ branch.val = 3 ∨ branch.val = 4 ∨
        branch.val = 5 := by omega
    rcases valueCases with valueEq | valueEq | valueEq | valueEq |
        valueEq | valueEq
    · exact Or.inl (Fin.ext valueEq)
    · exact Or.inr (Or.inl (Fin.ext valueEq))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext valueEq)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext valueEq))))
    · exact Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext valueEq)))))
    · exact Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext valueEq)))))
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  rcases branchCases with rfl | rfl | rfl | rfl | rfl | rfl
  · let declaration := EbnfValue.ruleView .dataDecl raw
    have rawEq := EbnfValue.rule_of_view .dataDecl raw
    have resultEq : executeContractMemberRoot file tokens origin finish
        ready.1 ready.2.1 input =
          sourceLoc witness (.dataDecl declaration) := by
      rw [executeContractMemberRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .contractMemberData origin finish declaration witness
  · let declaration := EbnfValue.ruleView .typeAliasDecl raw
    have rawEq := EbnfValue.rule_of_view .typeAliasDecl raw
    have resultEq : executeContractMemberRoot file tokens origin finish
        ready.1 ready.2.1 input =
          sourceLoc witness (.typeAlias declaration) := by
      rw [executeContractMemberRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .contractMemberTypeAlias origin finish declaration witness
  · let declaration := EbnfValue.ruleView .fieldDecl raw
    have rawEq := EbnfValue.rule_of_view .fieldDecl raw
    have resultEq : executeContractMemberRoot file tokens origin finish
        ready.1 ready.2.1 input =
          sourceLoc witness (.field declaration) := by
      rw [executeContractMemberRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .contractMemberField origin finish declaration witness
  · let declaration := EbnfValue.ruleView .functionDecl raw
    have rawEq := EbnfValue.rule_of_view .functionDecl raw
    have resultEq : executeContractMemberRoot file tokens origin finish
        ready.1 ready.2.1 input =
          sourceLoc witness (.function declaration) := by
      rw [executeContractMemberRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .contractMemberFunction origin finish declaration witness
  · let declaration := EbnfValue.ruleView .fallbackDecl raw
    have rawEq := EbnfValue.rule_of_view .fallbackDecl raw
    have resultEq : executeContractMemberRoot file tokens origin finish
        ready.1 ready.2.1 input =
          sourceLoc witness (.fallback declaration) := by
      rw [executeContractMemberRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .contractMemberFallback origin finish declaration witness
  · let declaration := EbnfValue.ruleView .contractConstructorDecl raw
    have rawEq := EbnfValue.rule_of_view .contractConstructorDecl raw
    have resultEq : executeContractMemberRoot file tokens origin finish
        ready.1 ready.2.1 input =
          sourceLoc witness (.constructor declaration) := by
      rw [executeContractMemberRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .contractMemberConstructor origin finish declaration witness

/-- The assignment-operator executor realizes its selected terminal root. -/
theorem executeAssignmentOperatorRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (_ready : RuleReductionReady file tokens .assignmentOperator origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .assignmentOperator)) :
    RuleReduction file tokens .assignmentOperator origin finish input
      (executeAssignmentOperatorRoot input) := by
  let branches : List EbnfExpr := [
    .atom (.terminal (.symbol .equal)),
    .atom (.terminal (.symbol .plusEqual)),
    .atom (.terminal (.symbol .minusEqual)),
    .atom (.terminal (.symbol .caretEqual)),
    .atom (.terminal (.symbol .ampEqual)),
    .atom (.terminal (.symbol .pipeEqual)),
    .atom (.terminal (.symbol .percentEqual))]
  change EbnfValue file tokens (.choice branches) at input
  generalize viewEq : EbnfValue.choiceView branches input = viewed
  rcases viewed with ⟨branch, raw⟩
  have inputEq : EbnfValue.choice branches ⟨branch, raw⟩ = input := by
    calc
      _ = EbnfValue.choice branches
          (EbnfValue.choiceView branches input) := by rw [viewEq]
      _ = input := EbnfValue.choice_of_view branches input
  have branchCases : branch.val = 0 ∨ branch.val = 1 ∨
      branch.val = 2 ∨ branch.val = 3 ∨ branch.val = 4 ∨
      branch.val = 5 ∨ branch.val = 6 := by
    have lengthEq : branches.length = 7 := by rfl
    have bound : branch.val < 7 := by simpa [lengthEq] using branch.isLt
    omega
  rcases branchCases with valueEq | valueEq | valueEq | valueEq |
      valueEq | valueEq | valueEq
  · have branchEq : branch = 0 := Fin.ext valueEq
    subst branch
    let terminal := EbnfValue.terminalView (.symbol .equal) raw
    have rawEq := EbnfValue.terminal_of_view (.symbol .equal) raw
    have resultEq : executeAssignmentOperatorRoot input =
        RuleReduction.assignmentOperator terminal (.equal terminal) := by
      rw [executeAssignmentOperatorRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .assignmentOperatorEqual origin finish terminal
  · have branchEq : branch = 1 := Fin.ext valueEq
    subst branch
    let terminal := EbnfValue.terminalView (.symbol .plusEqual) raw
    have rawEq := EbnfValue.terminal_of_view (.symbol .plusEqual) raw
    have resultEq : executeAssignmentOperatorRoot input =
        RuleReduction.assignmentOperator terminal (.addEqual terminal) := by
      rw [executeAssignmentOperatorRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .assignmentOperatorAddEqual origin finish terminal
  · have branchEq : branch = 2 := Fin.ext valueEq
    subst branch
    let terminal := EbnfValue.terminalView (.symbol .minusEqual) raw
    have rawEq := EbnfValue.terminal_of_view (.symbol .minusEqual) raw
    have resultEq : executeAssignmentOperatorRoot input =
        RuleReduction.assignmentOperator terminal (.subtractEqual terminal) := by
      rw [executeAssignmentOperatorRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .assignmentOperatorSubtractEqual origin finish terminal
  · have branchEq : branch = 3 := Fin.ext valueEq
    subst branch
    let terminal := EbnfValue.terminalView (.symbol .caretEqual) raw
    have rawEq := EbnfValue.terminal_of_view (.symbol .caretEqual) raw
    have resultEq : executeAssignmentOperatorRoot input =
        RuleReduction.assignmentOperator terminal (.bitXorEqual terminal) := by
      rw [executeAssignmentOperatorRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .assignmentOperatorBitXorEqual origin finish terminal
  · have branchEq : branch = 4 := Fin.ext valueEq
    subst branch
    let terminal := EbnfValue.terminalView (.symbol .ampEqual) raw
    have rawEq := EbnfValue.terminal_of_view (.symbol .ampEqual) raw
    have resultEq : executeAssignmentOperatorRoot input =
        RuleReduction.assignmentOperator terminal (.bitAndEqual terminal) := by
      rw [executeAssignmentOperatorRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .assignmentOperatorBitAndEqual origin finish terminal
  · have branchEq : branch = 5 := Fin.ext valueEq
    subst branch
    let terminal := EbnfValue.terminalView (.symbol .pipeEqual) raw
    have rawEq := EbnfValue.terminal_of_view (.symbol .pipeEqual) raw
    have resultEq : executeAssignmentOperatorRoot input =
        RuleReduction.assignmentOperator terminal (.bitOrEqual terminal) := by
      rw [executeAssignmentOperatorRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .assignmentOperatorBitOrEqual origin finish terminal
  · have branchEq : branch = 6 := Fin.ext valueEq
    subst branch
    let terminal := EbnfValue.terminalView (.symbol .percentEqual) raw
    have rawEq := EbnfValue.terminal_of_view (.symbol .percentEqual) raw
    have resultEq : executeAssignmentOperatorRoot input =
        RuleReduction.assignmentOperator terminal (.moduloEqual terminal) := by
      rw [executeAssignmentOperatorRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .assignmentOperatorModuloEqual origin finish terminal

/-- The prefix executor realizes its selected recursive root. -/
theorem executePrefixRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .prefix origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .prefix)) :
    RuleReduction file tokens .prefix origin finish input
      (executePrefixRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let bangAtom : EbnfExpr := .atom (.terminal (.symbol .bang))
  let prefixAtom : EbnfExpr := .atom (.nonterminal .prefix)
  let branches : List EbnfExpr := [
    .sequence [bangAtom, prefixAtom],
    .atom (.nonterminal .postfix)]
  change EbnfValue file tokens (.choice branches) at input
  generalize viewEq : EbnfValue.choiceView branches input = viewed
  rcases viewed with ⟨branch, raw⟩
  have inputEq : EbnfValue.choice branches ⟨branch, raw⟩ = input := by
    calc
      _ = EbnfValue.choice branches
          (EbnfValue.choiceView branches input) := by rw [viewEq]
      _ = input := EbnfValue.choice_of_view branches input
  have branchCases : branch = 0 ∨ branch = 1 := by
    have lengthEq : branches.length = 2 := by rfl
    have bound : branch.val < 2 := by simpa [lengthEq] using branch.isLt
    have valueCases : branch.val = 0 ∨ branch.val = 1 := by omega
    rcases valueCases with valueEq | valueEq
    · exact Or.inl (Fin.ext valueEq)
    · exact Or.inr (Fin.ext valueEq)
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  rcases branchCases with rfl | rfl
  · let viewed := EbnfValue.sequence2View bangAtom prefixAtom raw
    let bang := EbnfValue.terminalView (.symbol .bang) viewed.1
    let operand := EbnfValue.ruleView .prefix viewed.2
    have rawEq := EbnfValue.sequence2_of_view bangAtom prefixAtom raw
    have bangEq := EbnfValue.terminal_of_view (.symbol .bang) viewed.1
    have operandEq := EbnfValue.rule_of_view .prefix viewed.2
    have resultEq : executePrefixRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness
          (.prefix (RuleReduction.prefixOperator bang) operand) := by
      rw [executePrefixRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq, ← bangEq, ← operandEq]
    exact .prefixLogicalNot origin finish bang operand witness
  · let expression := EbnfValue.ruleView .postfix raw
    have rawEq := EbnfValue.rule_of_view .postfix raw
    have resultEq : executePrefixRoot file tokens origin finish
        ready.1 ready.2.1 input = expression := by
      rw [executePrefixRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .prefixPostfix origin finish expression

/-- The postfix-part executor realizes its selected structural root. -/
theorem executePostfixPartRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (_ready : RuleReductionReady file tokens .postfixPart origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .postfixPart)) :
    RuleReduction file tokens .postfixPart origin finish input
      (executePostfixPartRoot input) := by
  let expressionAtom : EbnfExpr := .atom (.nonterminal .expression)
  let branches : List EbnfExpr := [
    .sequence [
      .atom (.terminal (.symbol .leftParen)),
      .list0 expressionAtom,
      .atom (.terminal (.symbol .rightParen))],
    .sequence [
      .atom (.terminal (.symbol .dot)),
      .atom (.terminal (.category .identifier))],
    .sequence [
      .atom (.terminal (.symbol .leftBracket)),
      expressionAtom,
      .atom (.terminal (.symbol .rightBracket))]]
  change EbnfValue file tokens (.choice branches) at input
  generalize viewEq : EbnfValue.choiceView branches input = viewed
  rcases viewed with ⟨branch, raw⟩
  have inputEq : EbnfValue.choice branches ⟨branch, raw⟩ = input := by
    calc
      _ = EbnfValue.choice branches
          (EbnfValue.choiceView branches input) := by rw [viewEq]
      _ = input := EbnfValue.choice_of_view branches input
  have branchCases : branch = 0 ∨ branch = 1 ∨ branch = 2 := by
    have lengthEq : branches.length = 3 := by rfl
    have bound : branch.val < 3 := by simpa [lengthEq] using branch.isLt
    have valueCases : branch.val = 0 ∨ branch.val = 1 ∨
        branch.val = 2 := by omega
    rcases valueCases with valueEq | valueEq | valueEq
    · exact Or.inl (Fin.ext valueEq)
    · exact Or.inr (Or.inl (Fin.ext valueEq))
    · exact Or.inr (Or.inr (Fin.ext valueEq))
  rcases branchCases with rfl | rfl | rfl
  · let openAtom : EbnfExpr := .atom (.terminal (.symbol .leftParen))
    let closeAtom : EbnfExpr := .atom (.terminal (.symbol .rightParen))
    let viewed := EbnfValue.sequence3View
      openAtom (.list0 expressionAtom) closeAtom raw
    let openParen := EbnfValue.terminalView (.symbol .leftParen) viewed.1
    let rawArguments := EbnfValue.list0View expressionAtom viewed.2.1
    let arguments := rawArguments.map (EbnfValue.ruleView .expression)
    let closeParen := EbnfValue.terminalView
      (.symbol .rightParen) viewed.2.2
    have rawEq := EbnfValue.sequence3_of_view
      openAtom (.list0 expressionAtom) closeAtom raw
    have openEq := EbnfValue.terminal_of_view
      (.symbol .leftParen) viewed.1
    have argumentsMapEq :
        arguments.map (EbnfValue.ruleAtom .expression) = rawArguments :=
      shortRuleAtoms_of_views .expression rawArguments
    have argumentsEq : EbnfValue.list0 expressionAtom
        (arguments.map (EbnfValue.ruleAtom .expression)) = viewed.2.1 := by
      rw [argumentsMapEq]
      exact EbnfValue.list0_of_view expressionAtom viewed.2.1
    have closeEq := EbnfValue.terminal_of_view
      (.symbol .rightParen) viewed.2.2
    have resultEq : executePostfixPartRoot input =
        .call openParen.span arguments closeParen.span := by
      rw [executePostfixPartRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq, ← openEq, ← argumentsEq,
      ← closeEq]
    exact .postfixPartCall origin finish openParen arguments closeParen
  · let dotAtom : EbnfExpr := .atom (.terminal (.symbol .dot))
    let fieldAtom : EbnfExpr := .atom (.terminal (.category .identifier))
    let viewed := EbnfValue.sequence2View dotAtom fieldAtom raw
    let dot := EbnfValue.terminalView (.symbol .dot) viewed.1
    let field := EbnfValue.terminalView (.category .identifier) viewed.2
    let projection := field.identifierProjection
    have rawEq := EbnfValue.sequence2_of_view dotAtom fieldAtom raw
    have dotEq := EbnfValue.terminal_of_view (.symbol .dot) viewed.1
    have fieldEq := EbnfValue.terminal_of_view
      (.category .identifier) viewed.2
    have resultEq : executePostfixPartRoot input =
        .select dot.span
          (RuleReduction.terminalLoc field projection.2) := by
      rw [executePostfixPartRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq, ← dotEq, ← fieldEq]
    exact .postfixPartSelect origin finish dot field projection.1 projection.2
      field.identifierProjection_projects
  · let openAtom : EbnfExpr := .atom (.terminal (.symbol .leftBracket))
    let closeAtom : EbnfExpr := .atom (.terminal (.symbol .rightBracket))
    let viewed := EbnfValue.sequence3View
      openAtom expressionAtom closeAtom raw
    let openBracket := EbnfValue.terminalView
      (.symbol .leftBracket) viewed.1
    let index := EbnfValue.ruleView .expression viewed.2.1
    let closeBracket := EbnfValue.terminalView
      (.symbol .rightBracket) viewed.2.2
    have rawEq := EbnfValue.sequence3_of_view
      openAtom expressionAtom closeAtom raw
    have openEq := EbnfValue.terminal_of_view
      (.symbol .leftBracket) viewed.1
    have indexEq := EbnfValue.rule_of_view .expression viewed.2.1
    have closeEq := EbnfValue.terminal_of_view
      (.symbol .rightBracket) viewed.2.2
    have resultEq : executePostfixPartRoot input =
        .index openBracket.span index closeBracket.span := by
      rw [executePostfixPartRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq, ← openEq, ← indexEq,
      ← closeEq]
    exact .postfixPartIndex origin finish openBracket index closeBracket

theorem executeAtomRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .atom origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .atom)) :
    RuleReduction file tokens .atom origin finish input
      (executeAtomRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let expressionAtom : EbnfExpr := .atom (.nonterminal .expression)
  let argumentExpr : EbnfExpr := .sequence [
    .atom (.terminal (.symbol .leftParen)), .list0 expressionAtom,
    .atom (.terminal (.symbol .rightParen))]
  let tupleTail := EbnfValue.fixedInfixTailExpr (.symbol .comma) .expression
  let branches : List EbnfExpr := [
    .atom (.nonterminal .literal),
    .atom (.terminal (.category .identifier)),
    .sequence [.atom (.terminal (.symbol .dot)),
      .atom (.terminal (.category .identifier)),
      .optional argumentExpr],
    .sequence [.atom (.terminal (.symbol .at)),
      .atom (.nonterminal .typeAtom)],
    .atom (.nonterminal .lambda),
    .sequence [.atom (.terminal (.symbol .leftParen)),
      .atom (.terminal (.symbol .rightParen))],
    .sequence [.atom (.terminal (.symbol .leftParen)), expressionAtom,
      .atom (.terminal (.symbol .rightParen))],
    .sequence [.atom (.terminal (.symbol .leftParen)), expressionAtom,
      .atom (.terminal (.symbol .comma)), expressionAtom,
      .star tupleTail, .atom (.terminal (.symbol .rightParen))]]
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
      branch = 7 := by
    have lengthEq : branches.length = 8 := by rfl
    have bound : branch.val < 8 := by simpa [lengthEq] using branch.isLt
    have cases : branch.val = 0 ∨ branch.val = 1 ∨ branch.val = 2 ∨
        branch.val = 3 ∨ branch.val = 4 ∨ branch.val = 5 ∨
        branch.val = 6 ∨ branch.val = 7 := by omega
    rcases cases with h | h | h | h | h | h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h)))))))
  let witness := ConsumedSpanWitness.compute file tokens origin finish ready.1 ready.2.1
  rcases branchCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · let literal := EbnfValue.ruleView .literal raw
    have rawEq := EbnfValue.rule_of_view .literal raw
    have resultEq : executeAtomRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness (.literal literal) := by
      rw [executeAtomRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .atomLiteral origin finish literal witness
  · let name := EbnfValue.terminalView (.category .identifier) raw
    let projection := name.identifierProjection
    have rawEq := EbnfValue.terminal_of_view
      (.category .identifier) raw
    have resultEq : executeAtomRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness
          (.name (RuleReduction.terminalLoc name projection.2)) := by
      rw [executeAtomRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .atomName origin finish name projection.1 projection.2
      name.identifierProjection_projects witness
  · let dotAtom : EbnfExpr := .atom (.terminal (.symbol .dot))
    let nameAtom : EbnfExpr :=
      .atom (.terminal (.category .identifier))
    let viewed := EbnfValue.sequence3View
      dotAtom nameAtom (.optional argumentExpr) raw
    let dot := EbnfValue.terminalView (.symbol .dot) viewed.1
    let name := EbnfValue.terminalView
      (.category .identifier) viewed.2.1
    let projection := name.identifierProjection
    let rootArguments := (EbnfValue.optionalView argumentExpr
      viewed.2.2).map fun argumentRaw =>
        let argumentView := EbnfValue.sequence3View
          (.atom (.terminal (.symbol .leftParen)))
          (.list0 expressionAtom)
          (.atom (.terminal (.symbol .rightParen))) argumentRaw
        (EbnfValue.list0View expressionAtom argumentView.2.1).map
          (EbnfValue.ruleView .expression)
    have rawEq := EbnfValue.sequence3_of_view
      dotAtom nameAtom (.optional argumentExpr) raw
    have dotEq := EbnfValue.terminal_of_view (.symbol .dot) viewed.1
    have nameEq := EbnfValue.terminal_of_view
      (.category .identifier) viewed.2.1
    have rootResultEq : executeAtomRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness
          (.dotConstructor (RuleReduction.terminalLoc dot ())
            (RuleReduction.terminalLoc name projection.2)
            rootArguments) := by
      rw [executeAtomRoot, viewEq]
      rfl
    generalize optionalEq : EbnfValue.optionalView argumentExpr
      viewed.2.2 = selected
    cases selected with
    | none =>
        have selectedEq : EbnfValue.optional argumentExpr none =
            viewed.2.2 := by
          calc
            _ = EbnfValue.optional argumentExpr
                (EbnfValue.optionalView argumentExpr viewed.2.2) := by
              rw [optionalEq]
            _ = viewed.2.2 :=
              EbnfValue.optional_of_view argumentExpr viewed.2.2
        have rootArgumentsEq : rootArguments = none := by
          simp [rootArguments, optionalEq]
        rw [rootResultEq, rootArgumentsEq, ← inputEq, ← rawEq,
          ← dotEq, ← nameEq,
          ← selectedEq]
        exact .atomDotConstructorWithoutArguments origin finish dot name
          projection.1 projection.2 name.identifierProjection_projects
          witness
    | some argumentRaw =>
        let openAtom : EbnfExpr :=
          .atom (.terminal (.symbol .leftParen))
        let closeAtom : EbnfExpr :=
          .atom (.terminal (.symbol .rightParen))
        let argumentView := EbnfValue.sequence3View
          openAtom (.list0 expressionAtom) closeAtom argumentRaw
        let openParen := EbnfValue.terminalView
          (.symbol .leftParen) argumentView.1
        let rawArguments := EbnfValue.list0View
          expressionAtom argumentView.2.1
        let arguments := rawArguments.map
          (EbnfValue.ruleView .expression)
        let closeParen := EbnfValue.terminalView
          (.symbol .rightParen) argumentView.2.2
        have selectedEq : EbnfValue.optional argumentExpr
            (some argumentRaw) = viewed.2.2 := by
          calc
            _ = EbnfValue.optional argumentExpr
                (EbnfValue.optionalView argumentExpr viewed.2.2) := by
              rw [optionalEq]
            _ = viewed.2.2 :=
              EbnfValue.optional_of_view argumentExpr viewed.2.2
        have argumentEq := EbnfValue.sequence3_of_view
          openAtom (.list0 expressionAtom) closeAtom argumentRaw
        have openEq := EbnfValue.terminal_of_view
          (.symbol .leftParen) argumentView.1
        have argumentsMapEq : arguments.map
            (EbnfValue.ruleAtom .expression) = rawArguments :=
          shortRuleAtoms_of_views .expression rawArguments
        have argumentsEq : EbnfValue.list0 expressionAtom
            (arguments.map (EbnfValue.ruleAtom .expression)) =
              argumentView.2.1 := by
          rw [argumentsMapEq]
          exact EbnfValue.list0_of_view expressionAtom argumentView.2.1
        have closeEq := EbnfValue.terminal_of_view
          (.symbol .rightParen) argumentView.2.2
        have rootArgumentsEq : rootArguments = some arguments := by
          simp [rootArguments, optionalEq, arguments, rawArguments,
            argumentView, openAtom, closeAtom]
        rw [rootResultEq, rootArgumentsEq, ← inputEq, ← rawEq,
          ← dotEq, ← nameEq,
          ← selectedEq, ← argumentEq, ← openEq, ← argumentsEq,
          ← closeEq]
        exact .atomDotConstructorWithArguments origin finish dot name
          projection.1 projection.2 name.identifierProjection_projects
          openParen arguments closeParen witness
  · let atAtom : EbnfExpr := .atom (.terminal (.symbol .at))
    let typeAtom : EbnfExpr := .atom (.nonterminal .typeAtom)
    let viewed := EbnfValue.sequence2View atAtom typeAtom raw
    let marker := EbnfValue.terminalView (.symbol .at) viewed.1
    let typeValue := EbnfValue.ruleView .typeAtom viewed.2
    have rawEq := EbnfValue.sequence2_of_view atAtom typeAtom raw
    have markerEq := EbnfValue.terminal_of_view (.symbol .at) viewed.1
    have typeEq := EbnfValue.rule_of_view .typeAtom viewed.2
    have resultEq : executeAtomRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness
          (.proxy (RuleReduction.terminalLoc marker ()) typeValue) := by
      rw [executeAtomRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq, ← markerEq, ← typeEq]
    exact .atomProxy origin finish marker typeValue witness
  · let lambda := EbnfValue.ruleView .lambda raw
    have rawEq := EbnfValue.rule_of_view .lambda raw
    have resultEq : executeAtomRoot file tokens origin finish
        ready.1 ready.2.1 input = lambda := by
      rw [executeAtomRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .atomLambda origin finish lambda
  · let openAtom : EbnfExpr :=
      .atom (.terminal (.symbol .leftParen))
    let closeAtom : EbnfExpr :=
      .atom (.terminal (.symbol .rightParen))
    let viewed := EbnfValue.sequence2View openAtom closeAtom raw
    let openParen := EbnfValue.terminalView
      (.symbol .leftParen) viewed.1
    let closeParen := EbnfValue.terminalView
      (.symbol .rightParen) viewed.2
    have rawEq := EbnfValue.sequence2_of_view openAtom closeAtom raw
    have openEq := EbnfValue.terminal_of_view
      (.symbol .leftParen) viewed.1
    have closeEq := EbnfValue.terminal_of_view
      (.symbol .rightParen) viewed.2
    have resultEq : executeAtomRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness (.tuple []) := by
      rw [executeAtomRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq, ← openEq, ← closeEq]
    exact .atomEmptyTuple origin finish openParen closeParen witness
  · let openAtom : EbnfExpr :=
      .atom (.terminal (.symbol .leftParen))
    let closeAtom : EbnfExpr :=
      .atom (.terminal (.symbol .rightParen))
    let viewed := EbnfValue.sequence3View
      openAtom expressionAtom closeAtom raw
    let openParen := EbnfValue.terminalView
      (.symbol .leftParen) viewed.1
    let inner := EbnfValue.ruleView .expression viewed.2.1
    let closeParen := EbnfValue.terminalView
      (.symbol .rightParen) viewed.2.2
    have rawEq := EbnfValue.sequence3_of_view
      openAtom expressionAtom closeAtom raw
    have openEq := EbnfValue.terminal_of_view
      (.symbol .leftParen) viewed.1
    have innerEq := EbnfValue.rule_of_view .expression viewed.2.1
    have closeEq := EbnfValue.terminal_of_view
      (.symbol .rightParen) viewed.2.2
    have resultEq : executeAtomRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness (.group inner) := by
      rw [executeAtomRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq, ← openEq, ← innerEq,
      ← closeEq]
    exact .atomGroup origin finish openParen inner closeParen witness
  · let openAtom : EbnfExpr :=
      .atom (.terminal (.symbol .leftParen))
    let commaAtom : EbnfExpr := .atom (.terminal (.symbol .comma))
    let closeAtom : EbnfExpr :=
      .atom (.terminal (.symbol .rightParen))
    let children : List EbnfExpr := [openAtom, expressionAtom, commaAtom,
      expressionAtom, .star tupleTail, closeAtom]
    let viewed := EbnfValue.sequenceFlatView children raw
    let openParen := EbnfValue.terminalView
      (.symbol .leftParen) viewed.1
    let first := EbnfValue.ruleView .expression viewed.2.1
    let comma := EbnfValue.terminalView (.symbol .comma) viewed.2.2.1
    let second := EbnfValue.ruleView .expression viewed.2.2.2.1
    let rawRest := EbnfValue.starView tupleTail viewed.2.2.2.2.1
    let rest := rawRest.map (EbnfValue.fixedInfixTailView
      (.symbol .comma) .expression)
    let closeParen := EbnfValue.terminalView
      (.symbol .rightParen) viewed.2.2.2.2.2.1
    have rawEq := EbnfValue.sequence_of_flat_view children raw
    have openEq := EbnfValue.terminal_of_view
      (.symbol .leftParen) viewed.1
    have firstEq := EbnfValue.rule_of_view .expression viewed.2.1
    have commaEq := EbnfValue.terminal_of_view
      (.symbol .comma) viewed.2.2.1
    have secondEq := EbnfValue.rule_of_view .expression viewed.2.2.2.1
    have restValuesEq : rest.map (EbnfValue.fixedInfixTailValue
        (.symbol .comma) .expression) = rawRest := by
      simp only [rest, List.map_map]
      induction rawRest with
      | nil => rfl
      | cons head tail induction =>
          simp only [List.map_cons, List.cons.injEq]
          exact ⟨EbnfValue.fixedInfixTailValue_of_view
            (.symbol .comma) .expression head, induction⟩
    have restEq : EbnfValue.star tupleTail
        (rest.map (EbnfValue.fixedInfixTailValue
          (.symbol .comma) .expression)) = viewed.2.2.2.2.1 := by
      rw [restValuesEq]
      exact EbnfValue.star_of_view tupleTail viewed.2.2.2.2.1
    have closeEq := EbnfValue.terminal_of_view
      (.symbol .rightParen) viewed.2.2.2.2.2.1
    let rootRest := rawRest.map fun tail =>
      (EbnfValue.fixedInfixTailView
        (.symbol .comma) .expression tail).2
    have resultEq : executeAtomRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness
          (.tuple (first :: second :: rootRest)) := by
      rw [executeAtomRoot, viewEq]
      rfl
    have rootRestEq : rootRest = rest.map Prod.snd := by
      simp [rootRest, rest, List.map_map]
    rw [resultEq, rootRestEq, ← inputEq, ← rawEq]
    simp only [children, EbnfValue.sequenceValuesBuild]
    rw [← openEq, ← firstEq, ← commaEq, ← secondEq, ← restEq, ← closeEq]
    exact .atomTuple origin finish openParen first comma second rest closeParen witness

/-- The qualified-name executor realizes its dotted identifier root. -/
theorem executeQualifiedNameRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .qualifiedName origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .qualifiedName)) :
    RuleReduction file tokens .qualifiedName origin finish input
      (executeQualifiedNameRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let identifierAtom : EbnfExpr :=
    .atom (.terminal (.category .identifier))
  let tail := EbnfValue.terminalPairTailExpr
    (.symbol .dot) (.category .identifier)
  change EbnfValue file tokens
    (.sequence [identifierAtom, .star tail]) at input
  let viewed := EbnfValue.sequence2View identifierAtom (.star tail) input
  let first := EbnfValue.terminalView (.category .identifier) viewed.1
  let rawRest := EbnfValue.starView tail viewed.2
  let firstData : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier := {
    matched := first
    spelling := first.identifierProjection.1
    parsed := first.identifierProjection.2
  }
  let restData : List
      (MatchedTerminal file tokens (.symbol .dot) ×
        RuleReduction.SpelledTerminalData file tokens
          (.category .identifier) Identifier) :=
    rawRest.map fun raw =>
      let pair := EbnfValue.terminalPairTailView
        (.symbol .dot) (.category .identifier) raw
      (pair.1, {
        matched := pair.2
        spelling := pair.2.identifierProjection.1
        parsed := pair.2.identifierProjection.2
      })
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have inputEq := EbnfValue.sequence2_of_view
    identifierAtom (.star tail) input
  have firstEq := EbnfValue.terminal_of_view
    (.category .identifier) viewed.1
  have restValuesEq :
      (restData.map fun entry =>
        EbnfValue.terminalPairTailValue
          (.symbol .dot) (.category .identifier)
          (entry.1, entry.2.matched)) = rawRest := by
    simp only [restData, List.map_map]
    induction rawRest with
    | nil => rfl
    | cons head rest induction =>
        simp only [List.map_cons, List.cons.injEq]
        constructor
        · change EbnfValue.terminalPairTailValue
              (.symbol .dot) (.category .identifier)
              (EbnfValue.terminalPairTailView
                (.symbol .dot) (.category .identifier) head) = head
          exact EbnfValue.terminalPairTailValue_of_view
            (.symbol .dot) (.category .identifier) head
        · exact induction
  have restEq : EbnfValue.star tail
      (restData.map fun entry =>
        EbnfValue.terminalPairTailValue
          (.symbol .dot) (.category .identifier)
          (entry.1, entry.2.matched)) = viewed.2 := by
    rw [restValuesEq]
    exact EbnfValue.star_of_view tail viewed.2
  have firstProjects : IdentifierProjects firstData.matched
      firstData.spelling firstData.parsed :=
    first.identifierProjection_projects
  have restProjects : ∀ entry, entry ∈ restData →
      IdentifierProjects entry.2.matched
        entry.2.spelling entry.2.parsed := by
    intro entry member
    simp only [restData, List.mem_map] at member
    rcases member with ⟨raw, _rawMember, rfl⟩
    exact (EbnfValue.terminalPairTailView
      (.symbol .dot) (.category .identifier) raw).2
        |>.identifierProjection_projects
  have resultEq : executeQualifiedNameRoot file tokens origin finish
      ready.1 ready.2.1 input = sourceLoc witness {
        components := {
          head := RuleReduction.terminalLoc firstData.matched firstData.parsed
          tail := restData.map fun entry =>
            RuleReduction.terminalLoc entry.2.matched entry.2.parsed
        }
      } := by
    simp only [executeQualifiedNameRoot, firstData, restData, List.map_map]
    rfl
  rw [resultEq, ← inputEq, ← firstEq, ← restEq]
  exact .qualifiedName origin finish firstData restData
    firstProjects restProjects witness

/-- The literal executor realizes its selected source-token projection. -/
theorem executeLiteralRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (_ready : RuleReductionReady file tokens .literal origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .literal)) :
    RuleReduction file tokens .literal origin finish input
      (executeLiteralRoot input) := by
  let branches : List EbnfExpr := [
    .atom (.terminal (.category .decimalLiteral)),
    .atom (.terminal (.category .hexadecimalLiteral)),
    .atom (.terminal (.category .stringLiteral))]
  change EbnfValue file tokens (.choice branches) at input
  generalize viewEq : EbnfValue.choiceView branches input = viewed
  rcases viewed with ⟨branch, raw⟩
  have inputEq : EbnfValue.choice branches ⟨branch, raw⟩ = input := by
    calc
      _ = EbnfValue.choice branches
          (EbnfValue.choiceView branches input) := by rw [viewEq]
      _ = input := EbnfValue.choice_of_view branches input
  have branchCases : branch = 0 ∨ branch = 1 ∨ branch = 2 := by
    have lengthEq : branches.length = 3 := by rfl
    have bound : branch.val < 3 := by simpa [lengthEq] using branch.isLt
    have valueCases : branch.val = 0 ∨ branch.val = 1 ∨
        branch.val = 2 := by omega
    rcases valueCases with valueEq | valueEq | valueEq
    · exact Or.inl (Fin.ext valueEq)
    · exact Or.inr (Or.inl (Fin.ext valueEq))
    · exact Or.inr (Or.inr (Fin.ext valueEq))
  rcases branchCases with rfl | rfl | rfl
  · let terminal := EbnfValue.terminalView
      (.category .decimalLiteral) raw
    let payload := terminal.literalProjection .decimalLiteral (by simp)
    have rawEq := EbnfValue.terminal_of_view
      (.category .decimalLiteral) raw
    have resultEq : executeLiteralRoot input =
        RuleReduction.terminalLoc terminal payload := by
      rw [executeLiteralRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .literalDecimal origin finish terminal payload
      (terminal.literalProjection_projects .decimalLiteral (by simp))
  · let terminal := EbnfValue.terminalView
      (.category .hexadecimalLiteral) raw
    let payload := terminal.literalProjection .hexadecimalLiteral (by simp)
    have rawEq := EbnfValue.terminal_of_view
      (.category .hexadecimalLiteral) raw
    have resultEq : executeLiteralRoot input =
        RuleReduction.terminalLoc terminal payload := by
      rw [executeLiteralRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .literalHexadecimal origin finish terminal payload
      (terminal.literalProjection_projects .hexadecimalLiteral (by simp))
  · let terminal := EbnfValue.terminalView
      (.category .stringLiteral) raw
    let payload := terminal.literalProjection .stringLiteral (by simp)
    have rawEq := EbnfValue.terminal_of_view
      (.category .stringLiteral) raw
    have resultEq : executeLiteralRoot input =
        RuleReduction.terminalLoc terminal payload := by
      rw [executeLiteralRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .literalString origin finish terminal payload
      (terminal.literalProjection_projects .stringLiteral (by simp))

/-- The lambda executor realizes its arbitrary-length sequence root. -/
theorem executeLambdaRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .lambda origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .lambda)) :
    RuleReduction file tokens .lambda origin finish input
      (executeLambdaRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let keywordAtom : EbnfExpr :=
    .atom (.terminal (.hardKeyword .lamKw))
  let openAtom : EbnfExpr := .atom (.terminal (.symbol .leftParen))
  let parameterAtom : EbnfExpr := .atom (.nonterminal .parameter)
  let closeAtom : EbnfExpr := .atom (.terminal (.symbol .rightParen))
  let arrowAtom : EbnfExpr := .atom (.terminal (.symbol .arrow))
  let typeAtom : EbnfExpr := .atom (.nonterminal .type)
  let returnExpr : EbnfExpr := .sequence [arrowAtom, typeAtom]
  let bodyAtom : EbnfExpr := .atom (.nonterminal .body)
  let children : List EbnfExpr := [keywordAtom, openAtom,
    .list0 parameterAtom, closeAtom, .optional returnExpr, bodyAtom]
  change EbnfValue file tokens (.sequence children) at input
  let viewed := EbnfValue.sequenceFlatView children input
  let keyword := EbnfValue.terminalView
    (.hardKeyword .lamKw) viewed.1
  let openParen := EbnfValue.terminalView
    (.symbol .leftParen) viewed.2.1
  let rawParameters := EbnfValue.list0View
    parameterAtom viewed.2.2.1
  let parameters := rawParameters.map (EbnfValue.ruleView .parameter)
  let closeParen := EbnfValue.terminalView
    (.symbol .rightParen) viewed.2.2.2.1
  let rawReturn := EbnfValue.optionalView
    returnExpr viewed.2.2.2.2.1
  let returnType : Option
      (MatchedTerminal file tokens (.symbol .arrow) × TypeExpr) :=
    rawReturn.map fun raw =>
      let returnViewed := EbnfValue.sequence2View arrowAtom typeAtom raw
      (EbnfValue.terminalView (.symbol .arrow) returnViewed.1,
        EbnfValue.ruleView .type returnViewed.2)
  let body := EbnfValue.ruleView .body viewed.2.2.2.2.2.1
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have inputEq := EbnfValue.sequence_of_flat_view children input
  have keywordEq := EbnfValue.terminal_of_view
    (.hardKeyword .lamKw) viewed.1
  have openEq := EbnfValue.terminal_of_view
    (.symbol .leftParen) viewed.2.1
  have parametersMapEq :
      parameters.map (EbnfValue.ruleAtom .parameter) = rawParameters :=
    shortRuleAtoms_of_views .parameter rawParameters
  have parametersEq : EbnfValue.list0 parameterAtom
      (parameters.map (EbnfValue.ruleAtom .parameter)) = viewed.2.2.1 := by
    rw [parametersMapEq]
    exact EbnfValue.list0_of_view parameterAtom viewed.2.2.1
  have closeEq := EbnfValue.terminal_of_view
    (.symbol .rightParen) viewed.2.2.2.1
  have returnValuesEq :
      (returnType.map fun value =>
        EbnfValue.sequence [arrowAtom, typeAtom]
          (EbnfValues.cons arrowAtom [typeAtom]
            (EbnfValue.terminalAtom (.symbol .arrow) value.1)
            (EbnfValues.cons typeAtom []
              (EbnfValue.ruleAtom .type value.2) EbnfValues.nil))) =
        rawReturn := by
    cases selected : rawReturn with
    | none => simp [returnType, selected]
    | some raw =>
        let returnViewed := EbnfValue.sequence2View arrowAtom typeAtom raw
        let returnArrow := EbnfValue.terminalView
          (.symbol .arrow) returnViewed.1
        let returnedType := EbnfValue.ruleView .type returnViewed.2
        have arrowEq := EbnfValue.terminal_of_view
          (.symbol .arrow) returnViewed.1
        have typeEq := EbnfValue.rule_of_view .type returnViewed.2
        have sequenceEq := EbnfValue.sequence2_of_view
          arrowAtom typeAtom raw
        simp only [returnType, selected, Option.map]
        apply congrArg some
        change EbnfValue.sequence [arrowAtom, typeAtom]
          (EbnfValues.cons arrowAtom [typeAtom]
            (EbnfValue.terminalAtom (.symbol .arrow) returnArrow)
            (EbnfValues.cons typeAtom []
              (EbnfValue.ruleAtom .type returnedType) EbnfValues.nil)) = raw
        rw [arrowEq, typeEq]
        exact sequenceEq
  have returnEq : EbnfValue.optional returnExpr
      (returnType.map fun value =>
        EbnfValue.sequence [arrowAtom, typeAtom]
          (EbnfValues.cons arrowAtom [typeAtom]
            (EbnfValue.terminalAtom (.symbol .arrow) value.1)
            (EbnfValues.cons typeAtom []
              (EbnfValue.ruleAtom .type value.2) EbnfValues.nil))) =
        viewed.2.2.2.2.1 := by
    rw [returnValuesEq]
    exact EbnfValue.optional_of_view returnExpr viewed.2.2.2.2.1
  have bodyEq := EbnfValue.rule_of_view .body viewed.2.2.2.2.2.1
  have encodedInputEq : EbnfValue.sequence children
      (EbnfValues.cons keywordAtom [openAtom, .list0 parameterAtom,
          closeAtom, .optional returnExpr, bodyAtom]
        (EbnfValue.terminalAtom (.hardKeyword .lamKw) keyword)
        (EbnfValues.cons openAtom [.list0 parameterAtom, closeAtom,
            .optional returnExpr, bodyAtom]
          (EbnfValue.terminalAtom (.symbol .leftParen) openParen)
          (EbnfValues.cons (.list0 parameterAtom)
            [closeAtom, .optional returnExpr, bodyAtom]
            (EbnfValue.list0 parameterAtom
              (parameters.map (EbnfValue.ruleAtom .parameter)))
            (EbnfValues.cons closeAtom [.optional returnExpr, bodyAtom]
              (EbnfValue.terminalAtom (.symbol .rightParen) closeParen)
              (EbnfValues.cons (.optional returnExpr) [bodyAtom]
                (EbnfValue.optional returnExpr
                  (returnType.map fun value =>
                    EbnfValue.sequence [arrowAtom, typeAtom]
                      (EbnfValues.cons arrowAtom [typeAtom]
                        (EbnfValue.terminalAtom
                          (.symbol .arrow) value.1)
                        (EbnfValues.cons typeAtom []
                          (EbnfValue.ruleAtom .type value.2)
                          EbnfValues.nil))))
                (EbnfValues.cons bodyAtom []
                  (EbnfValue.ruleAtom .body body) EbnfValues.nil)))))) =
      input := by
    rw [keywordEq, openEq, parametersEq, closeEq, returnEq, bodyEq]
    exact inputEq
  have resultEq : executeLambdaRoot file tokens origin finish
      ready.1 ready.2.1 input = sourceLoc witness
        (.lambda parameters (returnType.map Prod.snd) body) := by rfl
  rw [resultEq, ← encodedInputEq]
  exact .lambda origin finish keyword openParen parameters closeParen
    returnType body witness

/-- The executable infix fold is the declarative semantic fold. -/
private theorem executeInfixLeft_eq_foldInfixLeft
    (file : WorkspaceFile) (left : Expression)
    (rest : List (Located InfixOperator × Expression)) :
    executeInfixLeft file left rest =
      RuleReduction.foldInfixLeft file left rest := by
  induction rest generalizing left with
  | nil => rfl
  | cons head tail induction =>
      rcases head with ⟨operator, right⟩
      simp only [executeInfixLeft, RuleReduction.foldInfixLeft]
      change executeInfixLeft file
          (RuleReduction.between file left.span right.span
            (.infix operator left right)) tail =
        RuleReduction.foldInfixLeft file
          (RuleReduction.between file left.span right.span
            (.infix operator left right)) tail
      exact induction _

/-- The logical-or executor realizes its exact fixed-infix reduction. -/
theorem executeLogicalOrRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (_ready : RuleReductionReady file tokens .logicalOr origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .logicalOr)) :
    RuleReduction file tokens .logicalOr origin finish input
      (executeLogicalOrRoot file input) := by
  let terminal : TerminalSymbol := .symbol .logicalOr
  let operand : GrammarRuleId := .logicalAnd
  change EbnfValue file tokens
    (EbnfValue.fixedInfixRootExpr terminal operand) at input
  let viewed := EbnfValue.fixedInfixRootView terminal operand input
  let left : Expression := viewed.1
  let rest : List (MatchedTerminal file tokens terminal × Expression) :=
    viewed.2
  have inputEq := EbnfValue.fixedInfixRootValue_of_view
    terminal operand input
  have resultEq : executeLogicalOrRoot file input =
      RuleReduction.foldInfixLeft file left
        (rest.map fun value =>
          (RuleReduction.infixOperator value.1 (.logicalOr value.1),
            value.2)) := by
    change executeInfixLeft file left
      (rest.map fun value =>
        (executableTerminalLoc value.1 .logicalOr, value.2)) = _
    rw [executeInfixLeft_eq_foldInfixLeft]
    rfl
  rw [resultEq, ← inputEq]
  exact .logicalOr origin finish left rest

/-- The logical-and executor realizes its exact fixed-infix reduction. -/
theorem executeLogicalAndRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (_ready : RuleReductionReady file tokens .logicalAnd origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .logicalAnd)) :
    RuleReduction file tokens .logicalAnd origin finish input
      (executeLogicalAndRoot file input) := by
  let terminal : TerminalSymbol := .symbol .logicalAnd
  let operand : GrammarRuleId := .equality
  change EbnfValue file tokens
    (EbnfValue.fixedInfixRootExpr terminal operand) at input
  let viewed := EbnfValue.fixedInfixRootView terminal operand input
  let left : Expression := viewed.1
  let rest : List (MatchedTerminal file tokens terminal × Expression) :=
    viewed.2
  have inputEq := EbnfValue.fixedInfixRootValue_of_view
    terminal operand input
  have resultEq : executeLogicalAndRoot file input =
      RuleReduction.foldInfixLeft file left
        (rest.map fun value =>
          (RuleReduction.infixOperator value.1 (.logicalAnd value.1),
            value.2)) := by
    change executeInfixLeft file left
      (rest.map fun value =>
        (executableTerminalLoc value.1 .logicalAnd, value.2)) = _
    rw [executeInfixLeft_eq_foldInfixLeft]
    rfl
  rw [resultEq, ← inputEq]
  exact .logicalAnd origin finish left rest

/-- The equality executor realizes its exact nonassociative reduction. -/
theorem executeEqualityRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .equality origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .equality)) :
    RuleReduction file tokens .equality origin finish input
      (executeEqualityRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let operandAtom : EbnfExpr := .atom (.nonterminal .relational)
  let tail := EbnfValue.equalityTailExpr
  change EbnfValue file tokens
    (.sequence [operandAtom, .optional tail]) at input
  let viewed := EbnfValue.sequence2View operandAtom (.optional tail) input
  let left := EbnfValue.ruleView .relational viewed.1
  generalize optionalEq : EbnfValue.optionalView tail viewed.2 = selected
  have operandEq := EbnfValue.rule_of_view .relational viewed.1
  have inputEq := EbnfValue.sequence2_of_view
    operandAtom (.optional tail) input
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  cases selected with
  | none =>
      have optionalValueEq : EbnfValue.optional tail none = viewed.2 := by
        calc
          _ = EbnfValue.optional tail
              (EbnfValue.optionalView tail viewed.2) := by rw [optionalEq]
          _ = viewed.2 := EbnfValue.optional_of_view tail viewed.2
      have resultEq : executeEqualityRoot file tokens origin finish
          ready.1 ready.2.1 input = left := by
        simp [executeEqualityRoot, optionalEq, operandAtom, tail, viewed, left]
      rw [resultEq, ← inputEq, ← operandEq, ← optionalValueEq]
      exact .equalityNone origin finish left
  | some rawTail =>
      generalize tailEq : EbnfValue.equalityTailView rawTail = decoded
      rcases decoded with ⟨operator, right⟩
      have tailValueEq : EbnfValue.equalityTailValue
          (operator, right) = rawTail := by
        rw [← tailEq]
        exact EbnfValue.equalityTailValue_of_view rawTail
      have optionalValueEq : EbnfValue.optional tail (some rawTail) =
          viewed.2 := by
        calc
          _ = EbnfValue.optional tail
              (EbnfValue.optionalView tail viewed.2) := by rw [optionalEq]
          _ = viewed.2 := EbnfValue.optional_of_view tail viewed.2
      cases operator with
      | inl equal =>
          have resultEq : executeEqualityRoot file tokens origin finish
              ready.1 ready.2.1 input = sourceLoc witness
                (.infix (executableTerminalLoc equal .equal) left right) := by
            simp [executeEqualityRoot, optionalEq, tailEq, operandAtom,
              tail, viewed, left, witness]
          rw [resultEq, ← inputEq, ← operandEq, ← optionalValueEq,
            ← tailValueEq]
          exact .equalityEqual origin finish left equal right witness
      | inr notEqual =>
          have resultEq : executeEqualityRoot file tokens origin finish
              ready.1 ready.2.1 input = sourceLoc witness
                (.infix (executableTerminalLoc notEqual .notEqual)
                  left right) := by
            simp [executeEqualityRoot, optionalEq, tailEq, operandAtom,
              tail, viewed, left, witness]
          rw [resultEq, ← inputEq, ← operandEq, ← optionalValueEq,
            ← tailValueEq]
          exact .equalityNotEqual origin finish left notEqual right witness

/-- The relational executor realizes its exact declarative reduction. -/
theorem executeRelationalRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .relational origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .relational)) :
    RuleReduction file tokens .relational origin finish input
      (executeRelationalRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let operand : EbnfExpr := .atom (.nonterminal .bitOr)
  let lessAtom : EbnfExpr := .atom (.terminal (.symbol .less))
  let greaterAtom : EbnfExpr := .atom (.terminal (.symbol .greater))
  let lessEqualAtom : EbnfExpr := .atom (.terminal (.symbol .lessEqual))
  let greaterEqualAtom : EbnfExpr :=
    .atom (.terminal (.symbol .greaterEqual))
  let choiceExpr : EbnfExpr := .choice [lessAtom, greaterAtom,
    lessEqualAtom, greaterEqualAtom]
  let operatorExpr : EbnfExpr := .group choiceExpr
  let tail : EbnfExpr := .sequence [operatorExpr, operand]
  change EbnfValue file tokens (.sequence [operand, .optional tail]) at input
  let outer := EbnfValue.sequence2View operand (.optional tail) input
  let left := EbnfValue.ruleView .bitOr outer.1
  have inputEq := EbnfValue.sequence2_of_view
    operand (.optional tail) input
  have leftEq := EbnfValue.rule_of_view .bitOr outer.1
  have optionalEq := EbnfValue.optional_of_view tail outer.2
  generalize optionEq : EbnfValue.optionalView tail outer.2 = viewed
  cases viewed with
  | none =>
      have resultEq : executeRelationalRoot file tokens origin finish
          ready.1 ready.2.1 input = left := by
        simp only [executeRelationalRoot, operand, lessAtom, greaterAtom,
          lessEqualAtom, greaterEqualAtom, choiceExpr, operatorExpr, tail,
          outer, left, optionEq]
      have optionalEq' : EbnfValue.optional tail none = outer.2 := by
        rw [← optionEq]
        exact optionalEq
      rw [resultEq, ← inputEq, ← leftEq, ← optionalEq']
      exact .relationalNone origin finish left
  | some rawTail =>
      let inner := EbnfValue.sequence2View operatorExpr operand rawTail
      let rawChoice := EbnfValue.groupView choiceExpr inner.1
      generalize choiceEq : EbnfValue.choice4View lessAtom greaterAtom
        lessEqualAtom greaterEqualAtom rawChoice = chosen
      have choiceRebuildEq := EbnfValue.choice4_of_view lessAtom
        greaterAtom lessEqualAtom greaterEqualAtom rawChoice
      rw [choiceEq] at choiceRebuildEq
      let right := EbnfValue.ruleView .bitOr inner.2
      have optionalEq' : EbnfValue.optional tail (some rawTail) = outer.2 := by
        rw [← optionEq]
        exact optionalEq
      have tailEq := EbnfValue.sequence2_of_view
        operatorExpr operand rawTail
      have groupEq : EbnfValue.group choiceExpr rawChoice = inner.1 := by
        exact EbnfValue.group_of_view choiceExpr inner.1
      have rightEq := EbnfValue.rule_of_view .bitOr inner.2
      let witness := ConsumedSpanWitness.compute
        file tokens origin finish ready.1 ready.2.1
      rcases chosen with raw | raw | raw | raw
      · let operator := EbnfValue.terminalView (.symbol .less) raw
        have operatorEq := EbnfValue.terminal_of_view (.symbol .less) raw
        have resultEq : executeRelationalRoot file tokens origin finish
            ready.1 ready.2.1 input = sourceLoc witness (.infix
              (executableTerminalLoc operator .less) left right) := by
          simp only [executeRelationalRoot, operand, lessAtom, greaterAtom,
            lessEqualAtom, greaterEqualAtom, choiceExpr, operatorExpr, tail,
            outer, left, optionEq, inner, right, rawChoice, choiceEq,
            operator, witness]
        rw [resultEq, ← inputEq, ← leftEq, ← optionalEq',
          ← tailEq, ← groupEq, ← choiceRebuildEq,
          ← operatorEq, ← rightEq]
        exact .relationalLess origin finish left operator right witness
      · let operator := EbnfValue.terminalView (.symbol .greater) raw
        have operatorEq := EbnfValue.terminal_of_view (.symbol .greater) raw
        have resultEq : executeRelationalRoot file tokens origin finish
            ready.1 ready.2.1 input = sourceLoc witness (.infix
              (executableTerminalLoc operator .greater) left right) := by
          simp only [executeRelationalRoot, operand, lessAtom, greaterAtom,
            lessEqualAtom, greaterEqualAtom, choiceExpr, operatorExpr, tail,
            outer, left, optionEq, inner, right, rawChoice, choiceEq,
            operator, witness]
        rw [resultEq, ← inputEq, ← leftEq, ← optionalEq',
          ← tailEq, ← groupEq, ← choiceRebuildEq,
          ← operatorEq, ← rightEq]
        exact .relationalGreater origin finish left operator right witness
      · let operator := EbnfValue.terminalView (.symbol .lessEqual) raw
        have operatorEq := EbnfValue.terminal_of_view (.symbol .lessEqual) raw
        have resultEq : executeRelationalRoot file tokens origin finish
            ready.1 ready.2.1 input = sourceLoc witness (.infix
              (executableTerminalLoc operator .lessEqual) left right) := by
          simp only [executeRelationalRoot, operand, lessAtom, greaterAtom,
            lessEqualAtom, greaterEqualAtom, choiceExpr, operatorExpr, tail,
            outer, left, optionEq, inner, right, rawChoice, choiceEq,
            operator, witness]
        rw [resultEq, ← inputEq, ← leftEq, ← optionalEq',
          ← tailEq, ← groupEq, ← choiceRebuildEq,
          ← operatorEq, ← rightEq]
        exact .relationalLessEqual origin finish left operator right witness
      · let operator := EbnfValue.terminalView (.symbol .greaterEqual) raw
        have operatorEq := EbnfValue.terminal_of_view
          (.symbol .greaterEqual) raw
        have resultEq : executeRelationalRoot file tokens origin finish
            ready.1 ready.2.1 input = sourceLoc witness (.infix
              (executableTerminalLoc operator .greaterEqual) left right) := by
          simp only [executeRelationalRoot, operand, lessAtom, greaterAtom,
            lessEqualAtom, greaterEqualAtom, choiceExpr, operatorExpr, tail,
            outer, left, optionEq, inner, right, rawChoice, choiceEq,
            operator, witness]
        rw [resultEq, ← inputEq, ← leftEq, ← optionalEq',
          ← tailEq, ← groupEq, ← choiceRebuildEq,
          ← operatorEq, ← rightEq]
        exact .relationalGreaterEqual origin finish left operator right witness

/-- The bitwise-or executor realizes its exact fixed-infix reduction. -/
theorem executeBitOrRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (_ready : RuleReductionReady file tokens .bitOr origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .bitOr)) :
    RuleReduction file tokens .bitOr origin finish input
      (executeBitOrRoot file input) := by
  let terminal : TerminalSymbol := .symbol .pipe
  let operand : GrammarRuleId := .bitXor
  change EbnfValue file tokens
    (EbnfValue.fixedInfixRootExpr terminal operand) at input
  let viewed := EbnfValue.fixedInfixRootView terminal operand input
  let left : Expression := viewed.1
  let rest : List (MatchedTerminal file tokens terminal × Expression) :=
    viewed.2
  have inputEq := EbnfValue.fixedInfixRootValue_of_view
    terminal operand input
  have resultEq : executeBitOrRoot file input =
      RuleReduction.foldInfixLeft file left
        (rest.map fun value =>
          (RuleReduction.infixOperator value.1 (.bitOr value.1), value.2)) := by
    change executeInfixLeft file left
      (rest.map fun value =>
        (executableTerminalLoc value.1 .bitOr, value.2)) = _
    rw [executeInfixLeft_eq_foldInfixLeft]
    rfl
  rw [resultEq, ← inputEq]
  exact .bitOr origin finish left rest

/-- The bitwise-xor executor realizes its exact fixed-infix reduction. -/
theorem executeBitXorRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (_ready : RuleReductionReady file tokens .bitXor origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .bitXor)) :
    RuleReduction file tokens .bitXor origin finish input
      (executeBitXorRoot file input) := by
  let terminal : TerminalSymbol := .symbol .caret
  let operand : GrammarRuleId := .bitAnd
  change EbnfValue file tokens
    (EbnfValue.fixedInfixRootExpr terminal operand) at input
  let viewed := EbnfValue.fixedInfixRootView terminal operand input
  let left : Expression := viewed.1
  let rest : List (MatchedTerminal file tokens terminal × Expression) :=
    viewed.2
  have inputEq := EbnfValue.fixedInfixRootValue_of_view
    terminal operand input
  have resultEq : executeBitXorRoot file input =
      RuleReduction.foldInfixLeft file left
        (rest.map fun value =>
          (RuleReduction.infixOperator value.1 (.bitXor value.1), value.2)) := by
    change executeInfixLeft file left
      (rest.map fun value =>
        (executableTerminalLoc value.1 .bitXor, value.2)) = _
    rw [executeInfixLeft_eq_foldInfixLeft]
    rfl
  rw [resultEq, ← inputEq]
  exact .bitXor origin finish left rest

/-- The bitwise-and executor realizes its exact fixed-infix reduction. -/
theorem executeBitAndRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (_ready : RuleReductionReady file tokens .bitAnd origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .bitAnd)) :
    RuleReduction file tokens .bitAnd origin finish input
      (executeBitAndRoot file input) := by
  let terminal : TerminalSymbol := .symbol .amp
  let operand : GrammarRuleId := .additive
  change EbnfValue file tokens
    (EbnfValue.fixedInfixRootExpr terminal operand) at input
  let viewed := EbnfValue.fixedInfixRootView terminal operand input
  let left : Expression := viewed.1
  let rest : List (MatchedTerminal file tokens terminal × Expression) :=
    viewed.2
  have inputEq := EbnfValue.fixedInfixRootValue_of_view
    terminal operand input
  have resultEq : executeBitAndRoot file input =
      RuleReduction.foldInfixLeft file left
        (rest.map fun value =>
          (RuleReduction.infixOperator value.1 (.bitAnd value.1), value.2)) := by
    change executeInfixLeft file left
      (rest.map fun value =>
        (executableTerminalLoc value.1 .bitAnd, value.2)) = _
    rw [executeInfixLeft_eq_foldInfixLeft]
    rfl
  rw [resultEq, ← inputEq]
  exact .bitAnd origin finish left rest

/-- The additive executor realizes the exact mixed-operator reduction. -/
theorem executeAdditiveRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (_ready : RuleReductionReady file tokens .additive origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .additive)) :
    RuleReduction file tokens .additive origin finish input
      (executeAdditiveRoot file input) := by
  let operandAtom : EbnfExpr := .atom (.nonterminal .multiplicative)
  let tail := EbnfValue.additiveTailExpr
  change EbnfValue file tokens
    (.sequence [operandAtom, .star tail]) at input
  let viewed := EbnfValue.sequence2View operandAtom (.star tail) input
  let left : Expression := EbnfValue.ruleView .multiplicative viewed.1
  let rawRest := EbnfValue.starView tail viewed.2
  let rest := rawRest.map EbnfValue.additiveTailView
  have leftEq := EbnfValue.rule_of_view .multiplicative viewed.1
  have restValuesEq : rest.map EbnfValue.additiveTailValue = rawRest := by
    dsimp only [rest]
    induction rawRest with
    | nil => rfl
    | cons head remaining induction =>
        simp only [List.map_cons]
        rw [EbnfValue.additiveTailValue_of_view, induction]
  have starEq := EbnfValue.star_of_view tail viewed.2
  have inputEq := EbnfValue.sequence2_of_view
    operandAtom (.star tail) input
  have rebuiltEq : EbnfValue.sequence [operandAtom, .star tail]
      (EbnfValues.cons operandAtom [.star tail]
        (EbnfValue.ruleAtom .multiplicative left)
        (EbnfValues.cons (.star tail) []
          (EbnfValue.star tail
            (rest.map EbnfValue.additiveTailValue)) EbnfValues.nil)) = input := by
    rw [restValuesEq, leftEq, starEq]
    exact inputEq
  have resultEq : executeAdditiveRoot file input =
      RuleReduction.foldInfixLeft file left
        (rest.map fun value =>
          ((match value.1 with
            | .inl plus =>
                RuleReduction.infixOperator plus (.add plus)
            | .inr minus =>
                RuleReduction.infixOperator minus (.subtract minus)),
            value.2)) := by
    change executeInfixLeft file left
      (rest.map fun value =>
        ((match value.1 with
          | .inl plus => executableTerminalLoc plus .add
          | .inr minus => executableTerminalLoc minus .subtract),
          value.2)) = _
    rw [executeInfixLeft_eq_foldInfixLeft]
    rfl
  rw [resultEq, ← rebuiltEq]
  exact .additive origin finish left rest

/-- The multiplicative executor realizes the exact mixed-operator reduction. -/
theorem executeMultiplicativeRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (_ready : RuleReductionReady file tokens .multiplicative origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .multiplicative)) :
    RuleReduction file tokens .multiplicative origin finish input
      (executeMultiplicativeRoot file input) := by
  let operandAtom : EbnfExpr := .atom (.nonterminal .prefix)
  let tail := EbnfValue.multiplicativeTailExpr
  change EbnfValue file tokens
    (.sequence [operandAtom, .star tail]) at input
  let viewed := EbnfValue.sequence2View operandAtom (.star tail) input
  let left : Expression := EbnfValue.ruleView .prefix viewed.1
  let rawRest := EbnfValue.starView tail viewed.2
  let rest := rawRest.map EbnfValue.multiplicativeTailView
  have leftEq := EbnfValue.rule_of_view .prefix viewed.1
  have restValuesEq : rest.map EbnfValue.multiplicativeTailValue = rawRest := by
    dsimp only [rest]
    induction rawRest with
    | nil => rfl
    | cons head remaining induction =>
        simp only [List.map_cons]
        rw [EbnfValue.multiplicativeTailValue_of_view, induction]
  have starEq := EbnfValue.star_of_view tail viewed.2
  have inputEq := EbnfValue.sequence2_of_view
    operandAtom (.star tail) input
  have rebuiltEq : EbnfValue.sequence [operandAtom, .star tail]
      (EbnfValues.cons operandAtom [.star tail]
        (EbnfValue.ruleAtom .prefix left)
        (EbnfValues.cons (.star tail) []
          (EbnfValue.star tail
            (rest.map EbnfValue.multiplicativeTailValue)) EbnfValues.nil)) =
      input := by
    rw [restValuesEq, leftEq, starEq]
    exact inputEq
  have resultEq : executeMultiplicativeRoot file input =
      RuleReduction.foldInfixLeft file left
        (rest.map fun value =>
          ((match value.1 with
            | .inl star =>
                RuleReduction.infixOperator star (.multiply star)
            | .inr (.inl slash) =>
                RuleReduction.infixOperator slash (.divide slash)
            | .inr (.inr percent) =>
                RuleReduction.infixOperator percent (.modulo percent)),
            value.2)) := by
    change executeInfixLeft file left
      (rest.map fun value =>
        ((match value.1 with
          | .inl star => executableTerminalLoc star .multiply
          | .inr (.inl slash) => executableTerminalLoc slash .divide
          | .inr (.inr percent) => executableTerminalLoc percent .modulo),
          value.2)) = _
    rw [executeInfixLeft_eq_foldInfixLeft]
    rfl
  rw [resultEq, ← rebuiltEq]
  exact .multiplicative origin finish left rest
/-- The executable postfix fold is the declarative semantic fold. -/
private theorem executePostfixLeft_eq_foldPostfix
    (file : WorkspaceFile) (receiver : Expression)
    (parts : List PostfixPartValue) :
    executePostfixLeft file receiver parts =
      RuleReduction.foldPostfix file receiver parts := by
  induction parts generalizing receiver with
  | nil => rfl
  | cons part rest induction =>
      cases part with
      | call openParen arguments closeParen =>
          simp only [executePostfixLeft, RuleReduction.foldPostfix]
          change executePostfixLeft file
              (RuleReduction.between file receiver.span closeParen
                (.call receiver arguments)) rest =
            RuleReduction.foldPostfix file
              (RuleReduction.between file receiver.span closeParen
                (.call receiver arguments)) rest
          exact induction _
      | select dot field =>
          simp only [executePostfixLeft, RuleReduction.foldPostfix]
          change executePostfixLeft file
              (RuleReduction.between file receiver.span field.span
                (.select receiver field)) rest =
            RuleReduction.foldPostfix file
              (RuleReduction.between file receiver.span field.span
                (.select receiver field)) rest
          exact induction _
      | index openBracket index closeBracket =>
          simp only [executePostfixLeft, RuleReduction.foldPostfix]
          change executePostfixLeft file
              (RuleReduction.between file receiver.span closeBracket
                (.index receiver index)) rest =
            RuleReduction.foldPostfix file
              (RuleReduction.between file receiver.span closeBracket
                (.index receiver index)) rest
          exact induction _

/-- The postfix executor realizes its exact ordered fold reduction. -/
theorem executePostfixRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (_ready : RuleReductionReady file tokens .postfix origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .postfix)) :
    RuleReduction file tokens .postfix origin finish input
      (executePostfixRoot file input) := by
  let atomExpr : EbnfExpr := .atom (.nonterminal .atom)
  let partExpr : EbnfExpr := .atom (.nonterminal .postfixPart)
  change EbnfValue file tokens
    (.sequence [atomExpr, .star partExpr]) at input
  let viewed := EbnfValue.sequence2View atomExpr (.star partExpr) input
  let atom := EbnfValue.ruleView .atom viewed.1
  let rawParts := EbnfValue.starView partExpr viewed.2
  let parts := rawParts.map (EbnfValue.ruleView .postfixPart)
  have inputEq := EbnfValue.sequence2_of_view
    atomExpr (.star partExpr) input
  have atomEq := EbnfValue.rule_of_view .atom viewed.1
  have partsMapEq :
      parts.map (EbnfValue.ruleAtom .postfixPart) = rawParts :=
    shortRuleAtoms_of_views .postfixPart rawParts
  have partsEq : EbnfValue.star partExpr
      (parts.map (EbnfValue.ruleAtom .postfixPart)) = viewed.2 := by
    rw [partsMapEq]
    exact EbnfValue.star_of_view partExpr viewed.2
  have resultEq : executePostfixRoot file input =
      RuleReduction.foldPostfix file atom parts := by
    change executePostfixLeft file atom parts = _
    exact executePostfixLeft_eq_foldPostfix file atom parts
  rw [resultEq, ← inputEq, ← atomEq, ← partsEq]
  exact .postfix origin finish atom parts

private theorem parameterComptime_map
    {file : WorkspaceFile} {tokens : List Token} :
    ∀ value : Option (MatchedTerminal file tokens
        (.contextualKeyword .comptimeKw)),
      (projects : ∀ terminal, value = some terminal →
        RuleReduction.MarkerProjects file tokens terminal
          .comptimeModifier) →
      (match value, projects with
        | none, _ => none
        | some terminal, evidence => some (RuleReduction.marker terminal
            (evidence terminal rfl))) =
        value.map fun terminal =>
          RuleReduction.terminalLoc terminal .comptimeModifier := by
  intro value
  cases value with
  | none => intro _; rfl
  | some _ => intro _; rfl

theorem executeParameterRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .parameter origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .parameter)) :
    RuleReduction file tokens .parameter origin finish input
      (executeParameterRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let comptimeAtom : EbnfExpr :=
    .atom (.terminal (.contextualKeyword .comptimeKw))
  let nameAtom : EbnfExpr := .atom (.terminal (.category .identifier))
  let colonAtom : EbnfExpr := .atom (.terminal (.symbol .colon))
  let typeAtom : EbnfExpr := .atom (.nonterminal .type)
  let typeChild : EbnfExpr := .sequence [colonAtom, typeAtom]
  change EbnfValue file tokens (.sequence [
    .optional comptimeAtom, nameAtom, .optional typeChild]) at input
  let viewed := EbnfValue.sequence3View
    (.optional comptimeAtom) nameAtom (.optional typeChild) input
  let rawComptime := EbnfValue.optionalView comptimeAtom viewed.1
  let comptime := rawComptime.map
    (EbnfValue.terminalView (.contextualKeyword .comptimeKw))
  let name := EbnfValue.terminalView (.category .identifier) viewed.2.1
  let rawType := EbnfValue.optionalView typeChild viewed.2.2
  let typeValue := rawType.map fun raw =>
    let pair := EbnfValue.sequence2View colonAtom typeAtom raw
    (EbnfValue.terminalView (.symbol .colon) pair.1,
      EbnfValue.ruleView .type pair.2, ())
  let nameData : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier := {
    matched := name
    spelling := name.identifierProjection.1
    parsed := name.identifierProjection.2
  }
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have inputEq := EbnfValue.sequence3_of_view
    (.optional comptimeAtom) nameAtom (.optional typeChild) input
  have comptimeEq : EbnfValue.optional comptimeAtom
      (comptime.map (EbnfValue.terminalAtom
        (.contextualKeyword .comptimeKw))) = viewed.1 := by
    calc
      _ = EbnfValue.optional comptimeAtom rawComptime := by
        congr 1
        cases selected : rawComptime with
        | none => simp [comptime, selected]
        | some raw =>
            simp only [comptime, selected, Option.map]
            exact congrArg some (EbnfValue.terminal_of_view
              (.contextualKeyword .comptimeKw) raw)
      _ = viewed.1 := EbnfValue.optional_of_view comptimeAtom viewed.1
  have nameEq := EbnfValue.terminal_of_view
    (.category .identifier) viewed.2.1
  have typeEq : EbnfValue.optional typeChild
      (typeValue.map fun value =>
        EbnfValue.sequence [colonAtom, typeAtom]
          (EbnfValues.cons colonAtom [typeAtom]
            (EbnfValue.terminalAtom (.symbol .colon) value.1)
            (EbnfValues.cons typeAtom []
              (EbnfValue.ruleAtom .type value.2.1)
              EbnfValues.nil))) = viewed.2.2 := by
    calc
      _ = EbnfValue.optional typeChild rawType := by
        congr 1
        cases selected : rawType with
        | none =>
            simp only [typeValue, selected, Option.map]
        | some raw =>
            simp only [typeValue, selected, Option.map]
            apply congrArg some
            let pair := EbnfValue.sequence2View colonAtom typeAtom raw
            have rawEq := EbnfValue.sequence2_of_view
              colonAtom typeAtom raw
            have colonEq := EbnfValue.terminal_of_view
              (.symbol .colon) pair.1
            have ruleEq := EbnfValue.rule_of_view .type pair.2
            rw [colonEq, ruleEq]
            exact rawEq
      _ = viewed.2.2 := EbnfValue.optional_of_view typeChild viewed.2.2
  have resultEq : executeParameterRoot file tokens origin finish
      ready.1 ready.2.1 input = sourceLoc witness {
        comptime := comptime.map fun terminal =>
          RuleReduction.terminalLoc terminal .comptimeModifier
        name := RuleReduction.terminalLoc name name.identifierProjection.2
        type := typeValue.map fun value => value.2.1
      } := by
    rfl
  have displayInputEq :
      EbnfValue.sequence [
        .optional comptimeAtom, nameAtom, .optional typeChild]
        (EbnfValues.cons (.optional comptimeAtom)
          [nameAtom, .optional typeChild]
          (EbnfValue.optional comptimeAtom
            (comptime.map (EbnfValue.terminalAtom
              (.contextualKeyword .comptimeKw))))
          (EbnfValues.cons nameAtom [.optional typeChild]
            (EbnfValue.terminalAtom (.category .identifier) name)
            (EbnfValues.cons (.optional typeChild) []
              (EbnfValue.optional typeChild
                (typeValue.map fun value =>
                  EbnfValue.sequence [colonAtom, typeAtom]
                    (EbnfValues.cons colonAtom [typeAtom]
                      (EbnfValue.terminalAtom (.symbol .colon) value.1)
                      (EbnfValues.cons typeAtom []
                        (EbnfValue.ruleAtom .type value.2.1)
                        EbnfValues.nil))))
              EbnfValues.nil))) = input := by
    rw [comptimeEq, nameEq, typeEq]
    exact inputEq
  have transportSelf
      (value : EbnfValue file tokens (.sequence [
        .optional comptimeAtom, nameAtom, .optional typeChild]))
      (shape : (.sequence [
        .optional comptimeAtom, nameAtom, .optional typeChild]) =
          m2cV1.rhs .parameter) :
      EbnfValue.transport shape value = value := by
    rw [show shape = (by rfl) from Subsingleton.elim _ _]
    rfl
  let comptimeProjects : ∀ terminal, comptime = some terminal →
      RuleReduction.MarkerProjects file tokens terminal
        .comptimeModifier := fun terminal _ => .comptimeModifier terminal
  have reduces := RuleReduction.parameter origin finish comptime nameData
    typeValue comptimeProjects name.identifierProjection_projects witness
  rw [transportSelf] at reduces
  let relationalComptime : Option Marker :=
    match comptime, comptimeProjects with
    | none, _ => none
    | some terminal, projects => some (RuleReduction.marker terminal
        (projects terminal rfl))
  let relationalOutput : Parameter := sourceLoc witness {
    comptime := relationalComptime
    name := RuleReduction.terminalLoc name name.identifierProjection.2
    type := typeValue.map fun value => value.2.1
  }
  change RuleReduction file tokens .parameter origin finish _
    relationalOutput at reduces
  have outputEq : relationalOutput = sourceLoc witness {
      comptime := comptime.map fun terminal =>
        RuleReduction.terminalLoc terminal .comptimeModifier
      name := RuleReduction.terminalLoc name name.identifierProjection.2
      type := typeValue.map fun value => value.2.1
    } := by
    simp only [relationalOutput, relationalComptime]
    rw [parameterComptime_map comptime comptimeProjects]
  rw [outputEq] at reduces
  simp only [nameData] at reduces
  have constructorInputEq := displayInputEq
  simp only [comptimeAtom, nameAtom, colonAtom, typeAtom, typeChild] at constructorInputEq
  have inputReduces : RuleReduction file tokens .parameter origin finish input
      (sourceLoc witness {
        comptime := comptime.map fun terminal =>
          RuleReduction.terminalLoc terminal .comptimeModifier
        name := RuleReduction.terminalLoc name name.identifierProjection.2
        type := typeValue.map fun value => value.2.1
      }) := constructorInputEq ▸ reduces
  exact resultEq.symm ▸ inputReduces

/-- The data-constructor executor realizes its exact root reduction. -/
theorem executeDataConstructorRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .dataConstructor origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .dataConstructor)) :
    RuleReduction file tokens .dataConstructor origin finish input
      (executeDataConstructorRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let nameAtom : EbnfExpr :=
    .atom (.terminal (.category .identifier))
  let typeAtom : EbnfExpr := .atom (.nonterminal .type)
  let openAtom : EbnfExpr := .atom (.terminal (.symbol .leftParen))
  let fieldsAtom : EbnfExpr := .list1 typeAtom
  let closeAtom : EbnfExpr := .atom (.terminal (.symbol .rightParen))
  let arguments : EbnfExpr :=
    .sequence [openAtom, fieldsAtom, closeAtom]
  change EbnfValue file tokens
    (.sequence [nameAtom, .optional arguments]) at input
  let viewed := EbnfValue.sequence2View
    nameAtom (.optional arguments) input
  let name := EbnfValue.terminalView (.category .identifier) viewed.1
  let nameData : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier := {
    matched := name
    spelling := name.identifierProjection.1
    parsed := name.identifierProjection.2
  }
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have inputEq := EbnfValue.sequence2_of_view
    nameAtom (.optional arguments) input
  have nameEq := EbnfValue.terminal_of_view
    (.category .identifier) viewed.1
  generalize selectedEq :
    EbnfValue.optionalView arguments viewed.2 = selected
  cases selected with
  | none =>
      have optionalEq : EbnfValue.optional arguments none = viewed.2 := by
        calc
          _ = EbnfValue.optional arguments
              (EbnfValue.optionalView arguments viewed.2) := by
                rw [selectedEq]
          _ = viewed.2 := EbnfValue.optional_of_view arguments viewed.2
      have resultEq : executeDataConstructorRoot file tokens
          origin finish ready.1 ready.2.1 input = sourceLoc witness {
        name := RuleReduction.terminalLoc name name.identifierProjection.2
        fields := none
      } := by
        simp [executeDataConstructorRoot, viewed, selectedEq,
          nameAtom, typeAtom, arguments, openAtom, fieldsAtom, closeAtom,
          name, witness]
        rfl
      rw [resultEq, ← inputEq, ← nameEq, ← optionalEq]
      exact .dataConstructorWithoutArguments origin finish nameData
        name.identifierProjection_projects witness
  | some rawArguments =>
      let argumentView := EbnfValue.sequence3View
        openAtom fieldsAtom closeAtom rawArguments
      let openParen := EbnfValue.terminalView
        (.symbol .leftParen) argumentView.1
      let rawFields := EbnfValue.list1View typeAtom argumentView.2.1
      let fields := rawFields.map (EbnfValue.ruleView .type)
      let closeParen := EbnfValue.terminalView
        (.symbol .rightParen) argumentView.2.2
      have optionalEq : EbnfValue.optional arguments
          (some rawArguments) = viewed.2 := by
        calc
          _ = EbnfValue.optional arguments
              (EbnfValue.optionalView arguments viewed.2) := by
                rw [selectedEq]
          _ = viewed.2 := EbnfValue.optional_of_view arguments viewed.2
      have argumentsEq := EbnfValue.sequence3_of_view
        openAtom fieldsAtom closeAtom rawArguments
      have openEq := EbnfValue.terminal_of_view
        (.symbol .leftParen) argumentView.1
      have fieldsMapEq : fields.map (EbnfValue.ruleAtom .type) =
          rawFields := ruleNonemptyAtoms_of_views .type rawFields
      have fieldsEq : EbnfValue.list1 typeAtom
          (fields.map (EbnfValue.ruleAtom .type)) = argumentView.2.1 := by
        rw [fieldsMapEq]
        exact EbnfValue.list1_of_view typeAtom argumentView.2.1
      have closeEq := EbnfValue.terminal_of_view
        (.symbol .rightParen) argumentView.2.2
      have resultEq : executeDataConstructorRoot file tokens
          origin finish ready.1 ready.2.1 input = sourceLoc witness {
        name := RuleReduction.terminalLoc name name.identifierProjection.2
        fields := some fields
      } := by
        simp [executeDataConstructorRoot, viewed, selectedEq,
          argumentView, fields, rawFields, nameAtom, typeAtom, arguments,
          openAtom, fieldsAtom, closeAtom, name, witness]
        rfl
      rw [resultEq, ← inputEq, ← nameEq, ← optionalEq,
        ← argumentsEq, ← openEq, ← fieldsEq, ← closeEq]
      exact .dataConstructorWithArguments origin finish nameData
        openParen fields closeParen name.identifierProjection_projects witness

private theorem identifierAtoms_of_views
    {file : WorkspaceFile} {tokens : List Token}
    (values : NonemptyList (EbnfValue file tokens
      (.atom (.terminal (.category .identifier))))) :
    values.map (fun raw => EbnfValue.terminalAtom
      (.category .identifier) (EbnfValue.terminalView
        (.category .identifier) raw)) = values := by
  cases values with
  | mk head tail =>
      simp [NonemptyList.map, EbnfValue.terminal_of_view]

private abbrev dataDeclIdentifierAtom : EbnfExpr :=
  .atom (.terminal (.category .identifier))

private abbrev dataDeclParameterExpr : EbnfExpr := .sequence [
  .atom (.terminal (.symbol .leftParen)),
  .list1 dataDeclIdentifierAtom,
  .atom (.terminal (.symbol .rightParen))]

private abbrev DataDeclParameterData
    (file : WorkspaceFile) (tokens : List Token) :=
  MatchedTerminal file tokens (.symbol .leftParen) ×
    (NonemptyList (RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier) ×
      (MatchedTerminal file tokens (.symbol .rightParen) × Unit))

private def dataDeclParameterView
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens dataDeclParameterExpr) :
    DataDeclParameterData file tokens :=
  let openAtom : EbnfExpr :=
    .atom (.terminal (.symbol .leftParen))
  let closeAtom : EbnfExpr :=
    .atom (.terminal (.symbol .rightParen))
  let viewed := EbnfValue.sequenceFlatView
    [openAtom, .list1 dataDeclIdentifierAtom, closeAtom] input
  let names := (EbnfValue.list1View dataDeclIdentifierAtom
    viewed.2.1).map fun raw =>
      let terminal := EbnfValue.terminalView
        (.category .identifier) raw
      ({
        matched := terminal
        spelling := terminal.identifierProjection.1
        parsed := terminal.identifierProjection.2
      } : RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)
  (EbnfValue.terminalView (.symbol .leftParen) viewed.1,
    names, EbnfValue.terminalView (.symbol .rightParen) viewed.2.2.1, ())

private def dataDeclParameterInput
    {file : WorkspaceFile} {tokens : List Token}
    (value : DataDeclParameterData file tokens) :
    EbnfValue file tokens dataDeclParameterExpr :=
  let openAtom : EbnfExpr :=
    .atom (.terminal (.symbol .leftParen))
  let closeAtom : EbnfExpr :=
    .atom (.terminal (.symbol .rightParen))
  EbnfValue.sequence [openAtom, .list1 dataDeclIdentifierAtom, closeAtom]
    (EbnfValues.cons openAtom
      [.list1 dataDeclIdentifierAtom, closeAtom]
      (EbnfValue.terminalAtom (.symbol .leftParen) value.1)
      (EbnfValues.cons (.list1 dataDeclIdentifierAtom) [closeAtom]
        (EbnfValue.list1 dataDeclIdentifierAtom
          (value.2.1.map fun name => EbnfValue.terminalAtom
            (.category .identifier) name.matched))
        (EbnfValues.cons closeAtom []
          (EbnfValue.terminalAtom (.symbol .rightParen) value.2.2.1)
          EbnfValues.nil)))

private theorem dataDeclParameterInput_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens dataDeclParameterExpr) :
    dataDeclParameterInput (dataDeclParameterView input) = input := by
  let openAtom : EbnfExpr :=
    .atom (.terminal (.symbol .leftParen))
  let closeAtom : EbnfExpr :=
    .atom (.terminal (.symbol .rightParen))
  let viewed := EbnfValue.sequenceFlatView
    [openAtom, .list1 dataDeclIdentifierAtom, closeAtom] input
  let rawNames := EbnfValue.list1View dataDeclIdentifierAtom viewed.2.1
  have mappedEq :
      ((rawNames.map fun raw =>
        let terminal := EbnfValue.terminalView
          (.category .identifier) raw
        ({
          matched := terminal
          spelling := terminal.identifierProjection.1
          parsed := terminal.identifierProjection.2
        } : RuleReduction.SpelledTerminalData file tokens
          (.category .identifier) Identifier)).map fun name =>
            EbnfValue.terminalAtom
              (.category .identifier) name.matched) = rawNames := by
    cases rawNames with
    | mk head tail =>
        simp [NonemptyList.map, List.map_map, Function.comp_def,
          EbnfValue.terminal_of_view]
  unfold dataDeclParameterInput dataDeclParameterView
  dsimp only
  rw [mappedEq,
    EbnfValue.list1_of_view dataDeclIdentifierAtom viewed.2.1,
    EbnfValue.terminal_of_view,
    EbnfValue.terminal_of_view]
  exact EbnfValue.sequence_of_flat_view
    [openAtom, .list1 dataDeclIdentifierAtom, closeAtom] input

private theorem dataDeclParameterView_projects
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens dataDeclParameterExpr) :
    let value := dataDeclParameterView input
    IdentifierProjects value.2.1.head.matched
      value.2.1.head.spelling value.2.1.head.parsed ∧
    ∀ parameter, parameter ∈ value.2.1.tail →
      IdentifierProjects parameter.matched
        parameter.spelling parameter.parsed := by
  let openAtom : EbnfExpr :=
    .atom (.terminal (.symbol .leftParen))
  let closeAtom : EbnfExpr :=
    .atom (.terminal (.symbol .rightParen))
  let viewed := EbnfValue.sequenceFlatView
    [openAtom, .list1 dataDeclIdentifierAtom, closeAtom] input
  let rawNames := EbnfValue.list1View dataDeclIdentifierAtom viewed.2.1
  constructor
  · exact (EbnfValue.terminalView (.category .identifier)
      rawNames.head).identifierProjection_projects
  · intro parameter parameterMem
    simp only [dataDeclParameterView, NonemptyList.map] at parameterMem
    rcases List.mem_map.mp parameterMem with ⟨raw, _rawMem, rfl⟩
    exact (EbnfValue.terminalView
      (.category .identifier) raw).identifierProjection_projects

private theorem dataDeclParameterResult_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens dataDeclParameterExpr) :
    (let parameterChildren : List EbnfExpr := [
      .atom (.terminal (.symbol .leftParen)),
      .list1 dataDeclIdentifierAtom,
      .atom (.terminal (.symbol .rightParen))]
    let ⟨_, rawNames, _, ⟨⟩⟩ := EbnfValue.sequenceFlatView
      parameterChildren input
    (EbnfValue.list1View dataDeclIdentifierAtom rawNames).map
        (fun value =>
          let terminal := EbnfValue.terminalView
            (.category .identifier) value
          RuleReduction.terminalLoc terminal
            terminal.identifierProjection.2)) =
      (dataDeclParameterView input).2.1.map fun parameter =>
        RuleReduction.terminalLoc parameter.matched parameter.parsed := by
  generalize sequenceEq : EbnfValue.sequenceFlatView [
    .atom (.terminal (.symbol .leftParen)),
    .list1 dataDeclIdentifierAtom,
    .atom (.terminal (.symbol .rightParen))] input = viewed
  rcases viewed with ⟨rawOpen, rawNames, rawClose, ⟨⟩⟩
  simp [dataDeclParameterView, sequenceEq, NonemptyList.map,
    List.map_map, Function.comp_def, RuleReduction.terminalLoc]

private abbrev dataDeclConstructorTail : EbnfExpr :=
  EbnfValue.fixedInfixTailExpr (.symbol .pipe) .dataConstructor

private abbrev dataDeclConstructorExpr : EbnfExpr := .sequence [
  .atom (.terminal (.symbol .equal)),
  .atom (.nonterminal .dataConstructor),
  .star dataDeclConstructorTail]

private abbrev DataDeclConstructorData
    (file : WorkspaceFile) (tokens : List Token) :=
  MatchedTerminal file tokens (.symbol .equal) ×
    (DataConstructor ×
      (List (MatchedTerminal file tokens (.symbol .pipe) ×
        DataConstructor) × Unit))

private def dataDeclConstructorView
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens dataDeclConstructorExpr) :
    DataDeclConstructorData file tokens :=
  let equalAtom : EbnfExpr :=
    .atom (.terminal (.symbol .equal))
  let constructorAtom : EbnfExpr :=
    .atom (.nonterminal .dataConstructor)
  let viewed := EbnfValue.sequence3View equalAtom constructorAtom
    (.star dataDeclConstructorTail) input
  (EbnfValue.terminalView (.symbol .equal) viewed.1,
    EbnfValue.ruleView .dataConstructor viewed.2.1,
    (EbnfValue.starView dataDeclConstructorTail viewed.2.2).map
      (EbnfValue.fixedInfixTailView (.symbol .pipe) .dataConstructor), ())

private def dataDeclConstructorInput
    {file : WorkspaceFile} {tokens : List Token}
    (value : DataDeclConstructorData file tokens) :
    EbnfValue file tokens dataDeclConstructorExpr :=
  let equalAtom : EbnfExpr :=
    .atom (.terminal (.symbol .equal))
  let constructorAtom : EbnfExpr :=
    .atom (.nonterminal .dataConstructor)
  EbnfValue.sequence [equalAtom, constructorAtom,
      .star dataDeclConstructorTail]
    (EbnfValues.cons equalAtom
      [constructorAtom, .star dataDeclConstructorTail]
      (EbnfValue.terminalAtom (.symbol .equal) value.1)
      (EbnfValues.cons constructorAtom [.star dataDeclConstructorTail]
        (EbnfValue.ruleAtom .dataConstructor value.2.1)
        (EbnfValues.cons (.star dataDeclConstructorTail) []
          (EbnfValue.star dataDeclConstructorTail
            (value.2.2.1.map (EbnfValue.fixedInfixTailValue
              (.symbol .pipe) .dataConstructor))) EbnfValues.nil)))

private theorem dataDeclConstructorTails_of_views
    {file : WorkspaceFile} {tokens : List Token}
    (values : List (EbnfValue file tokens dataDeclConstructorTail)) :
    (values.map (EbnfValue.fixedInfixTailView
      (.symbol .pipe) .dataConstructor)).map
        (EbnfValue.fixedInfixTailValue
          (.symbol .pipe) .dataConstructor) = values := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨EbnfValue.fixedInfixTailValue_of_view
        (.symbol .pipe) .dataConstructor head, induction⟩

private theorem dataDeclConstructorInput_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens dataDeclConstructorExpr) :
    dataDeclConstructorInput (dataDeclConstructorView input) = input := by
  let equalAtom : EbnfExpr :=
    .atom (.terminal (.symbol .equal))
  let constructorAtom : EbnfExpr :=
    .atom (.nonterminal .dataConstructor)
  let viewed := EbnfValue.sequence3View equalAtom constructorAtom
    (.star dataDeclConstructorTail) input
  let rawTails := EbnfValue.starView dataDeclConstructorTail viewed.2.2
  have tailsEq : EbnfValue.star dataDeclConstructorTail
      ((rawTails.map (EbnfValue.fixedInfixTailView
        (.symbol .pipe) .dataConstructor)).map
          (EbnfValue.fixedInfixTailValue
            (.symbol .pipe) .dataConstructor)) = viewed.2.2 := by
    rw [dataDeclConstructorTails_of_views rawTails]
    exact EbnfValue.star_of_view dataDeclConstructorTail viewed.2.2
  change EbnfValue.sequence
      [equalAtom, constructorAtom, .star dataDeclConstructorTail]
      (EbnfValues.cons equalAtom
        [constructorAtom, .star dataDeclConstructorTail]
        (EbnfValue.terminalAtom (.symbol .equal)
          (EbnfValue.terminalView (.symbol .equal) viewed.1))
        (EbnfValues.cons constructorAtom [.star dataDeclConstructorTail]
          (EbnfValue.ruleAtom .dataConstructor
            (EbnfValue.ruleView .dataConstructor viewed.2.1))
          (EbnfValues.cons (.star dataDeclConstructorTail) []
            (EbnfValue.star dataDeclConstructorTail
              ((rawTails.map (EbnfValue.fixedInfixTailView
                (.symbol .pipe) .dataConstructor)).map
                  (EbnfValue.fixedInfixTailValue
                    (.symbol .pipe) .dataConstructor))) EbnfValues.nil))) = input
  rw [EbnfValue.terminal_of_view, EbnfValue.rule_of_view, tailsEq]
  exact EbnfValue.sequence3_of_view equalAtom constructorAtom
    (.star dataDeclConstructorTail) input

private theorem dataDeclConstructorResult_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens dataDeclConstructorExpr) :
    let viewed := EbnfValue.sequence3View
      (.atom (.terminal (.symbol .equal)))
      (.atom (.nonterminal .dataConstructor))
      (.star dataDeclConstructorTail) input
    let head : DataConstructor :=
      EbnfValue.ruleView .dataConstructor viewed.2.1
    let tail : List DataConstructor :=
      (EbnfValue.starView dataDeclConstructorTail viewed.2.2).map
        fun rawTail =>
          (EbnfValue.fixedInfixTailView
            (.symbol .pipe) .dataConstructor rawTail).2
    ({ head := head, tail := tail } : NonemptyList DataConstructor) =
      let value := dataDeclConstructorView input
      ({ head := value.2.1, tail := value.2.2.1.map Prod.snd } :
        NonemptyList DataConstructor) := by
  simp [dataDeclConstructorView, List.map_map, Function.comp_def]

private theorem dataDecl_optional_map_of_view
    {file : WorkspaceFile} {tokens : List Token} {alpha : Type}
    (child : EbnfExpr) (decode : EbnfValue file tokens child → alpha)
    (encode : alpha → EbnfValue file tokens child)
    (roundtrip : ∀ raw, encode (decode raw) = raw)
    (input : EbnfValue file tokens (.optional child)) :
    EbnfValue.optional child
      ((EbnfValue.optionalView child input).map decode |>.map encode) =
        input := by
  generalize viewEq : EbnfValue.optionalView child input = viewed
  cases viewed with
  | none =>
      simpa [viewEq] using EbnfValue.optional_of_view child input
  | some raw =>
      simp only [Option.map]
      rw [roundtrip raw]
      simpa [viewEq] using EbnfValue.optional_of_view child input

/-- The type-alias executor realizes its exact root reduction. -/
theorem executeTypeAliasDeclRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .typeAliasDecl origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .typeAliasDecl)) :
    RuleReduction file tokens .typeAliasDecl origin finish input
      (executeTypeAliasDeclRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let identifierAtom : EbnfExpr :=
    .atom (.terminal (.category .identifier))
  let parameterChild : EbnfExpr := .sequence [
    .atom (.terminal (.symbol .leftParen)), .list1 identifierAtom,
    .atom (.terminal (.symbol .rightParen))]
  let children : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .typeKw)), identifierAtom,
    .optional parameterChild, .atom (.terminal (.symbol .equal)),
    .atom (.nonterminal .type),
    .atom (.terminal (.symbol .semicolon))]
  change EbnfValue file tokens (.sequence children) at input
  generalize sequenceEq : EbnfValue.sequenceFlatView children input = viewed
  rcases viewed with ⟨rawTypeKw, rawName, rawOptional,
    rawEqual, rawBody, rawSemicolon, ⟨⟩⟩
  have rawEq := EbnfValue.sequence_of_flat_view children input
  rw [sequenceEq] at rawEq
  let typeKw := EbnfValue.terminalView
    (.hardKeyword .typeKw) rawTypeKw
  let name := EbnfValue.terminalView (.category .identifier) rawName
  let equal := EbnfValue.terminalView (.symbol .equal) rawEqual
  let body := EbnfValue.ruleView .type rawBody
  let semicolon := EbnfValue.terminalView
    (.symbol .semicolon) rawSemicolon
  let nameData : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier := {
    matched := name
    spelling := name.identifierProjection.1
    parsed := name.identifierProjection.2
  }
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  cases selected : EbnfValue.optionalView parameterChild rawOptional with
  | none =>
      have optionalEq : EbnfValue.optional parameterChild none =
          rawOptional := by
        rw [← selected]
        exact EbnfValue.optional_of_view parameterChild rawOptional
      have resultEq : executeTypeAliasDeclRoot file tokens
          origin finish ready.1 ready.2.1 input = sourceLoc witness {
            name := executableTerminalLoc name
              name.identifierProjection.2
            parameters := none
            body := body
          } := by
        have sequenceEq' := sequenceEq
        have selected' := selected
        simp only [children, parameterChild, identifierAtom] at sequenceEq'
        simp only [parameterChild, identifierAtom] at selected'
        simp only [executeTypeAliasDeclRoot, sequenceEq',
          selected', Option.map]
        rfl
      rw [resultEq, ← rawEq,
        ← EbnfValue.terminal_of_view (.hardKeyword .typeKw) rawTypeKw,
        ← EbnfValue.terminal_of_view (.category .identifier) rawName,
        ← optionalEq,
        ← EbnfValue.terminal_of_view (.symbol .equal) rawEqual,
        ← EbnfValue.rule_of_view .type rawBody,
        ← EbnfValue.terminal_of_view (.symbol .semicolon) rawSemicolon]
      exact .typeAliasDecl origin finish typeKw nameData none equal body
        semicolon name.identifierProjection_projects (by simp) witness
  | some rawParameters =>
      have optionalEq : EbnfValue.optional parameterChild
          (some rawParameters) = rawOptional := by
        rw [← selected]
        exact EbnfValue.optional_of_view parameterChild rawOptional
      let parameterChildren : List EbnfExpr := [
        .atom (.terminal (.symbol .leftParen)), .list1 identifierAtom,
        .atom (.terminal (.symbol .rightParen))]
      generalize parameterSequenceEq : EbnfValue.sequenceFlatView
        parameterChildren rawParameters = parameterViewed
      rcases parameterViewed with ⟨rawOpen, rawNames, rawClose, ⟨⟩⟩
      have parametersRawEq := EbnfValue.sequence_of_flat_view
        parameterChildren rawParameters
      rw [parameterSequenceEq] at parametersRawEq
      let openParen := EbnfValue.terminalView
        (.symbol .leftParen) rawOpen
      generalize rawNameValuesEq : EbnfValue.list1View
        identifierAtom rawNames = rawNameValues
      let names : NonemptyList (RuleReduction.SpelledTerminalData
          file tokens (.category .identifier) Identifier) :=
        rawNameValues.map fun raw =>
        let parameter := EbnfValue.terminalView
          (.category .identifier) raw
        let projection := parameter.identifierProjection
        ({
          matched := parameter
          spelling := projection.1
          parsed := projection.2
        } : RuleReduction.SpelledTerminalData file tokens
          (.category .identifier) Identifier)
      let closeParen := EbnfValue.terminalView
        (.symbol .rightParen) rawClose
      let parameters := some (openParen, names, closeParen, ())
      have namesEq : EbnfValue.list1 identifierAtom
          (names.map fun value => EbnfValue.terminalAtom
            (.category .identifier) value.matched) = rawNames := by
        have mappedEq : names.map (fun value => EbnfValue.terminalAtom
            (.category .identifier) value.matched) = rawNameValues := by
          cases rawNameValues
          simp [names, NonemptyList.map, List.map_map,
            Function.comp_def, EbnfValue.terminal_of_view]
        rw [mappedEq]
        rw [← rawNameValuesEq]
        exact EbnfValue.list1_of_view identifierAtom rawNames
      have resultEq : executeTypeAliasDeclRoot file tokens
          origin finish ready.1 ready.2.1 input = sourceLoc witness {
            name := executableTerminalLoc name
              name.identifierProjection.2
            parameters := some (names.map fun parameter =>
              executableTerminalLoc parameter.matched parameter.parsed)
            body := body
          } := by
        have sequenceEq' := sequenceEq
        have selected' := selected
        have parameterSequenceEq' := parameterSequenceEq
        have rawNameValuesEq' := rawNameValuesEq
        simp only [children, parameterChild, identifierAtom] at sequenceEq'
        simp only [parameterChild, identifierAtom] at selected'
        simp only [parameterChildren, identifierAtom] at parameterSequenceEq'
        simp only [identifierAtom] at rawNameValuesEq'
        simp only [executeTypeAliasDeclRoot, sequenceEq', selected',
          Option.map, parameterSequenceEq', rawNameValuesEq']
        cases rawNameValues
        simp [names, NonemptyList.map, List.map_map]
        rfl
      rw [resultEq, ← rawEq,
        ← EbnfValue.terminal_of_view (.hardKeyword .typeKw) rawTypeKw,
        ← EbnfValue.terminal_of_view (.category .identifier) rawName,
        ← optionalEq, ← parametersRawEq,
        ← EbnfValue.terminal_of_view (.symbol .leftParen) rawOpen,
        ← namesEq,
        ← EbnfValue.terminal_of_view (.symbol .rightParen) rawClose,
        ← EbnfValue.terminal_of_view (.symbol .equal) rawEqual,
        ← EbnfValue.rule_of_view .type rawBody,
        ← EbnfValue.terminal_of_view (.symbol .semicolon) rawSemicolon]
      exact .typeAliasDecl origin finish typeKw nameData parameters equal body
        semicolon name.identifierProjection_projects (by
          intro value valueEq
          have valueEq' : value = (openParen, names, closeParen, ()) := by
            apply Option.some.inj
            simpa [parameters] using valueEq.symm
          subst value
          constructor
          · simpa [names, NonemptyList.map] using
              (EbnfValue.terminalView (.category .identifier)
                rawNameValues.head).identifierProjection_projects
          · intro parameter parameterMem
            simp only [names, NonemptyList.map] at parameterMem
            rcases List.mem_map.mp parameterMem with
              ⟨raw, _rawMem, rfl⟩
            exact (EbnfValue.terminalView (.category .identifier)
              raw).identifierProjection_projects)
        witness

/-- The data-declaration executor realizes its exact root reduction. -/
theorem executeDataDeclRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .dataDecl origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .dataDecl)) :
    RuleReduction file tokens .dataDecl origin finish input
      (executeDataDeclRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let dataAtom : EbnfExpr :=
    .atom (.terminal (.hardKeyword .dataKw))
  let semicolonAtom : EbnfExpr :=
    .atom (.terminal (.symbol .semicolon))
  let children : List EbnfExpr := [dataAtom, dataDeclIdentifierAtom,
    .optional dataDeclParameterExpr, .optional dataDeclConstructorExpr,
    semicolonAtom]
  change EbnfValue file tokens (.sequence children) at input
  generalize sequenceEq : EbnfValue.sequenceFlatView children input = viewed
  rcases viewed with ⟨rawData, rawName, rawParameters,
    rawConstructors, rawSemicolon, ⟨⟩⟩
  have inputEq := EbnfValue.sequence_of_flat_view children input
  rw [sequenceEq] at inputEq
  let dataKw := EbnfValue.terminalView (.hardKeyword .dataKw) rawData
  let name := EbnfValue.terminalView (.category .identifier) rawName
  let nameData : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier := {
    matched := name
    spelling := name.identifierProjection.1
    parsed := name.identifierProjection.2
  }
  let parameters := (EbnfValue.optionalView dataDeclParameterExpr
    rawParameters).map dataDeclParameterView
  let constructors := (EbnfValue.optionalView dataDeclConstructorExpr
    rawConstructors).map dataDeclConstructorView
  let semicolon := EbnfValue.terminalView
    (.symbol .semicolon) rawSemicolon
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have parametersEq : EbnfValue.optional dataDeclParameterExpr
      (parameters.map dataDeclParameterInput) = rawParameters := by
    exact dataDecl_optional_map_of_view dataDeclParameterExpr
      dataDeclParameterView dataDeclParameterInput
      dataDeclParameterInput_of_view rawParameters
  have constructorsEq : EbnfValue.optional dataDeclConstructorExpr
      (constructors.map dataDeclConstructorInput) = rawConstructors := by
    exact dataDecl_optional_map_of_view dataDeclConstructorExpr
      dataDeclConstructorView dataDeclConstructorInput
      dataDeclConstructorInput_of_view rawConstructors
  have parameterProjects : ∀ value, parameters = some value →
      IdentifierProjects value.2.1.head.matched
        value.2.1.head.spelling value.2.1.head.parsed ∧
      ∀ parameter, parameter ∈ value.2.1.tail →
        IdentifierProjects parameter.matched
          parameter.spelling parameter.parsed := by
    intro value valueEq
    generalize selectedEq : EbnfValue.optionalView
      dataDeclParameterExpr rawParameters = selected
    cases selected with
    | none => simp [parameters, selectedEq] at valueEq
    | some raw =>
        have valueEq' : value = dataDeclParameterView raw := by
          simpa [parameters, selectedEq] using valueEq.symm
        subst value
        exact dataDeclParameterView_projects raw
  have parametersResultEq :
      (EbnfValue.optionalView dataDeclParameterExpr rawParameters).map
          (fun raw =>
            let parameterChildren : List EbnfExpr := [
              .atom (.terminal (.symbol .leftParen)),
              .list1 dataDeclIdentifierAtom,
              .atom (.terminal (.symbol .rightParen))]
            let ⟨_, rawNames, _, ⟨⟩⟩ := EbnfValue.sequenceFlatView
              parameterChildren raw
            (EbnfValue.list1View dataDeclIdentifierAtom rawNames).map
              fun value =>
                let terminal := EbnfValue.terminalView
                  (.category .identifier) value
                RuleReduction.terminalLoc terminal
                  terminal.identifierProjection.2) =
        parameters.map fun value =>
          value.2.1.map fun parameter => RuleReduction.terminalLoc
            parameter.matched parameter.parsed := by
    generalize selectedEq : EbnfValue.optionalView
      dataDeclParameterExpr rawParameters = selected
    cases selected with
    | none => simp [parameters, selectedEq]
    | some raw =>
        simpa [parameters, selectedEq] using
          dataDeclParameterResult_of_view raw
  have constructorsResultEq :
      (EbnfValue.optionalView dataDeclConstructorExpr rawConstructors).map
          (fun raw =>
            let viewed := EbnfValue.sequence3View
              (.atom (.terminal (.symbol .equal)))
              (.atom (.nonterminal .dataConstructor))
              (.star dataDeclConstructorTail) raw
            let head : DataConstructor :=
              EbnfValue.ruleView .dataConstructor viewed.2.1
            let tail : List DataConstructor :=
              (EbnfValue.starView dataDeclConstructorTail viewed.2.2).map
                fun rawTail =>
                  (EbnfValue.fixedInfixTailView
                    (.symbol .pipe) .dataConstructor rawTail).2
            ({ head := head, tail := tail } :
              NonemptyList DataConstructor)) =
        constructors.map fun value =>
          ({ head := value.2.1, tail := value.2.2.1.map Prod.snd } :
            NonemptyList DataConstructor) := by
    generalize selectedEq : EbnfValue.optionalView
      dataDeclConstructorExpr rawConstructors = selected
    cases selected with
    | none => simp [constructors, selectedEq]
    | some raw =>
        simpa [constructors, selectedEq] using
          dataDeclConstructorResult_of_view raw
  simp only [children, dataAtom, semicolonAtom,
    dataDeclParameterExpr, dataDeclConstructorExpr,
    dataDeclConstructorTail, dataDeclIdentifierAtom,
    EbnfValue.fixedInfixTailExpr] at input sequenceEq inputEq
  simp only [dataDeclParameterExpr, dataDeclIdentifierAtom,
    RuleReduction.terminalLoc] at parametersResultEq
  simp only [dataDeclConstructorExpr, dataDeclConstructorTail,
    EbnfValue.fixedInfixTailExpr,
    EbnfValue.fixedInfixTailView] at constructorsResultEq
  have resultEq : executeDataDeclRoot file tokens origin finish
      ready.1 ready.2.1 input = sourceLoc witness {
        name := RuleReduction.terminalLoc name name.identifierProjection.2
        parameters := parameters.map fun value =>
          value.2.1.map fun parameter => RuleReduction.terminalLoc
            parameter.matched parameter.parsed
        constructors := constructors.map fun value => {
          head := value.2.1
          tail := value.2.2.1.map Prod.snd
        }
      } := by
    simp only [executeDataDeclRoot]
    rw [sequenceEq]
    simp only
    change @Eq (Located DataDeclPayload) _ _
    apply (sourceLoc_eq_iff _ _ _ _).2
    simpa [name, RuleReduction.terminalLoc,
      parametersResultEq, constructorsResultEq]
  rw [resultEq, ← inputEq]
  simp only [EbnfValue.sequenceValuesBuild]
  rw [← EbnfValue.terminal_of_view (.hardKeyword .dataKw) rawData,
    ← EbnfValue.terminal_of_view (.category .identifier) rawName,
    ← parametersEq, ← constructorsEq,
    ← EbnfValue.terminal_of_view (.symbol .semicolon) rawSemicolon]
  have transportSelf
      (value : EbnfValue file tokens (.sequence [
        .atom (.terminal (.hardKeyword .dataKw)),
        .atom (.terminal (.category .identifier)),
        .optional (.sequence [
          .atom (.terminal (.symbol .leftParen)),
          .list1 (.atom (.terminal (.category .identifier))),
          .atom (.terminal (.symbol .rightParen))]),
        .optional (.sequence [
          .atom (.terminal (.symbol .equal)),
          .atom (.nonterminal .dataConstructor),
          .star (.group (.sequence [
            .atom (.terminal (.symbol .pipe)),
            .atom (.nonterminal .dataConstructor)]))]),
        .atom (.terminal (.symbol .semicolon))]))
      (shape : (.sequence [
        .atom (.terminal (.hardKeyword .dataKw)),
        .atom (.terminal (.category .identifier)),
        .optional (.sequence [
          .atom (.terminal (.symbol .leftParen)),
          .list1 (.atom (.terminal (.category .identifier))),
          .atom (.terminal (.symbol .rightParen))]),
        .optional (.sequence [
          .atom (.terminal (.symbol .equal)),
          .atom (.nonterminal .dataConstructor),
          .star (.group (.sequence [
            .atom (.terminal (.symbol .pipe)),
            .atom (.nonterminal .dataConstructor)]))]),
        .atom (.terminal (.symbol .semicolon))]) =
          m2cV1.rhs .dataDecl) :
      EbnfValue.transport shape value = value := by
    rw [show shape = (by rfl) from Subsingleton.elim _ _]
    rfl
  have reduces := RuleReduction.dataDecl origin finish dataKw nameData
    parameters constructors semicolon name.identifierProjection_projects
    parameterProjects witness
  rw [transportSelf] at reduces
  exact reduces

/-- The contract-declaration executor realizes its exact root reduction. -/
theorem executeContractDeclRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .contractDecl origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .contractDecl)) :
    RuleReduction file tokens .contractDecl origin finish input
      (executeContractDeclRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let identifierAtom : EbnfExpr :=
    .atom (.terminal (.category .identifier))
  let parameterChild : EbnfExpr := .sequence [
    .atom (.terminal (.symbol .leftParen)), .list1 identifierAtom,
    .atom (.terminal (.symbol .rightParen))]
  let memberAtom : EbnfExpr := .atom (.nonterminal .contractMember)
  let children : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .contractKw)), identifierAtom,
    .optional parameterChild,
    .atom (.terminal (.symbol .leftBrace)), .star memberAtom,
    .atom (.terminal (.symbol .rightBrace))]
  change EbnfValue file tokens (.sequence children) at input
  generalize sequenceEq : EbnfValue.sequenceFlatView children input = viewed
  rcases viewed with ⟨rawContract, rawName, rawOptional,
    rawOpen, rawMembers, rawClose, ⟨⟩⟩
  have rawEq := EbnfValue.sequence_of_flat_view children input
  rw [sequenceEq] at rawEq
  let contractKw := EbnfValue.terminalView
    (.hardKeyword .contractKw) rawContract
  let name := EbnfValue.terminalView (.category .identifier) rawName
  let openBrace := EbnfValue.terminalView (.symbol .leftBrace) rawOpen
  let rawMemberValues := EbnfValue.starView memberAtom rawMembers
  let members := rawMemberValues.map
    (EbnfValue.ruleView .contractMember)
  let closeBrace := EbnfValue.terminalView (.symbol .rightBrace) rawClose
  let nameData : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier := {
    matched := name
    spelling := name.identifierProjection.1
    parsed := name.identifierProjection.2
  }
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have memberValuesEq : members.map
      (EbnfValue.ruleAtom .contractMember) = rawMemberValues :=
    ruleAtoms_of_views .contractMember rawMemberValues
  have membersEq : EbnfValue.star memberAtom
      (members.map (EbnfValue.ruleAtom .contractMember)) = rawMembers := by
    rw [memberValuesEq]
    exact EbnfValue.star_of_view memberAtom rawMembers
  cases selected : EbnfValue.optionalView parameterChild rawOptional with
  | none =>
      have optionalEq : EbnfValue.optional parameterChild none =
          rawOptional := by
        rw [← selected]
        exact EbnfValue.optional_of_view parameterChild rawOptional
      have resultEq : executeContractDeclRoot file tokens origin finish
          ready.1 ready.2.1 input = sourceLoc witness {
            name := executableTerminalLoc name name.identifierProjection.2
            parameters := none
            members := members
          } := by
        have sequenceEq' := sequenceEq
        have selected' := selected
        simp only [children, parameterChild, identifierAtom,
          memberAtom] at sequenceEq'
        simp only [parameterChild, identifierAtom] at selected'
        simp only [executeContractDeclRoot, sequenceEq', selected',
          Option.map, rawMemberValues, members]
        rfl
      rw [resultEq, ← rawEq,
        ← EbnfValue.terminal_of_view (.hardKeyword .contractKw) rawContract,
        ← EbnfValue.terminal_of_view (.category .identifier) rawName,
        ← optionalEq,
        ← EbnfValue.terminal_of_view (.symbol .leftBrace) rawOpen,
        ← membersEq,
        ← EbnfValue.terminal_of_view (.symbol .rightBrace) rawClose]
      exact .contractDecl origin finish contractKw nameData none
        openBrace members closeBrace name.identifierProjection_projects
        (by simp) witness
  | some rawParameters =>
      have optionalEq : EbnfValue.optional parameterChild
          (some rawParameters) = rawOptional := by
        rw [← selected]
        exact EbnfValue.optional_of_view parameterChild rawOptional
      let parameterChildren : List EbnfExpr := [
        .atom (.terminal (.symbol .leftParen)), .list1 identifierAtom,
        .atom (.terminal (.symbol .rightParen))]
      generalize parameterSequenceEq : EbnfValue.sequenceFlatView
        parameterChildren rawParameters = parameterViewed
      rcases parameterViewed with ⟨rawParameterOpen, rawNames,
        rawParameterClose, ⟨⟩⟩
      have parametersRawEq := EbnfValue.sequence_of_flat_view
        parameterChildren rawParameters
      rw [parameterSequenceEq] at parametersRawEq
      let parameterOpen := EbnfValue.terminalView
        (.symbol .leftParen) rawParameterOpen
      generalize rawNameValuesEq : EbnfValue.list1View
        identifierAtom rawNames = rawNameValues
      let names : NonemptyList (RuleReduction.SpelledTerminalData
          file tokens (.category .identifier) Identifier) :=
        rawNameValues.map fun raw =>
        let parameter := EbnfValue.terminalView (.category .identifier) raw
        let projection := parameter.identifierProjection
        ({
          matched := parameter
          spelling := projection.1
          parsed := projection.2
        } : RuleReduction.SpelledTerminalData file tokens
          (.category .identifier) Identifier)
      let parameterClose := EbnfValue.terminalView
        (.symbol .rightParen) rawParameterClose
      let parameters := some (parameterOpen, names, parameterClose, ())
      have namesEq : EbnfValue.list1 identifierAtom
          (names.map fun value => EbnfValue.terminalAtom
            (.category .identifier) value.matched) = rawNames := by
        have mappedEq : names.map (fun value => EbnfValue.terminalAtom
            (.category .identifier) value.matched) = rawNameValues := by
          cases rawNameValues
          simp [names, NonemptyList.map, List.map_map,
            Function.comp_def, EbnfValue.terminal_of_view]
        rw [mappedEq, ← rawNameValuesEq]
        exact EbnfValue.list1_of_view identifierAtom rawNames
      have resultEq : executeContractDeclRoot file tokens origin finish
          ready.1 ready.2.1 input = sourceLoc witness {
            name := executableTerminalLoc name name.identifierProjection.2
            parameters := some (names.map fun parameter =>
              executableTerminalLoc parameter.matched parameter.parsed)
            members := members
          } := by
        have sequenceEq' := sequenceEq
        have selected' := selected
        have parameterSequenceEq' := parameterSequenceEq
        have rawNameValuesEq' := rawNameValuesEq
        simp only [children, parameterChild, identifierAtom,
          memberAtom] at sequenceEq'
        simp only [parameterChild, identifierAtom] at selected'
        simp only [parameterChildren, identifierAtom] at parameterSequenceEq'
        simp only [identifierAtom] at rawNameValuesEq'
        simp only [executeContractDeclRoot, sequenceEq', selected',
          Option.map, parameterSequenceEq', rawNameValuesEq',
          rawMemberValues, members]
        cases rawNameValues
        simp [names, NonemptyList.map, List.map_map]
        rfl
      rw [resultEq, ← rawEq,
        ← EbnfValue.terminal_of_view (.hardKeyword .contractKw) rawContract,
        ← EbnfValue.terminal_of_view (.category .identifier) rawName,
        ← optionalEq, ← parametersRawEq,
        ← EbnfValue.terminal_of_view
          (.symbol .leftParen) rawParameterOpen,
        ← namesEq,
        ← EbnfValue.terminal_of_view
          (.symbol .rightParen) rawParameterClose,
        ← EbnfValue.terminal_of_view (.symbol .leftBrace) rawOpen,
        ← membersEq,
        ← EbnfValue.terminal_of_view (.symbol .rightBrace) rawClose]
      exact .contractDecl origin finish contractKw nameData parameters
        openBrace members closeBrace name.identifierProjection_projects (by
          intro value valueEq
          have valueEq' : value =
              (parameterOpen, names, parameterClose, ()) := by
            apply Option.some.inj
            simpa [parameters] using valueEq.symm
          subst value
          constructor
          · simpa [names, NonemptyList.map] using
              (EbnfValue.terminalView (.category .identifier)
                rawNameValues.head).identifierProjection_projects
          · intro parameter parameterMem
            simp only [names, NonemptyList.map] at parameterMem
            rcases List.mem_map.mp parameterMem with ⟨raw, _rawMem, rfl⟩
            exact (EbnfValue.terminalView
              (.category .identifier) raw).identifierProjection_projects)
        witness

/-- The field-declaration executor realizes its exact root reduction. -/
theorem executeFieldDeclRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .fieldDecl origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .fieldDecl)) :
    RuleReduction file tokens .fieldDecl origin finish input
      (executeFieldDeclRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let nameAtom : EbnfExpr :=
    .atom (.terminal (.category .identifier))
  let colonAtom : EbnfExpr := .atom (.terminal (.symbol .colon))
  let typeAtom : EbnfExpr := .atom (.nonterminal .type)
  let equalAtom : EbnfExpr := .atom (.terminal (.symbol .equal))
  let expressionAtom : EbnfExpr := .atom (.nonterminal .expression)
  let initializerChild : EbnfExpr :=
    .sequence [equalAtom, expressionAtom]
  let semicolonAtom : EbnfExpr := .atom (.terminal (.symbol .semicolon))
  let children : List EbnfExpr := [nameAtom, colonAtom, typeAtom,
    .optional initializerChild, semicolonAtom]
  change EbnfValue file tokens (.sequence children) at input
  generalize sequenceEq : EbnfValue.sequenceFlatView children input = values
  rcases values with
    ⟨rawName, rawColon, rawType, rawOptional, rawSemicolon, ⟨⟩⟩
  have inputEq := EbnfValue.sequence_of_flat_view children input
  rw [sequenceEq] at inputEq
  let name := EbnfValue.terminalView (.category .identifier) rawName
  let colon := EbnfValue.terminalView (.symbol .colon) rawColon
  let typeValue := EbnfValue.ruleView .type rawType
  let rawInitializer := EbnfValue.optionalView initializerChild
    rawOptional
  let initializer := rawInitializer.map fun raw =>
    let pair := EbnfValue.sequence2View equalAtom expressionAtom raw
    (EbnfValue.terminalView (.symbol .equal) pair.1,
      EbnfValue.ruleView .expression pair.2, ())
  let semicolon := EbnfValue.terminalView
    (.symbol .semicolon) rawSemicolon
  let nameData : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier := {
    matched := name
    spelling := name.identifierProjection.1
    parsed := name.identifierProjection.2
  }
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have nameEq := EbnfValue.terminal_of_view
    (.category .identifier) rawName
  have colonEq := EbnfValue.terminal_of_view
    (.symbol .colon) rawColon
  have typeEq := EbnfValue.rule_of_view .type rawType
  have initializerEq : EbnfValue.optional initializerChild
      (initializer.map fun value =>
        EbnfValue.sequence [equalAtom, expressionAtom]
          (EbnfValues.cons equalAtom [expressionAtom]
            (EbnfValue.terminalAtom (.symbol .equal) value.1)
            (EbnfValues.cons expressionAtom []
              (EbnfValue.ruleAtom .expression value.2.1)
              EbnfValues.nil))) = rawOptional := by
    calc
      _ = EbnfValue.optional initializerChild rawInitializer := by
        congr 1
        cases selected : rawInitializer with
        | none => simp only [initializer, selected, Option.map]
        | some raw =>
            simp only [initializer, selected, Option.map]
            apply congrArg some
            let pair := EbnfValue.sequence2View
              equalAtom expressionAtom raw
            have rawEq := EbnfValue.sequence2_of_view
              equalAtom expressionAtom raw
            have equalEq := EbnfValue.terminal_of_view
              (.symbol .equal) pair.1
            have expressionEq := EbnfValue.rule_of_view
              .expression pair.2
            rw [equalEq, expressionEq]
            exact rawEq
      _ = rawOptional :=
        EbnfValue.optional_of_view initializerChild rawOptional
  have semicolonEq := EbnfValue.terminal_of_view
    (.symbol .semicolon) rawSemicolon
  have resultEq : executeFieldDeclRoot file tokens origin finish
      ready.1 ready.2.1 input = sourceLoc witness {
    name := RuleReduction.terminalLoc name name.identifierProjection.2
    type := typeValue
    initializer := initializer.map fun value => value.2.1
  } := by
    simp [executeFieldDeclRoot, children, sequenceEq, nameAtom, colonAtom,
      typeAtom, equalAtom, expressionAtom, initializerChild, semicolonAtom,
      initializer, rawInitializer, name, typeValue, witness]
    rfl
  rw [resultEq, ← inputEq, ← nameEq, ← colonEq, ← typeEq,
    ← initializerEq, ← semicolonEq]
  exact .fieldDecl origin finish nameData colon typeValue initializer
    semicolon name.identifierProjection_projects witness
private theorem fallbackDecl_marker_fields_eq
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (genericPrefix : Option GenericPrefix)
    (publicToken : Option (MatchedTerminal file tokens
      (.hardKeyword .publicKw)))
    (payableToken : Option (MatchedTerminal file tokens
      (.hardKeyword .payableKw)))
    (fallbackKw : MatchedTerminal file tokens
      (.hardKeyword .fallbackKw))
    (parameters : List Parameter) (returnType : Option TypeExpr)
    (body : Body)
    (publicProjects : ∀ matched, publicToken = some matched →
      RuleReduction.MarkerProjects file tokens matched .publicModifier)
    (payableProjects : ∀ matched, payableToken = some matched →
      RuleReduction.MarkerProjects file tokens matched .payableModifier)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    sourceLoc witness ({
      genericPrefix := genericPrefix
      «public» := match publicToken, publicProjects with
        | none, _ => none
        | some terminal, evidence => some (RuleReduction.marker terminal
            (evidence terminal rfl))
      payable := match payableToken, payableProjects with
        | none, _ => none
        | some terminal, evidence => some (RuleReduction.marker terminal
            (evidence terminal rfl))
      marker := RuleReduction.marker fallbackKw (.fallbackName fallbackKw)
      parameters := parameters
      returnType := returnType
      body := body
    } : FallbackDeclPayload) = sourceLoc witness ({
      genericPrefix := genericPrefix
      «public» := publicToken.map fun terminal =>
        RuleReduction.terminalLoc terminal .publicModifier
      payable := payableToken.map fun terminal =>
        RuleReduction.terminalLoc terminal .payableModifier
      marker := RuleReduction.terminalLoc fallbackKw .fallbackName
      parameters := parameters
      returnType := returnType
      body := body
    } : FallbackDeclPayload) := by
  cases publicToken <;> cases payableToken <;> rfl

/-- The fallback-declaration executor realizes its exact root reduction. -/
theorem executeFallbackDeclRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .fallbackDecl origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .fallbackDecl)) :
    RuleReduction file tokens .fallbackDecl origin finish input
      (executeFallbackDeclRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let genericAtom : EbnfExpr := .atom (.nonterminal .genericPrefix)
  let publicAtom : EbnfExpr :=
    .atom (.terminal (.hardKeyword .publicKw))
  let payableAtom : EbnfExpr :=
    .atom (.terminal (.hardKeyword .payableKw))
  let parameterAtom : EbnfExpr := .atom (.nonterminal .parameter)
  let returnChild : EbnfExpr := .sequence [
    .atom (.terminal (.symbol .arrow)), .atom (.nonterminal .type)]
  let children : List EbnfExpr := [.optional genericAtom,
    .optional publicAtom, .optional payableAtom,
    .atom (.terminal (.hardKeyword .fallbackKw)),
    .atom (.terminal (.symbol .leftParen)), .list0 parameterAtom,
    .atom (.terminal (.symbol .rightParen)), .optional returnChild,
    .atom (.nonterminal .body)]
  change EbnfValue file tokens (.sequence children) at input
  generalize sequenceEq : EbnfValue.sequenceFlatView children input = values
  rcases values with ⟨rawGeneric, rawPublic, rawPayable, rawFallback,
    rawOpen, rawParameters, rawClose, rawReturn, rawBody, ⟨⟩⟩
  have inputEq := EbnfValue.sequence_of_flat_view children input
  rw [sequenceEq] at inputEq
  let rawGenericValue := EbnfValue.optionalView genericAtom rawGeneric
  let genericPrefix := rawGenericValue.map
    (EbnfValue.ruleView .genericPrefix)
  let rawPublicValue := EbnfValue.optionalView publicAtom rawPublic
  let publicToken := rawPublicValue.map
    (EbnfValue.terminalView (.hardKeyword .publicKw))
  let rawPayableValue := EbnfValue.optionalView payableAtom rawPayable
  let payableToken := rawPayableValue.map
    (EbnfValue.terminalView (.hardKeyword .payableKw))
  let fallbackKw := EbnfValue.terminalView
    (.hardKeyword .fallbackKw) rawFallback
  let openParen := EbnfValue.terminalView (.symbol .leftParen) rawOpen
  let rawParameterValues := EbnfValue.list0View
    parameterAtom rawParameters
  let parameters := rawParameterValues.map (EbnfValue.ruleView .parameter)
  let closeParen := EbnfValue.terminalView (.symbol .rightParen) rawClose
  let rawReturnValue := EbnfValue.optionalView returnChild rawReturn
  let returnValue := rawReturnValue.map fun raw =>
    let pair := EbnfValue.sequence2View
      (.atom (.terminal (.symbol .arrow)))
      (.atom (.nonterminal .type)) raw
    (EbnfValue.terminalView (.symbol .arrow) pair.1,
      EbnfValue.ruleView .type pair.2, ())
  let body := EbnfValue.ruleView .body rawBody
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have genericEq : EbnfValue.optional genericAtom
      (genericPrefix.map (EbnfValue.ruleAtom .genericPrefix)) =
        rawGeneric := by
    calc
      _ = EbnfValue.optional genericAtom rawGenericValue := by
        congr 1
        cases selected : rawGenericValue with
        | none => simp [genericPrefix, selected]
        | some raw => simp [genericPrefix, selected,
            EbnfValue.rule_of_view]
      _ = rawGeneric := EbnfValue.optional_of_view genericAtom rawGeneric
  have publicEq : EbnfValue.optional publicAtom
      (publicToken.map (EbnfValue.terminalAtom
        (.hardKeyword .publicKw))) = rawPublic := by
    calc
      _ = EbnfValue.optional publicAtom rawPublicValue := by
        congr 1
        cases selected : rawPublicValue with
        | none => simp [publicToken, selected]
        | some raw => simp [publicToken, selected,
            EbnfValue.terminal_of_view]
      _ = rawPublic := EbnfValue.optional_of_view publicAtom rawPublic
  have payableEq : EbnfValue.optional payableAtom
      (payableToken.map (EbnfValue.terminalAtom
        (.hardKeyword .payableKw))) = rawPayable := by
    calc
      _ = EbnfValue.optional payableAtom rawPayableValue := by
        congr 1
        cases selected : rawPayableValue with
        | none => simp [payableToken, selected]
        | some raw => simp [payableToken, selected,
            EbnfValue.terminal_of_view]
      _ = rawPayable := EbnfValue.optional_of_view payableAtom rawPayable
  have parameterMapEq : parameters.map
      (EbnfValue.ruleAtom .parameter) = rawParameterValues :=
    shortRuleAtoms_of_views .parameter rawParameterValues
  have parametersEq : EbnfValue.list0 parameterAtom
      (parameters.map (EbnfValue.ruleAtom .parameter)) = rawParameters := by
    rw [parameterMapEq]
    exact EbnfValue.list0_of_view parameterAtom rawParameters
  have returnValuesEq : (returnValue.map fun value =>
      EbnfValue.sequence [
          .atom (.terminal (.symbol .arrow)),
          .atom (.nonterminal .type)]
        (EbnfValues.cons (.atom (.terminal (.symbol .arrow)))
          [.atom (.nonterminal .type)]
          (EbnfValue.terminalAtom (.symbol .arrow) value.1)
          (EbnfValues.cons (.atom (.nonterminal .type)) []
            (EbnfValue.ruleAtom .type value.2.1) EbnfValues.nil))) =
        rawReturnValue := by
    cases selected : rawReturnValue with
    | none => simp [returnValue, selected]
    | some raw =>
        let pair := EbnfValue.sequence2View
          (.atom (.terminal (.symbol .arrow)))
          (.atom (.nonterminal .type)) raw
        simp only [returnValue, selected, Option.map]
        apply congrArg some
        rw [EbnfValue.terminal_of_view (.symbol .arrow) pair.1,
          EbnfValue.rule_of_view .type pair.2]
        exact EbnfValue.sequence2_of_view
          (.atom (.terminal (.symbol .arrow)))
          (.atom (.nonterminal .type)) raw
  have returnEq : EbnfValue.optional returnChild
      (returnValue.map fun value =>
        EbnfValue.sequence [
            .atom (.terminal (.symbol .arrow)),
            .atom (.nonterminal .type)]
          (EbnfValues.cons (.atom (.terminal (.symbol .arrow)))
            [.atom (.nonterminal .type)]
            (EbnfValue.terminalAtom (.symbol .arrow) value.1)
            (EbnfValues.cons (.atom (.nonterminal .type)) []
              (EbnfValue.ruleAtom .type value.2.1) EbnfValues.nil))) =
        rawReturn := by
    rw [returnValuesEq]
    exact EbnfValue.optional_of_view returnChild rawReturn
  let publicProjects : ∀ terminal, publicToken = some terminal →
      RuleReduction.MarkerProjects file tokens terminal
        .publicModifier := fun terminal _ => .publicModifier terminal
  let payableProjects : ∀ terminal, payableToken = some terminal →
      RuleReduction.MarkerProjects file tokens terminal
        .payableModifier := fun terminal _ => .payableModifier terminal
  let rebuilt : EbnfValue file tokens (.sequence children) :=
    EbnfValue.sequence children (EbnfValue.sequenceValuesBuild children
      (EbnfValue.optional genericAtom
          (genericPrefix.map (EbnfValue.ruleAtom .genericPrefix)),
        EbnfValue.optional publicAtom
          (publicToken.map (EbnfValue.terminalAtom
            (.hardKeyword .publicKw))),
        EbnfValue.optional payableAtom
          (payableToken.map (EbnfValue.terminalAtom
            (.hardKeyword .payableKw))),
        EbnfValue.terminalAtom (.hardKeyword .fallbackKw) fallbackKw,
        EbnfValue.terminalAtom (.symbol .leftParen) openParen,
        EbnfValue.list0 parameterAtom
          (parameters.map (EbnfValue.ruleAtom .parameter)),
        EbnfValue.terminalAtom (.symbol .rightParen) closeParen,
        EbnfValue.optional returnChild (returnValue.map fun value =>
          EbnfValue.sequence [
              .atom (.terminal (.symbol .arrow)),
              .atom (.nonterminal .type)]
            (EbnfValues.cons (.atom (.terminal (.symbol .arrow)))
              [.atom (.nonterminal .type)]
              (EbnfValue.terminalAtom (.symbol .arrow) value.1)
              (EbnfValues.cons (.atom (.nonterminal .type)) []
                (EbnfValue.ruleAtom .type value.2.1) EbnfValues.nil))),
        EbnfValue.ruleAtom .body body, ()))
  have rebuiltEq : rebuilt = input := by
    dsimp only [rebuilt]
    rw [genericEq, publicEq, payableEq,
      EbnfValue.terminal_of_view (.hardKeyword .fallbackKw) rawFallback,
      EbnfValue.terminal_of_view (.symbol .leftParen) rawOpen,
      parametersEq,
      EbnfValue.terminal_of_view (.symbol .rightParen) rawClose,
      returnEq, EbnfValue.rule_of_view .body rawBody]
    exact inputEq
  have transportSelf
      (value : EbnfValue file tokens (.sequence children))
      (shape : (.sequence children) = m2cV1.rhs .fallbackDecl) :
      EbnfValue.transport shape value = value := by
    rw [show shape = (by rfl) from Subsingleton.elim _ _]
    rfl
  have reduces := RuleReduction.fallbackDecl origin finish genericPrefix
    publicToken payableToken fallbackKw openParen parameters closeParen
    returnValue body publicProjects payableProjects
    (.fallbackName fallbackKw) witness
  have outputEq := fallbackDecl_marker_fields_eq genericPrefix publicToken
    payableToken fallbackKw parameters
    (returnValue.map fun value => value.2.1) body publicProjects
    payableProjects witness
  have normalizedReduces := outputEq ▸ reduces
  rw [transportSelf] at normalizedReduces
  have resultEq : executeFallbackDeclRoot file tokens origin finish
      ready.1 ready.2.1 input = sourceLoc witness {
        genericPrefix := genericPrefix
        «public» := publicToken.map fun terminal =>
          RuleReduction.terminalLoc terminal .publicModifier
        payable := payableToken.map fun terminal =>
          RuleReduction.terminalLoc terminal .payableModifier
        marker := RuleReduction.terminalLoc fallbackKw .fallbackName
        parameters := parameters
        returnType := returnValue.map fun value => value.2.1
        body := body
      } := by
    have sequenceEq' := sequenceEq
    simp only [children, genericAtom, publicAtom, payableAtom,
      parameterAtom, returnChild] at sequenceEq'
    simp [executeFallbackDeclRoot, sequenceEq', genericPrefix,
      publicToken, payableToken, fallbackKw, parameters, returnValue,
      body, witness]
    rfl
  have constructorInputEq := rebuiltEq
  simp only [rebuilt, children, genericAtom, publicAtom, payableAtom,
    parameterAtom, returnChild, EbnfValue.sequenceValuesBuild]
    at constructorInputEq
  have inputReduces : RuleReduction file tokens .fallbackDecl origin finish
      input (sourceLoc witness {
        genericPrefix := genericPrefix
        «public» := publicToken.map fun terminal =>
          RuleReduction.terminalLoc terminal .publicModifier
        payable := payableToken.map fun terminal =>
          RuleReduction.terminalLoc terminal .payableModifier
        marker := RuleReduction.terminalLoc fallbackKw .fallbackName
        parameters := parameters
        returnType := returnValue.map fun value => value.2.1
        body := body
      }) := constructorInputEq ▸ normalizedReduces
  exact resultEq.symm ▸ inputReduces

private theorem contractConstructorRuleAtoms_of_views
    {file : WorkspaceFile} {tokens : List Token}
    (inputs : List (EbnfValue file tokens
      (.atom (.nonterminal .parameter)))) :
    (inputs.map (EbnfValue.ruleView .parameter)).map
        (EbnfValue.ruleAtom .parameter) = inputs := by
  induction inputs with
  | nil => rfl
  | cons head tail induction =>
      simp [EbnfValue.rule_of_view, induction]

private theorem contractConstructorDecl_marker_fields_eq
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (publicToken : Option (MatchedTerminal file tokens
      (.hardKeyword .publicKw)))
    (payableToken : Option (MatchedTerminal file tokens
      (.hardKeyword .payableKw)))
    (constructorKw : MatchedTerminal file tokens
      (.hardKeyword .constructorKw))
    (parameters : List Parameter) (body : Body)
    (publicProjects : ∀ matched, publicToken = some matched →
      RuleReduction.MarkerProjects file tokens matched .publicModifier)
    (payableProjects : ∀ matched, payableToken = some matched →
      RuleReduction.MarkerProjects file tokens matched .payableModifier)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    sourceLoc witness ({
      «public» := match publicToken, publicProjects with
        | none, _ => none
        | some terminal, evidence => some (RuleReduction.marker terminal
            (evidence terminal rfl))
      payable := match payableToken, payableProjects with
        | none, _ => none
        | some terminal, evidence => some (RuleReduction.marker terminal
            (evidence terminal rfl))
      marker := RuleReduction.marker constructorKw
        (.contractConstructorName constructorKw)
      parameters := parameters
      body := body
    } : ContractConstructorDeclPayload) = sourceLoc witness ({
      «public» := publicToken.map fun terminal =>
        RuleReduction.terminalLoc terminal .publicModifier
      payable := payableToken.map fun terminal =>
        RuleReduction.terminalLoc terminal .payableModifier
      marker := RuleReduction.terminalLoc constructorKw
        .contractConstructorName
      parameters := parameters
      body := body
    } : ContractConstructorDeclPayload) := by
  cases publicToken <;> cases payableToken <;> rfl

/-- The contract-constructor executor realizes its exact root reduction. -/
theorem executeContractConstructorDeclRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .contractConstructorDecl
      origin finish)
    (input : EbnfValue file tokens
      (m2cV1.rhs .contractConstructorDecl)) :
    RuleReduction file tokens .contractConstructorDecl origin finish input
      (executeContractConstructorDeclRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let publicAtom : EbnfExpr :=
    .atom (.terminal (.hardKeyword .publicKw))
  let payableAtom : EbnfExpr :=
    .atom (.terminal (.hardKeyword .payableKw))
  let parameterAtom : EbnfExpr := .atom (.nonterminal .parameter)
  let children : List EbnfExpr := [.optional publicAtom,
    .optional payableAtom,
    .atom (.terminal (.hardKeyword .constructorKw)),
    .atom (.terminal (.symbol .leftParen)), .list0 parameterAtom,
    .atom (.terminal (.symbol .rightParen)),
    .atom (.nonterminal .body)]
  change EbnfValue file tokens (.sequence children) at input
  generalize sequenceEq : EbnfValue.sequenceFlatView children input = values
  rcases values with ⟨rawPublic, rawPayable, rawConstructor, rawOpen,
    rawParameters, rawClose, rawBody, ⟨⟩⟩
  have inputEq := EbnfValue.sequence_of_flat_view children input
  rw [sequenceEq] at inputEq
  let rawPublicValue := EbnfValue.optionalView publicAtom rawPublic
  let publicToken := rawPublicValue.map
    (EbnfValue.terminalView (.hardKeyword .publicKw))
  let rawPayableValue := EbnfValue.optionalView payableAtom rawPayable
  let payableToken := rawPayableValue.map
    (EbnfValue.terminalView (.hardKeyword .payableKw))
  let constructorKw := EbnfValue.terminalView
    (.hardKeyword .constructorKw) rawConstructor
  let openParen := EbnfValue.terminalView (.symbol .leftParen) rawOpen
  let rawParameterValues := EbnfValue.list0View
    parameterAtom rawParameters
  let parameters := rawParameterValues.map (EbnfValue.ruleView .parameter)
  let closeParen := EbnfValue.terminalView (.symbol .rightParen) rawClose
  let body := EbnfValue.ruleView .body rawBody
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have publicEq : EbnfValue.optional publicAtom
      (publicToken.map (EbnfValue.terminalAtom
        (.hardKeyword .publicKw))) = rawPublic := by
    calc
      _ = EbnfValue.optional publicAtom rawPublicValue := by
        congr 1
        cases selected : rawPublicValue with
        | none => simp [publicToken, selected]
        | some raw => simp [publicToken, selected,
            EbnfValue.terminal_of_view]
      _ = rawPublic := EbnfValue.optional_of_view publicAtom rawPublic
  have payableEq : EbnfValue.optional payableAtom
      (payableToken.map (EbnfValue.terminalAtom
        (.hardKeyword .payableKw))) = rawPayable := by
    calc
      _ = EbnfValue.optional payableAtom rawPayableValue := by
        congr 1
        cases selected : rawPayableValue with
        | none => simp [payableToken, selected]
        | some raw => simp [payableToken, selected,
            EbnfValue.terminal_of_view]
      _ = rawPayable := EbnfValue.optional_of_view payableAtom rawPayable
  have parameterMapEq : parameters.map
      (EbnfValue.ruleAtom .parameter) = rawParameterValues :=
    contractConstructorRuleAtoms_of_views rawParameterValues
  have parametersEq : EbnfValue.list0 parameterAtom
      (parameters.map (EbnfValue.ruleAtom .parameter)) = rawParameters := by
    rw [parameterMapEq]
    exact EbnfValue.list0_of_view parameterAtom rawParameters
  let publicProjects : ∀ terminal, publicToken = some terminal →
      RuleReduction.MarkerProjects file tokens terminal
        .publicModifier := fun terminal _ => .publicModifier terminal
  let payableProjects : ∀ terminal, payableToken = some terminal →
      RuleReduction.MarkerProjects file tokens terminal
        .payableModifier := fun terminal _ => .payableModifier terminal
  let rebuilt : EbnfValue file tokens (.sequence children) :=
    EbnfValue.sequence children (EbnfValue.sequenceValuesBuild children
      (EbnfValue.optional publicAtom
          (publicToken.map (EbnfValue.terminalAtom
            (.hardKeyword .publicKw))),
        EbnfValue.optional payableAtom
          (payableToken.map (EbnfValue.terminalAtom
            (.hardKeyword .payableKw))),
        EbnfValue.terminalAtom (.hardKeyword .constructorKw) constructorKw,
        EbnfValue.terminalAtom (.symbol .leftParen) openParen,
        EbnfValue.list0 parameterAtom
          (parameters.map (EbnfValue.ruleAtom .parameter)),
        EbnfValue.terminalAtom (.symbol .rightParen) closeParen,
        EbnfValue.ruleAtom .body body, ()))
  have rebuiltEq : rebuilt = input := by
    dsimp only [rebuilt]
    rw [publicEq, payableEq,
      EbnfValue.terminal_of_view (.hardKeyword .constructorKw)
        rawConstructor,
      EbnfValue.terminal_of_view (.symbol .leftParen) rawOpen,
      parametersEq,
      EbnfValue.terminal_of_view (.symbol .rightParen) rawClose,
      EbnfValue.rule_of_view .body rawBody]
    exact inputEq
  have transportSelf
      (value : EbnfValue file tokens (.sequence children))
      (shape : (.sequence children) =
        m2cV1.rhs .contractConstructorDecl) :
      EbnfValue.transport shape value = value := by
    rw [show shape = (by rfl) from Subsingleton.elim _ _]
    rfl
  have reduces := RuleReduction.contractConstructorDecl origin finish
    publicToken payableToken constructorKw openParen parameters closeParen
    body publicProjects payableProjects
    (.contractConstructorName constructorKw) witness
  have outputEq := contractConstructorDecl_marker_fields_eq publicToken
    payableToken constructorKw parameters body publicProjects
    payableProjects witness
  have normalizedReduces := outputEq ▸ reduces
  rw [transportSelf] at normalizedReduces
  have resultEq : executeContractConstructorDeclRoot file tokens
      origin finish ready.1 ready.2.1 input = sourceLoc witness {
        «public» := publicToken.map fun terminal =>
          RuleReduction.terminalLoc terminal .publicModifier
        payable := payableToken.map fun terminal =>
          RuleReduction.terminalLoc terminal .payableModifier
        marker := RuleReduction.terminalLoc constructorKw
          .contractConstructorName
        parameters := parameters
        body := body
      } := by
    have sequenceEq' := sequenceEq
    simp only [children, publicAtom, payableAtom, parameterAtom]
      at sequenceEq'
    simp [executeContractConstructorDeclRoot, sequenceEq', publicToken,
      payableToken, constructorKw, parameters, body, witness]
    rfl
  have constructorInputEq := rebuiltEq
  simp only [rebuilt, children, publicAtom, payableAtom, parameterAtom,
    EbnfValue.sequenceValuesBuild] at constructorInputEq
  have inputReduces : RuleReduction file tokens
      .contractConstructorDecl origin finish input (sourceLoc witness {
        «public» := publicToken.map fun terminal =>
          RuleReduction.terminalLoc terminal .publicModifier
        payable := payableToken.map fun terminal =>
          RuleReduction.terminalLoc terminal .payableModifier
        marker := RuleReduction.terminalLoc constructorKw
          .contractConstructorName
        parameters := parameters
        body := body
      }) := constructorInputEq ▸ normalizedReduces
  exact resultEq.symm ▸ inputReduces


private def pragmaTargetData
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens (.optional (.list1
      (.atom (.terminal (.category .identifier)))))) :
    Option (NonemptyList (RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)) :=
  (pragmaTargetTerminals input).map fun terminals => terminals.map fun terminal => {
    matched := terminal
    spelling := terminal.identifierProjection.1
    parsed := terminal.identifierProjection.2
  }

private theorem pragmaTargetData_rebuild
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens (.optional (.list1
      (.atom (.terminal (.category .identifier)))))) :
    EbnfValue.optional (.list1
      (.atom (.terminal (.category .identifier))))
      ((pragmaTargetData input).map fun values =>
        EbnfValue.list1 (.atom (.terminal (.category .identifier)))
          (values.map fun target => EbnfValue.terminalAtom
            (.category .identifier) target.matched)) = input := by
  have rebuilt := pragmaTargetTerminals_rebuild input
  cases selected : pragmaTargetTerminals input with
  | none =>
      simpa [pragmaTargetData, selected] using rebuilt
  | some terminals =>
      cases terminals
      simpa [pragmaTargetData, selected, NonemptyList.map,
        Function.comp_def] using rebuilt

private theorem pragmaTargetData_projects
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens (.optional (.list1
      (.atom (.terminal (.category .identifier)))))) :
    ∀ values, pragmaTargetData input = some values →
      IdentifierProjects values.head.matched
        values.head.spelling values.head.parsed ∧
      ∀ target, target ∈ values.tail →
        IdentifierProjects target.matched target.spelling target.parsed := by
  intro values valuesEq
  unfold pragmaTargetData at valuesEq
  cases selected : pragmaTargetTerminals input with
  | none => simp [selected] at valuesEq
  | some terminals =>
      simp only [selected, Option.map, Option.some.injEq] at valuesEq
      subst values
      constructor
      · exact terminals.head.identifierProjection_projects
      · intro target member
        simp only [NonemptyList.map, List.mem_map] at member
        rcases member with ⟨terminal, _terminalMember, rfl⟩
        exact terminal.identifierProjection_projects

private theorem executePragmaTargets_eq_targetData
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens (.optional (.list1
      (.atom (.terminal (.category .identifier)))))) :
    executePragmaTargets input =
      (pragmaTargetData input).elim [] fun values =>
        RuleReduction.firstRest (values.map fun target =>
          RuleReduction.terminalLoc target.matched target.parsed) := by
  unfold executePragmaTargets pragmaTargetData
  cases selected : pragmaTargetTerminals input with
  | none => rfl
  | some terminals =>
      cases terminals
      simp [RuleReduction.firstRest, NonemptyList.map,
        RuleReduction.terminalLoc]

/-- The pragma executor realizes all four exact fixed-name reductions. -/
theorem executePragmaDeclRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .pragmaDecl origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .pragmaDecl)) :
    RuleReduction file tokens .pragmaDecl origin finish input
      (executePragmaDeclRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let pragmaAtom : EbnfExpr :=
    .atom (.terminal (.hardKeyword .pragmaKw))
  let identifierAtom : EbnfExpr :=
    .atom (.terminal (.category .identifier))
  let targetsAtom : EbnfExpr := .optional (.list1 identifierAtom)
  let semicolonAtom : EbnfExpr :=
    .atom (.terminal (.symbol .semicolon))
  let branches : List EbnfExpr := [
    .sequence [pragmaAtom,
      .atom (.terminal (.pragmaName .noCoverageCondition)),
      targetsAtom, semicolonAtom],
    .sequence [pragmaAtom,
      .atom (.terminal (.pragmaName .noPattersonCondition)),
      targetsAtom, semicolonAtom],
    .sequence [pragmaAtom,
      .atom (.terminal (.pragmaName .noBoundedVariableCondition)),
      targetsAtom, semicolonAtom],
    .sequence [pragmaAtom,
      .atom (.terminal (.pragmaName .noGenericInstanceFor)),
      targetsAtom, semicolonAtom]]
  change EbnfValue file tokens (.choice branches) at input
  generalize viewEq : EbnfValue.choiceView branches input = viewed
  rcases viewed with ⟨branch, raw⟩
  have inputEq : EbnfValue.choice branches
      ⟨branch, raw⟩ = input := by
    calc
      _ = EbnfValue.choice branches
          (EbnfValue.choiceView branches input) := by rw [viewEq]
      _ = input := EbnfValue.choice_of_view branches input
  have branchCases : branch = 0 ∨ branch = 1 ∨
      branch = 2 ∨ branch = 3 := by
    have bound : branch.val < 4 := branch.isLt
    have valueCases : branch.val = 0 ∨ branch.val = 1 ∨
        branch.val = 2 ∨ branch.val = 3 := by omega
    rcases valueCases with valueEq | valueEq | valueEq | valueEq
    · exact Or.inl (Fin.ext valueEq)
    · exact Or.inr (Or.inl (Fin.ext valueEq))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext valueEq)))
    · exact Or.inr (Or.inr (Or.inr (Fin.ext valueEq)))
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have transportSelf
      (value : EbnfValue file tokens (.choice branches))
      (shape : (.choice branches) = m2cV1.rhs .pragmaDecl) :
      EbnfValue.transport shape value = value := by
    rw [show shape = (by rfl) from Subsingleton.elim _ _]
    rfl
  rcases branchCases with rfl | rfl | rfl | rfl
  · let viewed := EbnfValue.sequence4View pragmaAtom
      (.atom (.terminal (.pragmaName .noCoverageCondition)))
      targetsAtom semicolonAtom raw
    let pragmaKw := EbnfValue.terminalView
      (.hardKeyword .pragmaKw) viewed.1
    let kindToken := EbnfValue.terminalView
      (.pragmaName .noCoverageCondition) viewed.2.1
    let targets := pragmaTargetData viewed.2.2.1
    let semicolon := EbnfValue.terminalView
      (.symbol .semicolon) viewed.2.2.2
    have rawEq := EbnfValue.sequence4_of_view pragmaAtom
      (.atom (.terminal (.pragmaName .noCoverageCondition)))
      targetsAtom semicolonAtom raw
    have pragmaEq := EbnfValue.terminal_of_view
      (.hardKeyword .pragmaKw) viewed.1
    have kindEq := EbnfValue.terminal_of_view
      (.pragmaName .noCoverageCondition) viewed.2.1
    have targetsEq := pragmaTargetData_rebuild viewed.2.2.1
    have semicolonEq := EbnfValue.terminal_of_view
      (.symbol .semicolon) viewed.2.2.2
    have resultEq : executePragmaDeclRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness {
      kind := RuleReduction.terminalLoc kindToken .noCoverageCondition
      targets := executePragmaTargets viewed.2.2.1
    } := by
      rw [executePragmaDeclRoot, viewEq]
      rfl
    have reduces := RuleReduction.pragmaDeclNoCoverageCondition
      origin finish pragmaKw kindToken
      targets semicolon (pragmaTargetData_projects viewed.2.2.1) witness
    simp only [targets, NonemptyList.map] at reduces targetsEq
    rw [transportSelf, pragmaEq, kindEq, targetsEq, semicolonEq,
      rawEq, inputEq] at reduces
    rw [executePragmaTargets_eq_targetData] at resultEq
    exact resultEq.symm ▸ reduces
  · let viewed := EbnfValue.sequence4View pragmaAtom
      (.atom (.terminal (.pragmaName .noPattersonCondition)))
      targetsAtom semicolonAtom raw
    let pragmaKw := EbnfValue.terminalView
      (.hardKeyword .pragmaKw) viewed.1
    let kindToken := EbnfValue.terminalView
      (.pragmaName .noPattersonCondition) viewed.2.1
    let targets := pragmaTargetData viewed.2.2.1
    let semicolon := EbnfValue.terminalView
      (.symbol .semicolon) viewed.2.2.2
    have rawEq := EbnfValue.sequence4_of_view pragmaAtom
      (.atom (.terminal (.pragmaName .noPattersonCondition)))
      targetsAtom semicolonAtom raw
    have pragmaEq := EbnfValue.terminal_of_view
      (.hardKeyword .pragmaKw) viewed.1
    have kindEq := EbnfValue.terminal_of_view
      (.pragmaName .noPattersonCondition) viewed.2.1
    have targetsEq := pragmaTargetData_rebuild viewed.2.2.1
    have semicolonEq := EbnfValue.terminal_of_view
      (.symbol .semicolon) viewed.2.2.2
    have resultEq : executePragmaDeclRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness {
      kind := RuleReduction.terminalLoc kindToken .noPattersonCondition
      targets := executePragmaTargets viewed.2.2.1
    } := by
      rw [executePragmaDeclRoot, viewEq]
      rfl
    have reduces := RuleReduction.pragmaDeclNoPattersonCondition
      origin finish pragmaKw kindToken
      targets semicolon (pragmaTargetData_projects viewed.2.2.1) witness
    simp only [targets, NonemptyList.map] at reduces targetsEq
    rw [transportSelf, pragmaEq, kindEq, targetsEq, semicolonEq,
      rawEq, inputEq] at reduces
    rw [executePragmaTargets_eq_targetData] at resultEq
    exact resultEq.symm ▸ reduces
  · let viewed := EbnfValue.sequence4View pragmaAtom
      (.atom (.terminal (.pragmaName .noBoundedVariableCondition)))
      targetsAtom semicolonAtom raw
    let pragmaKw := EbnfValue.terminalView
      (.hardKeyword .pragmaKw) viewed.1
    let kindToken := EbnfValue.terminalView
      (.pragmaName .noBoundedVariableCondition) viewed.2.1
    let targets := pragmaTargetData viewed.2.2.1
    let semicolon := EbnfValue.terminalView
      (.symbol .semicolon) viewed.2.2.2
    have rawEq := EbnfValue.sequence4_of_view pragmaAtom
      (.atom (.terminal (.pragmaName .noBoundedVariableCondition)))
      targetsAtom semicolonAtom raw
    have pragmaEq := EbnfValue.terminal_of_view
      (.hardKeyword .pragmaKw) viewed.1
    have kindEq := EbnfValue.terminal_of_view
      (.pragmaName .noBoundedVariableCondition) viewed.2.1
    have targetsEq := pragmaTargetData_rebuild viewed.2.2.1
    have semicolonEq := EbnfValue.terminal_of_view
      (.symbol .semicolon) viewed.2.2.2
    have resultEq : executePragmaDeclRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness {
      kind := RuleReduction.terminalLoc kindToken
        .noBoundedVariableCondition
      targets := executePragmaTargets viewed.2.2.1
    } := by
      rw [executePragmaDeclRoot, viewEq]
      rfl
    have reduces := RuleReduction.pragmaDeclNoBoundedVariableCondition
      origin finish pragmaKw
      kindToken targets semicolon
        (pragmaTargetData_projects viewed.2.2.1) witness
    simp only [targets, NonemptyList.map] at reduces targetsEq
    rw [transportSelf, pragmaEq, kindEq, targetsEq, semicolonEq,
      rawEq, inputEq] at reduces
    rw [executePragmaTargets_eq_targetData] at resultEq
    exact resultEq.symm ▸ reduces
  · let viewed := EbnfValue.sequence4View pragmaAtom
      (.atom (.terminal (.pragmaName .noGenericInstanceFor)))
      targetsAtom semicolonAtom raw
    let pragmaKw := EbnfValue.terminalView
      (.hardKeyword .pragmaKw) viewed.1
    let kindToken := EbnfValue.terminalView
      (.pragmaName .noGenericInstanceFor) viewed.2.1
    let targets := pragmaTargetData viewed.2.2.1
    let semicolon := EbnfValue.terminalView
      (.symbol .semicolon) viewed.2.2.2
    have rawEq := EbnfValue.sequence4_of_view pragmaAtom
      (.atom (.terminal (.pragmaName .noGenericInstanceFor)))
      targetsAtom semicolonAtom raw
    have pragmaEq := EbnfValue.terminal_of_view
      (.hardKeyword .pragmaKw) viewed.1
    have kindEq := EbnfValue.terminal_of_view
      (.pragmaName .noGenericInstanceFor) viewed.2.1
    have targetsEq := pragmaTargetData_rebuild viewed.2.2.1
    have semicolonEq := EbnfValue.terminal_of_view
      (.symbol .semicolon) viewed.2.2.2
    have resultEq : executePragmaDeclRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness {
      kind := RuleReduction.terminalLoc kindToken .noGenericInstanceFor
      targets := executePragmaTargets viewed.2.2.1
    } := by
      rw [executePragmaDeclRoot, viewEq]
      rfl
    have reduces := RuleReduction.pragmaDeclNoGenericInstanceFor
      origin finish pragmaKw kindToken
      targets semicolon (pragmaTargetData_projects viewed.2.2.1) witness
    simp only [targets, NonemptyList.map] at reduces targetsEq
    rw [transportSelf, pragmaEq, kindEq, targetsEq, semicolonEq,
      rawEq, inputEq] at reduces
    rw [executePragmaTargets_eq_targetData] at resultEq
    exact resultEq.symm ▸ reduces

/-- The generic-prefix executor realizes its exact source-rule reduction. -/
theorem executeGenericPrefixRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .genericPrefix origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .genericPrefix)) :
    RuleReduction file tokens .genericPrefix origin finish input
      (executeGenericPrefixRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let contextChildren : List EbnfExpr := [
    .atom (.nonterminal .predicateList),
    .atom (.terminal (.symbol .fatArrow))]
  let children : List EbnfExpr := [
    .atom (.nonterminal .forallClause),
    .optional (.sequence contextChildren)]
  change EbnfValue file tokens (.sequence children) at input
  generalize rootEq : EbnfValue.sequenceFlatView children input = root
  rcases root with ⟨rawForall, rawOptional, ⟨⟩⟩
  let forallClause := EbnfValue.ruleView .forallClause rawForall
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  generalize optionalEq : EbnfValue.optionalView
    (.sequence contextChildren) rawOptional = viewed
  cases viewed with
  | none =>
      have inputEq : EbnfValue.sequence children
          (EbnfValues.cons _ _
            (EbnfValue.ruleAtom .forallClause forallClause)
            (EbnfValues.cons _ _
              (EbnfValue.optional (.sequence contextChildren) none)
              EbnfValues.nil)) = input := by
        rw [EbnfValue.rule_of_view .forallClause rawForall]
        have rebuild := EbnfValue.optional_of_view
          (.sequence contextChildren) rawOptional
        rw [optionalEq] at rebuild
        rw [rebuild]
        have rootRebuild := EbnfValue.sequence_of_flat_view children input
        rw [rootEq] at rootRebuild
        exact rootRebuild
      have resultEq : executeGenericPrefixRoot file tokens origin finish
          ready.1 ready.2.1 input = sourceLoc witness {
            forallClause := forallClause
            context := none
          } := by
        simp [executeGenericPrefixRoot, children, contextChildren,
          rootEq, optionalEq, forallClause, witness]
        rfl
      rw [resultEq, ← inputEq]
      exact .genericPrefixBare origin finish forallClause witness
  | some rawContext =>
      generalize contextEq : EbnfValue.sequenceFlatView
        contextChildren rawContext = context
      rcases context with ⟨rawPredicates, rawArrow, ⟨⟩⟩
      let predicates := EbnfValue.ruleView .predicateList rawPredicates
      let fatArrow := EbnfValue.terminalView (.symbol .fatArrow) rawArrow
      have contextInputEq : EbnfValue.sequence contextChildren
          (EbnfValues.cons _ _
            (EbnfValue.ruleAtom .predicateList predicates)
            (EbnfValues.cons _ _
              (EbnfValue.terminalAtom (.symbol .fatArrow) fatArrow)
              EbnfValues.nil)) = rawContext := by
        rw [EbnfValue.rule_of_view .predicateList rawPredicates]
        rw [EbnfValue.terminal_of_view (.symbol .fatArrow) rawArrow]
        have contextRebuild := EbnfValue.sequence_of_flat_view
          contextChildren rawContext
        rw [contextEq] at contextRebuild
        exact contextRebuild
      have inputEq : EbnfValue.sequence children
          (EbnfValues.cons _ _
            (EbnfValue.ruleAtom .forallClause forallClause)
            (EbnfValues.cons _ _
              (EbnfValue.optional (.sequence contextChildren)
                (some (EbnfValue.sequence contextChildren
                  (EbnfValues.cons _ _
                    (EbnfValue.ruleAtom .predicateList predicates)
                    (EbnfValues.cons _ _
                      (EbnfValue.terminalAtom (.symbol .fatArrow) fatArrow)
                      EbnfValues.nil)))))
              EbnfValues.nil)) = input := by
        rw [contextInputEq]
        rw [EbnfValue.rule_of_view .forallClause rawForall]
        have optionalRebuild := EbnfValue.optional_of_view
          (.sequence contextChildren) rawOptional
        rw [optionalEq] at optionalRebuild
        rw [optionalRebuild]
        have rootRebuild := EbnfValue.sequence_of_flat_view children input
        rw [rootEq] at rootRebuild
        exact rootRebuild
      have resultEq : executeGenericPrefixRoot file tokens origin finish
          ready.1 ready.2.1 input = sourceLoc witness {
            forallClause := forallClause
            context := some predicates
          } := by
        simp [executeGenericPrefixRoot, children, contextChildren,
          rootEq, optionalEq, contextEq, forallClause, predicates,
          witness]
        rfl
      rw [resultEq, ← inputEq]
      exact .genericPrefixContext origin finish forallClause
        predicates fatArrow witness

/-- The forall-clause executor realizes its exact root reduction. -/
theorem executeForallClauseRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .forallClause origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .forallClause)) :
    RuleReduction file tokens .forallClause origin finish input
      (executeForallClauseRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let forallAtom : EbnfExpr :=
    .atom (.terminal (.hardKeyword .forallKw))
  let binderAtom : EbnfExpr := .atom (.nonterminal .forallBinder)
  let tail := EbnfValue.rulePairTailExpr .optionalComma .forallBinder
  let dotAtom : EbnfExpr := .atom (.terminal (.symbol .dot))
  change EbnfValue file tokens
    (.sequence [forallAtom, binderAtom, .star tail, dotAtom]) at input
  let viewed := EbnfValue.sequence4View
    forallAtom binderAtom (.star tail) dotAtom input
  let forallKw := EbnfValue.terminalView
    (.hardKeyword .forallKw) viewed.1
  let first := EbnfValue.ruleView .forallBinder viewed.2.1
  let rawRest := EbnfValue.starView tail viewed.2.2.1
  let rest := rawRest.map
    (EbnfValue.rulePairTailView .optionalComma .forallBinder)
  let dot := EbnfValue.terminalView (.symbol .dot) viewed.2.2.2
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have inputEq := EbnfValue.sequence4_of_view
    forallAtom binderAtom (.star tail) dotAtom input
  have forallEq := EbnfValue.terminal_of_view
    (.hardKeyword .forallKw) viewed.1
  have firstEq := EbnfValue.rule_of_view .forallBinder viewed.2.1
  have restMapEq : rest.map (EbnfValue.rulePairTailValue
      .optionalComma .forallBinder) = rawRest := by
    simp [rest, List.map_map, Function.comp_def,
      EbnfValue.rulePairTailValue_of_view]
  have restEq : EbnfValue.star tail
      (rest.map (EbnfValue.rulePairTailValue
        .optionalComma .forallBinder)) = viewed.2.2.1 := by
    rw [restMapEq]
    exact EbnfValue.star_of_view tail viewed.2.2.1
  have dotEq := EbnfValue.terminal_of_view (.symbol .dot) viewed.2.2.2
  have resultEq : executeForallClauseRoot file tokens origin finish
      ready.1 ready.2.1 input = sourceLoc witness {
        binders := {
          head := first
          tail := rest.map Prod.snd
        }
      } := by
    rfl
  rw [resultEq, ← inputEq, ← forallEq, ← firstEq, ← restEq, ← dotEq]
  exact .forallClause origin finish forallKw first rest dot witness

private theorem forallBinderRuleNonemptyAtoms_of_views
    {file : WorkspaceFile} {tokens : List Token}
    (inputs : NonemptyList
      (EbnfValue file tokens (.atom (.nonterminal .type)))) :
    (inputs.map (EbnfValue.ruleView .type)).map
        (EbnfValue.ruleAtom .type) = inputs := by
  cases inputs with
  | mk head tail =>
      simp only [NonemptyList.map, NonemptyList.mk.injEq]
      constructor
      · exact EbnfValue.rule_of_view .type head
      · induction tail with
        | nil => rfl
        | cons next rest induction =>
            simp [EbnfValue.rule_of_view, induction]

/-- The universal-binder executor realizes its exact root reduction. -/
theorem executeForallBinderRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .forallBinder origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .forallBinder)) :
    RuleReduction file tokens .forallBinder origin finish input
      (executeForallBinderRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let identifierAtom : EbnfExpr := .atom (.terminal (.category .identifier))
  let typeAtom : EbnfExpr := .atom (.nonterminal .type)
  let openAtom : EbnfExpr :=
    .atom (.terminal (.symbol .leftParen))
  let typesAtom : EbnfExpr := .list1 typeAtom
  let closeAtom : EbnfExpr :=
    .atom (.terminal (.symbol .rightParen))
  let argumentChildren : List EbnfExpr :=
    [openAtom, typesAtom, closeAtom]
  let argumentChild : EbnfExpr := .sequence argumentChildren
  let colonAtom : EbnfExpr :=
    .atom (.terminal (.symbol .colon))
  let classAtom : EbnfExpr := .atom (.nonterminal .qualifiedName)
  let boundedChildren : List EbnfExpr :=
    [identifierAtom, colonAtom, classAtom, .optional argumentChild]
  change EbnfValue file tokens
    (.choice [identifierAtom, .sequence boundedChildren]) at input
  generalize choiceEq : EbnfValue.choice2View identifierAtom
    (.sequence boundedChildren) input = selected
  have inputEq := EbnfValue.choice2_of_view
    identifierAtom (.sequence boundedChildren) input
  rw [choiceEq] at inputEq
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  rcases selected with rawName | rawBounded
  · let name := EbnfValue.terminalView
      (.category .identifier) rawName
    let nameData : RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier := {
      matched := name
      spelling := name.identifierProjection.1
      parsed := name.identifierProjection.2
    }
    have resultEq : executeForallBinderRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness (.bare
          (executableTerminalLoc name name.identifierProjection.2)) := by
      rw [executeForallBinderRoot, choiceEq]
      rfl
    rw [resultEq, ← inputEq,
      ← EbnfValue.terminal_of_view (.category .identifier) rawName]
    exact .forallBinderBare origin finish nameData
      name.identifierProjection_projects witness
  · generalize boundedEq : EbnfValue.sequenceFlatView
      boundedChildren rawBounded = bounded
    rcases bounded with ⟨rawName, rawColon, rawClass, rawOptional, ⟨⟩⟩
    let name := EbnfValue.terminalView
      (.category .identifier) rawName
    let nameData : RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier := {
      matched := name
      spelling := name.identifierProjection.1
      parsed := name.identifierProjection.2
    }
    let colon := EbnfValue.terminalView (.symbol .colon) rawColon
    let className := EbnfValue.ruleView .qualifiedName rawClass
    generalize optionalEq : EbnfValue.optionalView
      argumentChild rawOptional = arguments
    cases arguments with
    | none =>
        have resultEq : executeForallBinderRoot file tokens origin finish
            ready.1 ready.2.1 input = sourceLoc witness (.bounded
              (executableTerminalLoc name name.identifierProjection.2)
              className none) := by
          simp [executeForallBinderRoot, choiceEq, boundedEq, optionalEq,
            identifierAtom, typeAtom, openAtom, typesAtom, closeAtom,
            argumentChildren, argumentChild, colonAtom, classAtom,
            boundedChildren, name, className, witness]
          rfl
        have rawOptionalEq : EbnfValue.optional argumentChild none =
            rawOptional := by
          calc
            _ = EbnfValue.optional argumentChild
                (EbnfValue.optionalView argumentChild rawOptional) := by
                  rw [optionalEq]
            _ = rawOptional := EbnfValue.optional_of_view
              argumentChild rawOptional
        rw [resultEq, ← inputEq,
          ← EbnfValue.sequence_of_flat_view boundedChildren rawBounded,
          boundedEq,
          ← EbnfValue.terminal_of_view (.category .identifier) rawName,
          ← EbnfValue.terminal_of_view (.symbol .colon) rawColon,
          ← EbnfValue.rule_of_view .qualifiedName rawClass,
          ← rawOptionalEq]
        exact .forallBinderBoundedWithoutArguments origin finish
          nameData colon className name.identifierProjection_projects witness
    | some rawArguments =>
        generalize argumentsEq : EbnfValue.sequenceFlatView
          argumentChildren rawArguments = argumentValues
        rcases argumentValues with ⟨rawOpen, rawTypes, rawClose, ⟨⟩⟩
        let openParen := EbnfValue.terminalView
          (.symbol .leftParen) rawOpen
        let rawTypeValues := EbnfValue.list1View typeAtom rawTypes
        let parameters := rawTypeValues.map (EbnfValue.ruleView .type)
        let closeParen := EbnfValue.terminalView
          (.symbol .rightParen) rawClose
        have parametersMapEq : parameters.map
            (EbnfValue.ruleAtom .type) = rawTypeValues :=
          forallBinderRuleNonemptyAtoms_of_views rawTypeValues
        have parametersEq : EbnfValue.list1 typeAtom
            (parameters.map (EbnfValue.ruleAtom .type)) = rawTypes := by
          rw [parametersMapEq]
          exact EbnfValue.list1_of_view typeAtom rawTypes
        have resultEq : executeForallBinderRoot file tokens origin finish
            ready.1 ready.2.1 input = sourceLoc witness (.bounded
              (executableTerminalLoc name name.identifierProjection.2)
              className (some parameters)) := by
          simp [executeForallBinderRoot, choiceEq, boundedEq, optionalEq,
            argumentsEq, identifierAtom, typeAtom, openAtom, typesAtom,
            closeAtom, argumentChildren, argumentChild, colonAtom, classAtom,
            boundedChildren, name, className, rawTypeValues, parameters,
            witness]
          rfl
        have rawOptionalEq : EbnfValue.optional argumentChild
            (some rawArguments) = rawOptional := by
          calc
            _ = EbnfValue.optional argumentChild
                (EbnfValue.optionalView argumentChild rawOptional) := by
                  rw [optionalEq]
            _ = rawOptional := EbnfValue.optional_of_view
              argumentChild rawOptional
        rw [resultEq, ← inputEq,
          ← EbnfValue.sequence_of_flat_view boundedChildren rawBounded,
          boundedEq,
          ← EbnfValue.terminal_of_view (.category .identifier) rawName,
          ← EbnfValue.terminal_of_view (.symbol .colon) rawColon,
          ← EbnfValue.rule_of_view .qualifiedName rawClass,
          ← rawOptionalEq,
          ← EbnfValue.sequence_of_flat_view argumentChildren rawArguments,
          argumentsEq,
          ← EbnfValue.terminal_of_view (.symbol .leftParen) rawOpen,
          ← parametersEq,
          ← EbnfValue.terminal_of_view (.symbol .rightParen) rawClose]
        exact .forallBinderBoundedWithArguments origin finish nameData colon
          className openParen parameters closeParen
          name.identifierProjection_projects witness

/-- The export-item executor realizes its exact root reduction. -/
theorem executeExportItemRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .exportItem origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .exportItem)) :
    RuleReduction file tokens .exportItem origin finish input
      (executeExportItemRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let identifierAtom : EbnfExpr :=
    .atom (.terminal (.category .identifier))
  let selectionAtom : EbnfExpr :=
    .atom (.nonterminal .constructorSelection)
  change EbnfValue file tokens
    (.sequence [identifierAtom, .optional selectionAtom]) at input
  let viewed := EbnfValue.sequence2View
    identifierAtom (.optional selectionAtom) input
  let name := EbnfValue.terminalView
    (.category .identifier) viewed.1
  let nameData : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier := {
    matched := name
    spelling := name.identifierProjection.1
    parsed := name.identifierProjection.2
  }
  let selection := (EbnfValue.optionalView selectionAtom viewed.2).map
    (EbnfValue.ruleView .constructorSelection)
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have inputEq := EbnfValue.sequence2_of_view
    identifierAtom (.optional selectionAtom) input
  have nameEq := EbnfValue.terminal_of_view
    (.category .identifier) viewed.1
  have selectionEq : EbnfValue.optional selectionAtom
      (selection.map (EbnfValue.ruleAtom .constructorSelection)) =
      viewed.2 := by
    let rawSelection := EbnfValue.optionalView selectionAtom viewed.2
    calc
      _ = EbnfValue.optional selectionAtom rawSelection := by
        congr 1
        cases selected : rawSelection with
        | none => simp [selection, rawSelection, selected]
        | some raw =>
            simp only [selection, rawSelection, selected, Option.map]
            exact congrArg some
              (EbnfValue.rule_of_view .constructorSelection raw)
      _ = viewed.2 := EbnfValue.optional_of_view selectionAtom viewed.2
  have resultEq : executeExportItemRoot file tokens origin finish
      ready.1 ready.2.1 input = sourceLoc witness {
        name := RuleReduction.terminalLoc name name.identifierProjection.2
        constructors := selection
      } := by
    rfl
  rw [resultEq, ← inputEq, ← nameEq, ← selectionEq]
  exact .exportItem origin finish nameData selection
    name.identifierProjection_projects witness

private theorem constructorSelectionIdentifierAtoms_of_views
    {file : WorkspaceFile} {tokens : List Token}
    (values : NonemptyList (EbnfValue file tokens
      (.atom (.terminal (.category .identifier))))) :
    values.map (fun raw => EbnfValue.terminalAtom
      (.category .identifier) (EbnfValue.terminalView
        (.category .identifier) raw)) = values := by
  cases values with
  | mk head tail =>
      simp [NonemptyList.map, EbnfValue.terminal_of_view]

/-- The constructor-selection executor realizes its root reduction. -/
theorem executeConstructorSelectionRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens
      .constructorSelection origin finish)
    (input : EbnfValue file tokens
      (m2cV1.rhs .constructorSelection)) :
    RuleReduction file tokens .constructorSelection origin finish input
      (executeConstructorSelectionRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let identifierAtom : EbnfExpr :=
    .atom (.terminal (.category .identifier))
  let allChildren : List EbnfExpr := [
    .atom (.terminal (.symbol .leftParen)),
    .atom (.terminal (.symbol .star)),
    .atom (.terminal (.symbol .rightParen))]
  let namedChildren : List EbnfExpr := [
    .atom (.terminal (.symbol .leftParen)), .list1 identifierAtom,
    .atom (.terminal (.symbol .rightParen))]
  let branches : List EbnfExpr :=
    [.sequence allChildren, .sequence namedChildren]
  change EbnfValue file tokens (.choice branches) at input
  generalize viewEq : EbnfValue.choiceView branches input = viewed
  rcases viewed with ⟨branch, raw⟩
  have inputEq : EbnfValue.choice branches ⟨branch, raw⟩ = input := by
    calc
      _ = EbnfValue.choice branches
          (EbnfValue.choiceView branches input) := by rw [viewEq]
      _ = input := EbnfValue.choice_of_view branches input
  have branchCases : branch = 0 ∨ branch = 1 := by
    have branchesLength : branches.length = 2 := by rfl
    have bound : branch.val < 2 := by
      calc
        branch.val < branches.length := branch.isLt
        _ = 2 := branchesLength
    have values : branch.val = 0 ∨ branch.val = 1 := by omega
    rcases values with valueEq | valueEq
    · exact Or.inl (Fin.ext valueEq)
    · exact Or.inr (Fin.ext valueEq)
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  rcases branchCases with rfl | rfl
  · let values := EbnfValue.sequenceFlatView allChildren raw
    let rawOpen := values.1
    let rawStar := values.2.1
    let rawClose := values.2.2.1
    have rawEq := EbnfValue.sequence_of_flat_view allChildren raw
    let openParen := EbnfValue.terminalView
      (.symbol .leftParen) rawOpen
    let star := EbnfValue.terminalView (.symbol .star) rawStar
    let closeParen := EbnfValue.terminalView
      (.symbol .rightParen) rawClose
    have rawEq' : EbnfValue.sequence allChildren
        (EbnfValue.sequenceValuesBuild allChildren
          ⟨rawOpen, rawStar, rawClose, ⟨⟩⟩) = raw := rawEq
    have resultEq : executeConstructorSelectionRoot file tokens
        origin finish ready.1 ready.2.1 input = sourceLoc witness
          (.all (executableTerminalLoc star .wildcard)) := by
      rw [executeConstructorSelectionRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq',
      ← EbnfValue.terminal_of_view (.symbol .leftParen) rawOpen,
      ← EbnfValue.terminal_of_view (.symbol .star) rawStar,
      ← EbnfValue.terminal_of_view (.symbol .rightParen) rawClose]
    exact .constructorSelectionAll origin finish openParen star closeParen
      (.wildcardStar star) witness
  · let values := EbnfValue.sequenceFlatView namedChildren raw
    let rawOpen := values.1
    let rawNames := values.2.1
    let rawClose := values.2.2.1
    have rawEq := EbnfValue.sequence_of_flat_view namedChildren raw
    let openParen := EbnfValue.terminalView
      (.symbol .leftParen) rawOpen
    let closeParen := EbnfValue.terminalView
      (.symbol .rightParen) rawClose
    have rawEq' : EbnfValue.sequence namedChildren
        (EbnfValue.sequenceValuesBuild namedChildren
          ⟨rawOpen, rawNames, rawClose, ⟨⟩⟩) = raw := rawEq
    generalize rawNameValuesEq : EbnfValue.list1View
      identifierAtom rawNames = rawNameValues
    let names : NonemptyList (RuleReduction.SpelledTerminalData
        file tokens (.category .identifier) Identifier) :=
      rawNameValues.map fun rawName =>
        let name := EbnfValue.terminalView
          (.category .identifier) rawName
        ({
          matched := name
          spelling := name.identifierProjection.1
          parsed := name.identifierProjection.2
        } : RuleReduction.SpelledTerminalData file tokens
          (.category .identifier) Identifier)
    let executableNames := (EbnfValue.list1View identifierAtom rawNames).map
      fun rawName =>
        let name := EbnfValue.terminalView
          (.category .identifier) rawName
        ({ span := name.span, payload := name.identifierProjection.2 } :
          IdentifierOccurrence)
    have namesEq : EbnfValue.list1 identifierAtom
        (names.map fun value => EbnfValue.terminalAtom
          (.category .identifier) value.matched) = rawNames := by
      have mappedEq : names.map (fun value => EbnfValue.terminalAtom
          (.category .identifier) value.matched) = rawNameValues := by
        cases rawNameValues
        simp [names, NonemptyList.map, List.map_map, Function.comp_def,
          EbnfValue.terminal_of_view]
      rw [mappedEq, ← rawNameValuesEq]
      exact EbnfValue.list1_of_view identifierAtom rawNames
    have resultEq : executeConstructorSelectionRoot file tokens
        origin finish ready.1 ready.2.1 input = sourceLoc witness
          (.named executableNames) := by
      rw [executeConstructorSelectionRoot, viewEq]
      rfl
    have executableNamesEq : executableNames = names.map fun name =>
        executableTerminalLoc name.matched name.parsed := by
      unfold executableNames
      rw [rawNameValuesEq]
      cases rawNameValues
      simp [names, NonemptyList.map, List.map_map,
        executableTerminalLoc]
    rw [resultEq, executableNamesEq, ← inputEq, ← rawEq',
      ← EbnfValue.terminal_of_view (.symbol .leftParen) rawOpen,
      ← namesEq,
      ← EbnfValue.terminal_of_view (.symbol .rightParen) rawClose]
    exact .constructorSelectionNamed origin finish openParen names closeParen
      (by
        simpa [names, NonemptyList.map] using
          (EbnfValue.terminalView (.category .identifier)
            rawNameValues.head).identifierProjection_projects)
      (by
        intro name nameMem
        simp only [names, NonemptyList.map] at nameMem
        rcases List.mem_map.mp nameMem with ⟨rawName, _rawMem, rfl⟩
        exact (EbnfValue.terminalView (.category .identifier)
          rawName).identifierProjection_projects)
      witness

private theorem importDeclRuleAtoms_of_views
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId)
    (values : List (EbnfValue file tokens
      (.atom (.nonterminal rule)))) :
    values.map (fun raw => EbnfValue.ruleAtom rule
      (EbnfValue.ruleView rule raw)) = values := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp [EbnfValue.rule_of_view]

private theorem importDeclOptionalRuleAtom_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId)
    (input : EbnfValue file tokens
      (.optional (.atom (.nonterminal rule)))) :
    EbnfValue.optional (.atom (.nonterminal rule))
      ((EbnfValue.optionalView (.atom (.nonterminal rule)) input).map
        (EbnfValue.ruleView rule) |>.map (EbnfValue.ruleAtom rule)) =
      input := by
  generalize viewEq : EbnfValue.optionalView
    (.atom (.nonterminal rule)) input = viewed
  cases viewed with
  | none =>
      simp only [Option.map]
      calc
        _ = EbnfValue.optional (.atom (.nonterminal rule))
            (EbnfValue.optionalView
              (.atom (.nonterminal rule)) input) := by rw [viewEq]
        _ = input := EbnfValue.optional_of_view
          (.atom (.nonterminal rule)) input
  | some raw =>
      simp only [Option.map]
      calc
        _ = EbnfValue.optional (.atom (.nonterminal rule))
            (some raw) := by rw [EbnfValue.rule_of_view]
        _ = EbnfValue.optional (.atom (.nonterminal rule))
            (EbnfValue.optionalView
              (.atom (.nonterminal rule)) input) := by rw [viewEq]
        _ = input := EbnfValue.optional_of_view
          (.atom (.nonterminal rule)) input

/-- The import-declaration executor realizes every exact root reduction. -/
theorem executeImportDeclRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .importDecl origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .importDecl)) :
    RuleReduction file tokens .importDecl origin finish input
      (executeImportDeclRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let moduleChildren : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .importKw)),
    .atom (.nonterminal .moduleRef),
    .atom (.terminal (.symbol .semicolon))]
  let aliasChildren : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .importKw)),
    .atom (.nonterminal .moduleRef),
    .atom (.terminal (.hardKeyword .asKw)),
    .atom (.terminal (.category .identifier)),
    .atom (.terminal (.symbol .semicolon))]
  let entryAtom : EbnfExpr := .atom (.nonterminal .importEntry)
  let hidingAtom : EbnfExpr := .atom (.nonterminal .hidingClause)
  let itemsChildren : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .importKw)),
    .atom (.nonterminal .moduleRef),
    .atom (.terminal (.symbol .dot)),
    .atom (.terminal (.symbol .leftBrace)), .list0 entryAtom,
    .atom (.terminal (.symbol .rightBrace)), .optional hidingAtom,
    .atom (.terminal (.symbol .semicolon))]
  let branches : List EbnfExpr := [.sequence moduleChildren,
    .sequence aliasChildren, .sequence itemsChildren]
  change EbnfValue file tokens (.choice branches) at input
  generalize viewEq : EbnfValue.choiceView branches input = viewed
  rcases viewed with ⟨branch, raw⟩
  have inputEq : EbnfValue.choice branches ⟨branch, raw⟩ = input := by
    calc
      _ = EbnfValue.choice branches
          (EbnfValue.choiceView branches input) := by rw [viewEq]
      _ = input := EbnfValue.choice_of_view branches input
  have branchCases : branch = 0 ∨ branch = 1 ∨ branch = 2 := by
    have branchesLength : branches.length = 3 := by rfl
    have bound : branch.val < 3 := by
      calc
        branch.val < branches.length := branch.isLt
        _ = 3 := branchesLength
    have valueCases : branch.val = 0 ∨ branch.val = 1 ∨
        branch.val = 2 := by omega
    rcases valueCases with valueEq | valueEq | valueEq
    · exact Or.inl (Fin.ext valueEq)
    · exact Or.inr (Or.inl (Fin.ext valueEq))
    · exact Or.inr (Or.inr (Fin.ext valueEq))
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  rcases branchCases with rfl | rfl | rfl
  · let viewed := EbnfValue.sequenceFlatView moduleChildren raw
    let rawImport := viewed.1
    let rawReference := viewed.2.1
    let rawSemicolon := viewed.2.2.1
    let importKw := EbnfValue.terminalView
      (.hardKeyword .importKw) rawImport
    let reference := EbnfValue.ruleView .moduleRef rawReference
    let semicolon := EbnfValue.terminalView
      (.symbol .semicolon) rawSemicolon
    have rawEq := EbnfValue.sequence_of_flat_view moduleChildren raw
    have rawEq' : EbnfValue.sequence moduleChildren
        (EbnfValue.sequenceValuesBuild moduleChildren
          ⟨rawImport, rawReference, rawSemicolon, ⟨⟩⟩) = raw := rawEq
    have resultEq : executeImportDeclRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness {
          moduleRef := reference
          mode := .module none
        } := by
      rw [executeImportDeclRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq',
      ← EbnfValue.terminal_of_view (.hardKeyword .importKw) rawImport,
      ← EbnfValue.rule_of_view .moduleRef rawReference,
      ← EbnfValue.terminal_of_view (.symbol .semicolon) rawSemicolon]
    exact .importDeclModule origin finish importKw reference
      semicolon witness
  · let viewed := EbnfValue.sequenceFlatView aliasChildren raw
    let rawImport := viewed.1
    let rawReference := viewed.2.1
    let rawAs := viewed.2.2.1
    let rawName := viewed.2.2.2.1
    let rawSemicolon := viewed.2.2.2.2.1
    let importKw := EbnfValue.terminalView
      (.hardKeyword .importKw) rawImport
    let reference := EbnfValue.ruleView .moduleRef rawReference
    let asKw := EbnfValue.terminalView (.hardKeyword .asKw) rawAs
    let name := EbnfValue.terminalView (.category .identifier) rawName
    let nameData : RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier := {
      matched := name
      spelling := name.identifierProjection.1
      parsed := name.identifierProjection.2
    }
    let semicolon := EbnfValue.terminalView
      (.symbol .semicolon) rawSemicolon
    have rawEq := EbnfValue.sequence_of_flat_view aliasChildren raw
    have rawEq' : EbnfValue.sequence aliasChildren
        (EbnfValue.sequenceValuesBuild aliasChildren
          ⟨rawImport, rawReference, rawAs, rawName,
            rawSemicolon, ⟨⟩⟩) = raw := rawEq
    have resultEq : executeImportDeclRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness {
          moduleRef := reference
          mode := .module (some
            (RuleReduction.terminalLoc name name.identifierProjection.2))
        } := by
      rw [executeImportDeclRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq',
      ← EbnfValue.terminal_of_view (.hardKeyword .importKw) rawImport,
      ← EbnfValue.rule_of_view .moduleRef rawReference,
      ← EbnfValue.terminal_of_view (.hardKeyword .asKw) rawAs,
      ← EbnfValue.terminal_of_view (.category .identifier) rawName,
      ← EbnfValue.terminal_of_view (.symbol .semicolon) rawSemicolon]
    exact .importDeclAliased origin finish importKw reference asKw
      nameData semicolon name.identifierProjection_projects witness
  · let viewed := EbnfValue.sequenceFlatView itemsChildren raw
    let rawImport := viewed.1
    let rawReference := viewed.2.1
    let rawDot := viewed.2.2.1
    let rawOpen := viewed.2.2.2.1
    let rawEntries := viewed.2.2.2.2.1
    let rawClose := viewed.2.2.2.2.2.1
    let rawHiding := viewed.2.2.2.2.2.2.1
    let rawSemicolon := viewed.2.2.2.2.2.2.2.1
    let importKw := EbnfValue.terminalView
      (.hardKeyword .importKw) rawImport
    let reference := EbnfValue.ruleView .moduleRef rawReference
    let dot := EbnfValue.terminalView (.symbol .dot) rawDot
    let openBrace := EbnfValue.terminalView (.symbol .leftBrace) rawOpen
    let entries := (EbnfValue.list0View entryAtom rawEntries).map
      (EbnfValue.ruleView .importEntry)
    let closeBrace := EbnfValue.terminalView
      (.symbol .rightBrace) rawClose
    let hidingValue := (EbnfValue.optionalView hidingAtom rawHiding).map
      (EbnfValue.ruleView .hidingClause)
    let semicolon := EbnfValue.terminalView
      (.symbol .semicolon) rawSemicolon
    have rawEq := EbnfValue.sequence_of_flat_view itemsChildren raw
    have rawEq' : EbnfValue.sequence itemsChildren
        (EbnfValue.sequenceValuesBuild itemsChildren
          ⟨rawImport, rawReference, rawDot, rawOpen, rawEntries,
            rawClose, rawHiding, rawSemicolon, ⟨⟩⟩) = raw := rawEq
    let rawEntryValues := EbnfValue.list0View entryAtom rawEntries
    have entryAtomsEq : rawEntryValues.map (fun rawEntry =>
        EbnfValue.ruleAtom .importEntry
          (EbnfValue.ruleView .importEntry rawEntry)) =
        rawEntryValues :=
      importDeclRuleAtoms_of_views .importEntry rawEntryValues
    have entriesEq : EbnfValue.list0 entryAtom
        (entries.map (EbnfValue.ruleAtom .importEntry)) = rawEntries := by
      simp only [entries, List.map_map,
        Function.comp_def]
      rw [entryAtomsEq]
      exact EbnfValue.list0_of_view entryAtom rawEntries
    have hidingEq : EbnfValue.optional hidingAtom
        (hidingValue.map (EbnfValue.ruleAtom .hidingClause)) =
        rawHiding :=
      importDeclOptionalRuleAtom_of_view .hidingClause rawHiding
    have resultEq : executeImportDeclRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness {
          moduleRef := reference
          mode := .items
            (RuleReduction.between file openBrace.span closeBrace.span {
              entries := entries
            }) hidingValue
        } := by
      rw [executeImportDeclRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq',
      ← EbnfValue.terminal_of_view (.hardKeyword .importKw) rawImport,
      ← EbnfValue.rule_of_view .moduleRef rawReference,
      ← EbnfValue.terminal_of_view (.symbol .dot) rawDot,
      ← EbnfValue.terminal_of_view (.symbol .leftBrace) rawOpen,
      ← entriesEq,
      ← EbnfValue.terminal_of_view (.symbol .rightBrace) rawClose,
      ← hidingEq,
      ← EbnfValue.terminal_of_view (.symbol .semicolon) rawSemicolon]
    exact .importDeclItems origin finish importKw reference dot openBrace
      entries closeBrace hidingValue semicolon witness

private theorem exportDeclRuleAtoms_of_views
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId)
    (values : List (EbnfValue file tokens
      (.atom (.nonterminal rule)))) :
    (values.map (EbnfValue.ruleView rule)).map
      (EbnfValue.ruleAtom rule) = values := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨EbnfValue.rule_of_view rule head, induction⟩

/-- The export-declaration executor realizes its selected root reduction. -/
theorem executeExportDeclRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .exportDecl origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .exportDecl)) :
    RuleReduction file tokens .exportDecl origin finish input
      (executeExportDeclRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let localAtom : EbnfExpr := .atom (.nonterminal .localExportEntry)
  let remoteAtom : EbnfExpr := .atom (.nonterminal .remoteExportEntry)
  let localChildren : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .exportKw)),
    .atom (.terminal (.symbol .leftBrace)), .list0 localAtom,
    .atom (.terminal (.symbol .rightBrace)),
    .atom (.terminal (.symbol .semicolon))]
  let moduleChildren : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .exportKw)),
    .atom (.nonterminal .moduleRef),
    .atom (.terminal (.symbol .semicolon))]
  let aliasChildren : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .exportKw)),
    .atom (.nonterminal .moduleRef),
    .atom (.terminal (.hardKeyword .asKw)),
    .atom (.terminal (.category .identifier)),
    .atom (.terminal (.symbol .semicolon))]
  let wildcardChildren : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .exportKw)),
    .atom (.nonterminal .moduleRef), .atom (.terminal (.symbol .dot)),
    .atom (.terminal (.symbol .star)),
    .atom (.terminal (.symbol .semicolon))]
  let bracedChildren : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .exportKw)),
    .atom (.nonterminal .moduleRef), .atom (.terminal (.symbol .dot)),
    .atom (.terminal (.symbol .leftBrace)), .list0 remoteAtom,
    .atom (.terminal (.symbol .rightBrace)),
    .atom (.terminal (.symbol .semicolon))]
  let branches : List EbnfExpr := [.sequence localChildren,
    .sequence moduleChildren, .sequence aliasChildren,
    .sequence wildcardChildren, .sequence bracedChildren]
  change EbnfValue file tokens (.choice branches) at input
  generalize viewEq : EbnfValue.choiceView branches input = viewed
  rcases viewed with ⟨branch, raw⟩
  have inputEq : EbnfValue.choice branches ⟨branch, raw⟩ = input := by
    calc
      _ = EbnfValue.choice branches
          (EbnfValue.choiceView branches input) := by rw [viewEq]
      _ = input := EbnfValue.choice_of_view branches input
  have branchCases : branch = 0 ∨ branch = 1 ∨ branch = 2 ∨
      branch = 3 ∨ branch = 4 := by
    have branchesLength : branches.length = 5 := by rfl
    have bound : branch.val < 5 := by
      calc
        branch.val < branches.length := branch.isLt
        _ = 5 := branchesLength
    have values : branch.val = 0 ∨ branch.val = 1 ∨
        branch.val = 2 ∨ branch.val = 3 ∨ branch.val = 4 := by omega
    rcases values with h | h | h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h))))
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  rcases branchCases with rfl | rfl | rfl | rfl | rfl
  · let values := EbnfValue.sequenceFlatView localChildren raw
    let rawExport := values.1
    let rawOpen := values.2.1
    let rawEntries := values.2.2.1
    let rawClose := values.2.2.2.1
    let rawSemicolon := values.2.2.2.2.1
    have rawEq := EbnfValue.sequence_of_flat_view localChildren raw
    have rawEq' : EbnfValue.sequence localChildren
        (EbnfValue.sequenceValuesBuild localChildren
          ⟨rawExport, rawOpen, rawEntries, rawClose, rawSemicolon, ⟨⟩⟩) =
        raw := rawEq
    let exportKw := EbnfValue.terminalView
      (.hardKeyword .exportKw) rawExport
    let openBrace := EbnfValue.terminalView (.symbol .leftBrace) rawOpen
    let rawEntryValues := EbnfValue.list0View localAtom rawEntries
    let entries := rawEntryValues.map
      (EbnfValue.ruleView .localExportEntry)
    let closeBrace := EbnfValue.terminalView (.symbol .rightBrace) rawClose
    let semicolon := EbnfValue.terminalView (.symbol .semicolon) rawSemicolon
    have entriesEq : EbnfValue.list0 localAtom
        (entries.map (EbnfValue.ruleAtom .localExportEntry)) =
        rawEntries := by
      rw [exportDeclRuleAtoms_of_views .localExportEntry rawEntryValues]
      exact EbnfValue.list0_of_view localAtom rawEntries
    have resultEq : executeExportDeclRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness (.local
          (RuleReduction.between file openBrace.span closeBrace.span {
            entries := entries
          })) := by
      rw [executeExportDeclRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq',
      ← EbnfValue.terminal_of_view (.hardKeyword .exportKw) rawExport,
      ← EbnfValue.terminal_of_view (.symbol .leftBrace) rawOpen,
      ← entriesEq,
      ← EbnfValue.terminal_of_view (.symbol .rightBrace) rawClose,
      ← EbnfValue.terminal_of_view (.symbol .semicolon) rawSemicolon]
    exact .exportDeclLocal origin finish exportKw openBrace entries
      closeBrace semicolon witness
  · let values := EbnfValue.sequenceFlatView moduleChildren raw
    let rawExport := values.1
    let rawReference := values.2.1
    let rawSemicolon := values.2.2.1
    have rawEq := EbnfValue.sequence_of_flat_view moduleChildren raw
    have rawEq' : EbnfValue.sequence moduleChildren
        (EbnfValue.sequenceValuesBuild moduleChildren
          ⟨rawExport, rawReference, rawSemicolon, ⟨⟩⟩) = raw := rawEq
    let exportKw := EbnfValue.terminalView
      (.hardKeyword .exportKw) rawExport
    let reference := EbnfValue.ruleView .moduleRef rawReference
    let semicolon := EbnfValue.terminalView (.symbol .semicolon) rawSemicolon
    have resultEq : executeExportDeclRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness
          (.module reference none) := by
      rw [executeExportDeclRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq',
      ← EbnfValue.terminal_of_view (.hardKeyword .exportKw) rawExport,
      ← EbnfValue.rule_of_view .moduleRef rawReference,
      ← EbnfValue.terminal_of_view (.symbol .semicolon) rawSemicolon]
    exact .exportDeclModule origin finish exportKw reference semicolon witness
  · let values := EbnfValue.sequenceFlatView aliasChildren raw
    let rawExport := values.1
    let rawReference := values.2.1
    let rawAs := values.2.2.1
    let rawName := values.2.2.2.1
    let rawSemicolon := values.2.2.2.2.1
    have rawEq := EbnfValue.sequence_of_flat_view aliasChildren raw
    have rawEq' : EbnfValue.sequence aliasChildren
        (EbnfValue.sequenceValuesBuild aliasChildren
          ⟨rawExport, rawReference, rawAs, rawName, rawSemicolon, ⟨⟩⟩) =
        raw := rawEq
    let exportKw := EbnfValue.terminalView
      (.hardKeyword .exportKw) rawExport
    let reference := EbnfValue.ruleView .moduleRef rawReference
    let asKw := EbnfValue.terminalView (.hardKeyword .asKw) rawAs
    let name := EbnfValue.terminalView (.category .identifier) rawName
    let nameData : RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier := {
      matched := name
      spelling := name.identifierProjection.1
      parsed := name.identifierProjection.2
    }
    let semicolon := EbnfValue.terminalView (.symbol .semicolon) rawSemicolon
    have resultEq : executeExportDeclRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness (.module reference
          (some (RuleReduction.terminalLoc name
            name.identifierProjection.2))) := by
      rw [executeExportDeclRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq',
      ← EbnfValue.terminal_of_view (.hardKeyword .exportKw) rawExport,
      ← EbnfValue.rule_of_view .moduleRef rawReference,
      ← EbnfValue.terminal_of_view (.hardKeyword .asKw) rawAs,
      ← EbnfValue.terminal_of_view (.category .identifier) rawName,
      ← EbnfValue.terminal_of_view (.symbol .semicolon) rawSemicolon]
    exact .exportDeclAliased origin finish exportKw reference asKw nameData
      semicolon name.identifierProjection_projects witness
  · let values := EbnfValue.sequenceFlatView wildcardChildren raw
    let rawExport := values.1
    let rawReference := values.2.1
    let rawDot := values.2.2.1
    let rawStar := values.2.2.2.1
    let rawSemicolon := values.2.2.2.2.1
    have rawEq := EbnfValue.sequence_of_flat_view wildcardChildren raw
    have rawEq' : EbnfValue.sequence wildcardChildren
        (EbnfValue.sequenceValuesBuild wildcardChildren
          ⟨rawExport, rawReference, rawDot, rawStar, rawSemicolon, ⟨⟩⟩) =
        raw := rawEq
    let exportKw := EbnfValue.terminalView
      (.hardKeyword .exportKw) rawExport
    let reference := EbnfValue.ruleView .moduleRef rawReference
    let dot := EbnfValue.terminalView (.symbol .dot) rawDot
    let star := EbnfValue.terminalView (.symbol .star) rawStar
    let semicolon := EbnfValue.terminalView (.symbol .semicolon) rawSemicolon
    have resultEq : executeExportDeclRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness (.from reference
          (RuleReduction.between file dot.span star.span
            (.dotWildcard (RuleReduction.terminalLoc star .wildcard)))) := by
      rw [executeExportDeclRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq',
      ← EbnfValue.terminal_of_view (.hardKeyword .exportKw) rawExport,
      ← EbnfValue.rule_of_view .moduleRef rawReference,
      ← EbnfValue.terminal_of_view (.symbol .dot) rawDot,
      ← EbnfValue.terminal_of_view (.symbol .star) rawStar,
      ← EbnfValue.terminal_of_view (.symbol .semicolon) rawSemicolon]
    exact .exportDeclWildcard origin finish exportKw reference dot star
      semicolon (.wildcardStar star) witness
  · let values := EbnfValue.sequenceFlatView bracedChildren raw
    let rawExport := values.1
    let rawReference := values.2.1
    let rawDot := values.2.2.1
    let rawOpen := values.2.2.2.1
    let rawEntries := values.2.2.2.2.1
    let rawClose := values.2.2.2.2.2.1
    let rawSemicolon := values.2.2.2.2.2.2.1
    have rawEq := EbnfValue.sequence_of_flat_view bracedChildren raw
    have rawEq' : EbnfValue.sequence bracedChildren
        (EbnfValue.sequenceValuesBuild bracedChildren
          ⟨rawExport, rawReference, rawDot, rawOpen, rawEntries, rawClose,
            rawSemicolon, ⟨⟩⟩) = raw := rawEq
    let exportKw := EbnfValue.terminalView
      (.hardKeyword .exportKw) rawExport
    let reference := EbnfValue.ruleView .moduleRef rawReference
    let dot := EbnfValue.terminalView (.symbol .dot) rawDot
    let openBrace := EbnfValue.terminalView (.symbol .leftBrace) rawOpen
    let rawEntryValues := EbnfValue.list0View remoteAtom rawEntries
    let entries := rawEntryValues.map
      (EbnfValue.ruleView .remoteExportEntry)
    let closeBrace := EbnfValue.terminalView (.symbol .rightBrace) rawClose
    let semicolon := EbnfValue.terminalView (.symbol .semicolon) rawSemicolon
    have entriesEq : EbnfValue.list0 remoteAtom
        (entries.map (EbnfValue.ruleAtom .remoteExportEntry)) =
        rawEntries := by
      rw [exportDeclRuleAtoms_of_views .remoteExportEntry rawEntryValues]
      exact EbnfValue.list0_of_view remoteAtom rawEntries
    have resultEq : executeExportDeclRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness (.from reference
          (RuleReduction.between file openBrace.span closeBrace.span
            (.braced entries))) := by
      rw [executeExportDeclRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq',
      ← EbnfValue.terminal_of_view (.hardKeyword .exportKw) rawExport,
      ← EbnfValue.rule_of_view .moduleRef rawReference,
      ← EbnfValue.terminal_of_view (.symbol .dot) rawDot,
      ← EbnfValue.terminal_of_view (.symbol .leftBrace) rawOpen,
      ← entriesEq,
      ← EbnfValue.terminal_of_view (.symbol .rightBrace) rawClose,
      ← EbnfValue.terminal_of_view (.symbol .semicolon) rawSemicolon]
    exact .exportDeclBraced origin finish exportKw reference dot openBrace
      entries closeBrace semicolon witness

/-- The import-entry executor realizes its selected root reduction. -/
theorem executeImportEntryRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .importEntry origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .importEntry)) :
    RuleReduction file tokens .importEntry origin finish input
      (executeImportEntryRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let starAtom : EbnfExpr :=
    .atom (.terminal (.symbol .star))
  let identifierAtom : EbnfExpr :=
    .atom (.terminal (.category .identifier))
  let aliasChildren : List EbnfExpr := [
    .atom (.terminal (.hardKeyword .asKw)), identifierAtom]
  let namedChildren : List EbnfExpr := [
    identifierAtom, .optional (.sequence aliasChildren)]
  change EbnfValue file tokens
    (.choice [starAtom, .sequence namedChildren]) at input
  generalize viewEq : EbnfValue.choice2View
    starAtom (.sequence namedChildren) input = viewed
  have inputEq := EbnfValue.choice2_of_view
    starAtom (.sequence namedChildren) input
  rw [viewEq] at inputEq
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  rcases viewed with raw | raw
  · let star := EbnfValue.terminalView (.symbol .star) raw
    have rawEq := EbnfValue.terminal_of_view (.symbol .star) raw
    have resultEq : executeImportEntryRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness
          (.wildcard (RuleReduction.terminalLoc star .wildcard)) := by
      rw [executeImportEntryRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .importEntryWildcard origin finish star (.wildcardStar star) witness
  · let viewed := EbnfValue.sequence2View
      identifierAtom (.optional (.sequence aliasChildren)) raw
    let name := EbnfValue.terminalView
      (.category .identifier) viewed.1
    let nameData : RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier := {
      matched := name
      spelling := name.identifierProjection.1
      parsed := name.identifierProjection.2
    }
    have rawEq := EbnfValue.sequence2_of_view
      identifierAtom (.optional (.sequence aliasChildren)) raw
    have nameEq := EbnfValue.terminal_of_view
      (.category .identifier) viewed.1
    generalize optionalEq : EbnfValue.optionalView (.sequence aliasChildren)
      viewed.2 = aliasValue
    simp only [viewed, identifierAtom, aliasChildren] at optionalEq
    cases aliasValue with
    | none =>
        have rawOptionalEq : EbnfValue.optional (.sequence aliasChildren)
            none = viewed.2 := by
          calc
            _ = EbnfValue.optional (.sequence aliasChildren)
                (EbnfValue.optionalView (.sequence aliasChildren)
                  viewed.2) := by rw [optionalEq]
            _ = viewed.2 := EbnfValue.optional_of_view
              (.sequence aliasChildren) viewed.2
        have resultEq : executeImportEntryRoot file tokens origin finish
            ready.1 ready.2.1 input = sourceLoc witness (.named
              (RuleReduction.terminalLoc name name.identifierProjection.2)
              none) := by
          rw [executeImportEntryRoot, viewEq]
          simp only
          rw [optionalEq]
          rfl
        rw [resultEq, ← inputEq, ← rawEq, ← nameEq, ← rawOptionalEq]
        exact .importEntryNamed origin finish nameData
          name.identifierProjection_projects witness
    | some rawAlias =>
        let aliasViewed := EbnfValue.sequence2View
          (.atom (.terminal (.hardKeyword .asKw))) identifierAtom rawAlias
        let asKw := EbnfValue.terminalView
          (.hardKeyword .asKw) aliasViewed.1
        let aliasName := EbnfValue.terminalView
          (.category .identifier) aliasViewed.2
        let aliasData : RuleReduction.SpelledTerminalData file tokens
            (.category .identifier) Identifier := {
          matched := aliasName
          spelling := aliasName.identifierProjection.1
          parsed := aliasName.identifierProjection.2
        }
        have rawOptionalEq : EbnfValue.optional (.sequence aliasChildren)
            (some rawAlias) = viewed.2 := by
          calc
            _ = EbnfValue.optional (.sequence aliasChildren)
                (EbnfValue.optionalView (.sequence aliasChildren)
                  viewed.2) := by rw [optionalEq]
            _ = viewed.2 := EbnfValue.optional_of_view
              (.sequence aliasChildren) viewed.2
        have rawAliasEq := EbnfValue.sequence2_of_view
          (.atom (.terminal (.hardKeyword .asKw))) identifierAtom rawAlias
        have asEq := EbnfValue.terminal_of_view
          (.hardKeyword .asKw) aliasViewed.1
        have aliasNameEq := EbnfValue.terminal_of_view
          (.category .identifier) aliasViewed.2
        have resultEq : executeImportEntryRoot file tokens origin finish
            ready.1 ready.2.1 input = sourceLoc witness (.named
              (RuleReduction.terminalLoc name name.identifierProjection.2)
              (some (RuleReduction.terminalLoc aliasName
                aliasName.identifierProjection.2))) := by
          rw [executeImportEntryRoot, viewEq]
          simp only
          rw [optionalEq]
          rfl
        rw [resultEq, ← inputEq, ← rawEq, ← nameEq, ← rawOptionalEq,
          ← rawAliasEq, ← asEq, ← aliasNameEq]
        exact .importEntryAliased origin finish nameData aliasData asKw
          name.identifierProjection_projects
          aliasName.identifierProjection_projects witness

/-- The local-export-entry executor realizes its selected root reduction. -/
theorem executeLocalExportEntryRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .localExportEntry origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .localExportEntry)) :
    RuleReduction file tokens .localExportEntry origin finish input
      (executeLocalExportEntryRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let starAtom : EbnfExpr :=
    .atom (.terminal (.symbol .star))
  let allChildren : List EbnfExpr := [
    .atom (.nonterminal .moduleRef),
    .atom (.terminal (.symbol .dot)), starAtom]
  let branches : List EbnfExpr := [
    starAtom, .atom (.nonterminal .exportItem), .sequence allChildren]
  change EbnfValue file tokens (.choice branches) at input
  generalize viewEq : EbnfValue.choiceView branches input = viewed
  rcases viewed with ⟨branch, raw⟩
  have inputEq : EbnfValue.choice branches ⟨branch, raw⟩ = input := by
    calc
      _ = EbnfValue.choice branches
          (EbnfValue.choiceView branches input) := by rw [viewEq]
      _ = input := EbnfValue.choice_of_view branches input
  have branchCases : branch = 0 ∨ branch = 1 ∨ branch = 2 := by
    have branchesLength : branches.length = 3 := by rfl
    have bound : branch.val < 3 := by
      calc
        branch.val < branches.length := branch.isLt
        _ = 3 := branchesLength
    have values : branch.val = 0 ∨ branch.val = 1 ∨
        branch.val = 2 := by omega
    rcases values with valueEq | valueEq | valueEq
    · exact Or.inl (Fin.ext valueEq)
    · exact Or.inr (Or.inl (Fin.ext valueEq))
    · exact Or.inr (Or.inr (Fin.ext valueEq))
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  rcases branchCases with rfl | rfl | rfl
  · let star := EbnfValue.terminalView (.symbol .star) raw
    have rawEq := EbnfValue.terminal_of_view (.symbol .star) raw
    have resultEq : executeLocalExportEntryRoot file tokens
        origin finish ready.1 ready.2.1 input = sourceLoc witness
          (.wildcard (RuleReduction.terminalLoc star .wildcard)) := by
      rw [executeLocalExportEntryRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .localExportEntryWildcard origin finish star
      (.wildcardStar star) witness
  · let item := EbnfValue.ruleView .exportItem raw
    have rawEq := EbnfValue.rule_of_view .exportItem raw
    have resultEq : executeLocalExportEntryRoot file tokens
        origin finish ready.1 ready.2.1 input =
          sourceLoc witness (.item item) := by
      rw [executeLocalExportEntryRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .localExportEntryItem origin finish item witness
  · let values := EbnfValue.sequenceFlatView allChildren raw
    let rawReference := values.1
    let rawDot := values.2.1
    let rawStar := values.2.2.1
    let reference := EbnfValue.ruleView .moduleRef rawReference
    let dot := EbnfValue.terminalView (.symbol .dot) rawDot
    let star := EbnfValue.terminalView (.symbol .star) rawStar
    have rawEq := EbnfValue.sequence_of_flat_view allChildren raw
    have rawEq' : EbnfValue.sequence allChildren
        (EbnfValue.sequenceValuesBuild allChildren
          ⟨rawReference, rawDot, rawStar, ⟨⟩⟩) = raw := rawEq
    have resultEq : executeLocalExportEntryRoot file tokens
        origin finish ready.1 ready.2.1 input = sourceLoc witness
          (.allFrom reference
            (RuleReduction.terminalLoc star .wildcard)) := by
      rw [executeLocalExportEntryRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq',
      ← EbnfValue.rule_of_view .moduleRef rawReference,
      ← EbnfValue.terminal_of_view (.symbol .dot) rawDot,
      ← EbnfValue.terminal_of_view (.symbol .star) rawStar]
    exact .localExportEntryAllFrom origin finish reference dot star
      (.wildcardStar star) witness

/-- The remote-export-entry executor realizes its selected root reduction. -/
theorem executeRemoteExportEntryRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens
      .remoteExportEntry origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .remoteExportEntry)) :
    RuleReduction file tokens .remoteExportEntry origin finish input
      (executeRemoteExportEntryRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let starAtom : EbnfExpr :=
    .atom (.terminal (.symbol .star))
  let itemAtom : EbnfExpr :=
    .atom (.nonterminal .exportItem)
  change EbnfValue file tokens (.choice [starAtom, itemAtom]) at input
  generalize viewEq : EbnfValue.choice2View
    starAtom itemAtom input = viewed
  have inputEq := EbnfValue.choice2_of_view starAtom itemAtom input
  rw [viewEq] at inputEq
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  rcases viewed with raw | raw
  · let star := EbnfValue.terminalView (.symbol .star) raw
    have rawEq := EbnfValue.terminal_of_view (.symbol .star) raw
    have resultEq : executeRemoteExportEntryRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness
          (.wildcard (RuleReduction.terminalLoc star .wildcard)) := by
      rw [executeRemoteExportEntryRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq]
    exact .remoteExportEntryWildcard origin finish star
      (.wildcardStar star) witness
  · let item := EbnfValue.ruleView .exportItem raw
    have rawEq := EbnfValue.rule_of_view .exportItem raw
    have resultEq : executeRemoteExportEntryRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness (.item item) := by
      rw [executeRemoteExportEntryRoot, viewEq]
    rw [resultEq, ← inputEq, ← rawEq]
    exact .remoteExportEntryItem origin finish item witness

private theorem hidingClauseIdentifierAtoms_of_views
    {file : WorkspaceFile} {tokens : List Token}
    (values : List (EbnfValue file tokens
      (.atom (.terminal (.category .identifier))))) :
    values.map (fun raw => EbnfValue.terminalAtom
      (.category .identifier) (EbnfValue.terminalView
        (.category .identifier) raw)) = values := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp [EbnfValue.terminal_of_view]

/-- The hiding-clause executor realizes its exact root reduction. -/
theorem executeHidingClauseRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .hidingClause origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .hidingClause)) :
    RuleReduction file tokens .hidingClause origin finish input
      (executeHidingClauseRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let keywordAtom : EbnfExpr :=
    .atom (.terminal (.hardKeyword .hidingKw))
  let openAtom : EbnfExpr :=
    .atom (.terminal (.symbol .leftBrace))
  let identifierAtom : EbnfExpr :=
    .atom (.terminal (.category .identifier))
  let namesAtom : EbnfExpr := .list0 identifierAtom
  let closeAtom : EbnfExpr :=
    .atom (.terminal (.symbol .rightBrace))
  change EbnfValue file tokens
    (.sequence [keywordAtom, openAtom, namesAtom, closeAtom]) at input
  let viewed := EbnfValue.sequence4View
    keywordAtom openAtom namesAtom closeAtom input
  let keyword := EbnfValue.terminalView
    (.hardKeyword .hidingKw) viewed.1
  let openBrace := EbnfValue.terminalView
    (.symbol .leftBrace) viewed.2.1
  let rawNames := EbnfValue.list0View identifierAtom viewed.2.2.1
  let closeBrace := EbnfValue.terminalView
    (.symbol .rightBrace) viewed.2.2.2
  let names : List (RuleReduction.SpelledTerminalData
      file tokens (.category .identifier) Identifier) :=
    rawNames.map fun rawName =>
      let name := EbnfValue.terminalView
        (.category .identifier) rawName
      ({
        matched := name
        spelling := name.identifierProjection.1
        parsed := name.identifierProjection.2
      } : RuleReduction.SpelledTerminalData file tokens
        (.category .identifier) Identifier)
  let executableNames : List IdentifierOccurrence :=
    rawNames.map fun rawName =>
      let name := EbnfValue.terminalView
        (.category .identifier) rawName
      ({ span := name.span, payload := name.identifierProjection.2 } :
        IdentifierOccurrence)
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have namesEq : EbnfValue.list0 identifierAtom
      (names.map fun value => EbnfValue.terminalAtom
        (.category .identifier) value.matched) = viewed.2.2.1 := by
    have mappedEq : names.map (fun value => EbnfValue.terminalAtom
        (.category .identifier) value.matched) = rawNames := by
      simpa [names, rawNames, List.map_map, Function.comp_def] using
        hidingClauseIdentifierAtoms_of_views rawNames
    rw [mappedEq]
    exact EbnfValue.list0_of_view identifierAtom viewed.2.2.1
  have executableNamesEq : executableNames = names.map fun name =>
      RuleReduction.terminalLoc name.matched name.parsed := by
    simp [executableNames, names, List.map_map,
      RuleReduction.terminalLoc]
  have resultEq : executeHidingClauseRoot file tokens origin finish
      ready.1 ready.2.1 input = sourceLoc witness {
        names := executableNames
      } := by
    rfl
  rw [resultEq, executableNamesEq,
    ← EbnfValue.sequence4_of_view keywordAtom openAtom namesAtom
      closeAtom input,
    ← EbnfValue.terminal_of_view (.hardKeyword .hidingKw) viewed.1,
    ← EbnfValue.terminal_of_view (.symbol .leftBrace) viewed.2.1,
    ← namesEq,
    ← EbnfValue.terminal_of_view (.symbol .rightBrace) viewed.2.2.2]
  exact .hidingClause origin finish keyword openBrace names closeBrace
    (by
      intro name nameMem
      simp only [names, List.mem_map] at nameMem
      rcases nameMem with ⟨rawName, _rawMem, rfl⟩
      exact (EbnfValue.terminalView (.category .identifier)
        rawName).identifierProjection_projects)
    witness

/-- The type executor realizes every exact compile-time or arrow reduction. -/
theorem executeTypeRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .type origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .type)) :
    RuleReduction file tokens .type origin finish input
      (executeTypeRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let comptimeAtom : EbnfExpr :=
    .atom (.terminal (.contextualKeyword .comptimeKw))
  let typeAtom : EbnfExpr := .atom (.nonterminal .type)
  let atomAtom : EbnfExpr := .atom (.nonterminal .typeAtom)
  let arrowAtom : EbnfExpr := .atom (.terminal (.symbol .arrow))
  let arrowSeq : EbnfExpr := .sequence [arrowAtom, typeAtom]
  let comptimeBranch : EbnfExpr := .sequence [comptimeAtom, typeAtom]
  let plainBranch : EbnfExpr :=
    .sequence [atomAtom, .optional arrowSeq]
  change EbnfValue file tokens
    (.choice [comptimeBranch, plainBranch]) at input
  generalize choiceEq : EbnfValue.choice2View
    comptimeBranch plainBranch input = selected
  have inputEq := EbnfValue.choice2_of_view
    comptimeBranch plainBranch input
  rw [choiceEq] at inputEq
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  cases selected with
  | inl raw =>
      let viewed := EbnfValue.sequence2View comptimeAtom typeAtom raw
      let comptime := EbnfValue.terminalView
        (.contextualKeyword .comptimeKw) viewed.1
      let inner := EbnfValue.ruleView .type viewed.2
      have sequenceEq := EbnfValue.sequence2_of_view
        comptimeAtom typeAtom raw
      have comptimeEq := EbnfValue.terminal_of_view
        (.contextualKeyword .comptimeKw) viewed.1
      have innerEq := EbnfValue.rule_of_view .type viewed.2
      have resultEq : executeTypeRoot file tokens origin finish
          ready.1 ready.2.1 input = sourceLoc witness (.comptime
            { span := comptime.span, payload := .comptimeModifier } inner) := by
        simp only [executeTypeRoot, comptimeBranch, plainBranch,
          comptimeAtom, typeAtom, atomAtom, arrowAtom, arrowSeq,
          choiceEq, viewed, comptime, inner, witness]
      rw [resultEq, ← inputEq, ← sequenceEq, ← comptimeEq, ← innerEq]
      exact .typeComptime origin finish comptime inner
        (.comptimeModifier comptime) witness
  | inr raw =>
      let viewed := EbnfValue.sequence2View
        atomAtom (.optional arrowSeq) raw
      let domain := EbnfValue.ruleView .typeAtom viewed.1
      generalize optionalEq : EbnfValue.optionalView
        arrowSeq viewed.2 = selectedArrow
      have sequenceEq := EbnfValue.sequence2_of_view
        atomAtom (.optional arrowSeq) raw
      have domainEq := EbnfValue.rule_of_view .typeAtom viewed.1
      have optionalRebuild := EbnfValue.optional_of_view arrowSeq viewed.2
      rw [optionalEq] at optionalRebuild
      cases selectedArrow with
      | none =>
          have resultEq : executeTypeRoot file tokens origin finish
              ready.1 ready.2.1 input = domain := by
            simp only [executeTypeRoot, comptimeBranch, plainBranch,
              comptimeAtom, typeAtom, atomAtom, arrowAtom, arrowSeq,
              choiceEq, viewed, domain, optionalEq]
          rw [resultEq, ← inputEq, ← sequenceEq, ← domainEq,
            ← optionalRebuild]
          exact .typeAtomOnly origin finish domain
      | some rawArrow =>
          let arrowViewed := EbnfValue.sequence2View
            arrowAtom typeAtom rawArrow
          let arrow := EbnfValue.terminalView (.symbol .arrow) arrowViewed.1
          let codomain := EbnfValue.ruleView .type arrowViewed.2
          have arrowSequenceEq := EbnfValue.sequence2_of_view
            arrowAtom typeAtom rawArrow
          have arrowEq := EbnfValue.terminal_of_view
            (.symbol .arrow) arrowViewed.1
          have codomainEq := EbnfValue.rule_of_view .type arrowViewed.2
          have resultEq : executeTypeRoot file tokens origin finish
              ready.1 ready.2.1 input =
                sourceLoc witness (.function domain codomain) := by
            simp only [executeTypeRoot, comptimeBranch, plainBranch,
              comptimeAtom, typeAtom, atomAtom, arrowAtom, arrowSeq,
              choiceEq, viewed, domain, optionalEq, arrowViewed, codomain,
              witness]
          rw [resultEq, ← inputEq, ← sequenceEq, ← domainEq,
            ← optionalRebuild, ← arrowSequenceEq, ← arrowEq,
            ← codomainEq]
          exact .typeFunction origin finish domain arrow codomain witness

private theorem typeAtomRuleAtoms_of_views
    {file : WorkspaceFile} {tokens : List Token}
    (inputs : List
      (EbnfValue file tokens (.atom (.nonterminal .type)))) :
    (inputs.map (EbnfValue.ruleView .type)).map
        (EbnfValue.ruleAtom .type) = inputs := by
  induction inputs with
  | nil => rfl
  | cons head tail induction =>
      simp [EbnfValue.rule_of_view, induction]

private theorem typeAtomRuleList1_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens
      (.list1 (.atom (.nonterminal .type)))) :
    EbnfValue.list1 (.atom (.nonterminal .type))
      ((EbnfValue.list1View (.atom (.nonterminal .type)) input).map
        (EbnfValue.ruleView .type) |>.map (EbnfValue.ruleAtom .type)) =
      input := by
  let viewed := EbnfValue.list1View
    (.atom (.nonterminal .type)) input
  have mapEq : (viewed.map (EbnfValue.ruleView .type)).map
      (EbnfValue.ruleAtom .type) = viewed := by
    cases viewed with
    | mk head tail =>
        simp only [NonemptyList.map, NonemptyList.mk.injEq]
        exact ⟨EbnfValue.rule_of_view .type head,
          typeAtomRuleAtoms_of_views tail⟩
  rw [mapEq]
  exact EbnfValue.list1_of_view (.atom (.nonterminal .type)) input

/-- The atomic-type executor realizes every exact source-rule reduction. -/
theorem executeTypeAtomRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .typeAtom origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .typeAtom)) :
    RuleReduction file tokens .typeAtom origin finish input
      (executeTypeAtomRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let atAtom : EbnfExpr := .atom (.terminal (.symbol .at))
  let atomAtom : EbnfExpr := .atom (.nonterminal .typeAtom)
  let nameAtom : EbnfExpr := .atom (.nonterminal .qualifiedName)
  let openAtom : EbnfExpr := .atom (.terminal (.symbol .leftParen))
  let closeAtom : EbnfExpr := .atom (.terminal (.symbol .rightParen))
  let commaAtom : EbnfExpr := .atom (.terminal (.symbol .comma))
  let typeAtom : EbnfExpr := .atom (.nonterminal .type)
  let argumentsExpr : EbnfExpr :=
    .sequence [openAtom, .list1 typeAtom, closeAtom]
  let tupleTail := EbnfValue.fixedInfixTailExpr (.symbol .comma) .type
  let branches : List EbnfExpr := [
    .sequence [atAtom, atomAtom],
    .sequence [nameAtom, .optional argumentsExpr],
    .sequence [openAtom, closeAtom],
    .sequence [openAtom, typeAtom, closeAtom],
    .sequence [openAtom, typeAtom, commaAtom, typeAtom,
      .star tupleTail, closeAtom]]
  change EbnfValue file tokens (.choice branches) at input
  generalize viewEq : EbnfValue.choiceView branches input = viewed
  rcases viewed with ⟨branch, raw⟩
  have inputEq : EbnfValue.choice branches ⟨branch, raw⟩ = input := by
    calc
      _ = EbnfValue.choice branches
          (EbnfValue.choiceView branches input) := by rw [viewEq]
      _ = input := EbnfValue.choice_of_view branches input
  have branchCases : branch = 0 ∨ branch = 1 ∨ branch = 2 ∨
      branch = 3 ∨ branch = 4 := by
    have lengthEq : branches.length = 5 := by rfl
    have bound : branch.val < 5 := by
      simpa [lengthEq] using branch.isLt
    have cases : branch.val = 0 ∨ branch.val = 1 ∨ branch.val = 2 ∨
        branch.val = 3 ∨ branch.val = 4 := by omega
    rcases cases with h | h | h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h))))
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  rcases branchCases with rfl | rfl | rfl | rfl | rfl
  · let viewed := EbnfValue.sequence2View atAtom atomAtom raw
    let marker := EbnfValue.terminalView (.symbol .at) viewed.1
    let inner := EbnfValue.ruleView .typeAtom viewed.2
    have rawEq := EbnfValue.sequence2_of_view atAtom atomAtom raw
    have markerEq := EbnfValue.terminal_of_view (.symbol .at) viewed.1
    have innerEq := EbnfValue.rule_of_view .typeAtom viewed.2
    have resultEq : executeTypeAtomRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness
          (.proxy (RuleReduction.terminalLoc marker ()) inner) := by
      rw [executeTypeAtomRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq, ← markerEq, ← innerEq]
    exact .typeAtomProxy origin finish marker inner witness
  · let viewed := EbnfValue.sequence2View
      nameAtom (.optional argumentsExpr) raw
    let name := EbnfValue.ruleView .qualifiedName viewed.1
    let rootArguments := (EbnfValue.optionalView argumentsExpr
      viewed.2).map fun argumentRaw =>
        let argumentView := EbnfValue.sequence3View
          openAtom (.list1 typeAtom) closeAtom argumentRaw
        (EbnfValue.list1View typeAtom argumentView.2.1).map
          (EbnfValue.ruleView .type)
    have rawEq := EbnfValue.sequence2_of_view
      nameAtom (.optional argumentsExpr) raw
    have nameEq := EbnfValue.rule_of_view .qualifiedName viewed.1
    have rootResultEq : executeTypeAtomRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness
          (.named name rootArguments) := by
      rw [executeTypeAtomRoot, viewEq]
      rfl
    generalize optionalEq : EbnfValue.optionalView argumentsExpr
      viewed.2 = selected
    cases selected with
    | none =>
        have selectedEq : EbnfValue.optional argumentsExpr none =
            viewed.2 := by
          calc
            _ = EbnfValue.optional argumentsExpr
                (EbnfValue.optionalView argumentsExpr viewed.2) := by
              rw [optionalEq]
            _ = viewed.2 :=
              EbnfValue.optional_of_view argumentsExpr viewed.2
        have rootArgumentsEq : rootArguments = none := by
          simp [rootArguments, optionalEq]
        rw [rootResultEq, rootArgumentsEq, ← inputEq, ← rawEq,
          ← nameEq, ← selectedEq]
        exact .typeAtomNamedWithoutArguments origin finish name witness
    | some argumentRaw =>
        let argumentView := EbnfValue.sequence3View
          openAtom (.list1 typeAtom) closeAtom argumentRaw
        let openParen := EbnfValue.terminalView
          (.symbol .leftParen) argumentView.1
        let rawArguments := EbnfValue.list1View
          typeAtom argumentView.2.1
        let arguments := rawArguments.map (EbnfValue.ruleView .type)
        let closeParen := EbnfValue.terminalView
          (.symbol .rightParen) argumentView.2.2
        have selectedEq : EbnfValue.optional argumentsExpr
            (some argumentRaw) = viewed.2 := by
          calc
            _ = EbnfValue.optional argumentsExpr
                (EbnfValue.optionalView argumentsExpr viewed.2) := by
              rw [optionalEq]
            _ = viewed.2 :=
              EbnfValue.optional_of_view argumentsExpr viewed.2
        have argumentEq := EbnfValue.sequence3_of_view
          openAtom (.list1 typeAtom) closeAtom argumentRaw
        have openEq := EbnfValue.terminal_of_view
          (.symbol .leftParen) argumentView.1
        have argumentsEq : EbnfValue.list1 typeAtom
            (arguments.map (EbnfValue.ruleAtom .type)) =
              argumentView.2.1 := by
          exact typeAtomRuleList1_of_view argumentView.2.1
        have closeEq := EbnfValue.terminal_of_view
          (.symbol .rightParen) argumentView.2.2
        have rootArgumentsEq : rootArguments = some arguments := by
          simp [rootArguments, optionalEq, arguments, rawArguments,
            argumentView, openAtom, closeAtom]
        rw [rootResultEq, rootArgumentsEq, ← inputEq, ← rawEq,
          ← nameEq, ← selectedEq, ← argumentEq, ← openEq,
          ← argumentsEq, ← closeEq]
        exact .typeAtomNamedWithArguments origin finish name openParen
          arguments closeParen witness
  · let viewed := EbnfValue.sequence2View openAtom closeAtom raw
    let openParen := EbnfValue.terminalView
      (.symbol .leftParen) viewed.1
    let closeParen := EbnfValue.terminalView
      (.symbol .rightParen) viewed.2
    have rawEq := EbnfValue.sequence2_of_view openAtom closeAtom raw
    have openEq := EbnfValue.terminal_of_view
      (.symbol .leftParen) viewed.1
    have closeEq := EbnfValue.terminal_of_view
      (.symbol .rightParen) viewed.2
    have resultEq : executeTypeAtomRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness (.tuple []) := by
      rw [executeTypeAtomRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq, ← openEq, ← closeEq]
    exact .typeAtomEmptyTuple origin finish openParen closeParen witness
  · let viewed := EbnfValue.sequence3View
      openAtom typeAtom closeAtom raw
    let openParen := EbnfValue.terminalView
      (.symbol .leftParen) viewed.1
    let inner := EbnfValue.ruleView .type viewed.2.1
    let closeParen := EbnfValue.terminalView
      (.symbol .rightParen) viewed.2.2
    have rawEq := EbnfValue.sequence3_of_view
      openAtom typeAtom closeAtom raw
    have openEq := EbnfValue.terminal_of_view
      (.symbol .leftParen) viewed.1
    have innerEq := EbnfValue.rule_of_view .type viewed.2.1
    have closeEq := EbnfValue.terminal_of_view
      (.symbol .rightParen) viewed.2.2
    have resultEq : executeTypeAtomRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness (.group inner) := by
      rw [executeTypeAtomRoot, viewEq]
      rfl
    rw [resultEq, ← inputEq, ← rawEq, ← openEq, ← innerEq,
      ← closeEq]
    exact .typeAtomGroup origin finish openParen inner closeParen witness
  · let children : List EbnfExpr := [openAtom, typeAtom, commaAtom,
      typeAtom, .star tupleTail, closeAtom]
    let viewed := EbnfValue.sequenceFlatView children raw
    let openParen := EbnfValue.terminalView
      (.symbol .leftParen) viewed.1
    let first := EbnfValue.ruleView .type viewed.2.1
    let comma := EbnfValue.terminalView (.symbol .comma) viewed.2.2.1
    let second := EbnfValue.ruleView .type viewed.2.2.2.1
    let rawRest := EbnfValue.starView tupleTail viewed.2.2.2.2.1
    let rest := rawRest.map (EbnfValue.fixedInfixTailView
      (.symbol .comma) .type)
    let closeParen := EbnfValue.terminalView
      (.symbol .rightParen) viewed.2.2.2.2.2.1
    have rawEq := EbnfValue.sequence_of_flat_view children raw
    have openEq := EbnfValue.terminal_of_view
      (.symbol .leftParen) viewed.1
    have firstEq := EbnfValue.rule_of_view .type viewed.2.1
    have commaEq := EbnfValue.terminal_of_view
      (.symbol .comma) viewed.2.2.1
    have secondEq := EbnfValue.rule_of_view .type viewed.2.2.2.1
    have restValuesEq : rest.map (EbnfValue.fixedInfixTailValue
        (.symbol .comma) .type) = rawRest := by
      simp only [rest, List.map_map]
      induction rawRest with
      | nil => rfl
      | cons head tail induction =>
          simp only [List.map_cons, List.cons.injEq]
          exact ⟨EbnfValue.fixedInfixTailValue_of_view
            (.symbol .comma) .type head, induction⟩
    have restEq : EbnfValue.star tupleTail
        (rest.map (EbnfValue.fixedInfixTailValue
          (.symbol .comma) .type)) = viewed.2.2.2.2.1 := by
      rw [restValuesEq]
      exact EbnfValue.star_of_view tupleTail viewed.2.2.2.2.1
    have closeEq := EbnfValue.terminal_of_view
      (.symbol .rightParen) viewed.2.2.2.2.2.1
    let rootRest := rawRest.map fun tail =>
      (EbnfValue.fixedInfixTailView
        (.symbol .comma) .type tail).2
    have resultEq : executeTypeAtomRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness
          (.tuple (first :: second :: rootRest)) := by
      rw [executeTypeAtomRoot, viewEq]
      rfl
    have rootRestEq : rootRest = rest.map Prod.snd := by
      simp [rootRest, rest, List.map_map]
    rw [resultEq, rootRestEq, ← inputEq, ← rawEq]
    simp only [children, EbnfValue.sequenceValuesBuild]
    rw [← openEq, ← firstEq, ← commaEq, ← secondEq,
      ← restEq, ← closeEq]
    exact .typeAtomTuple origin finish openParen first comma second rest
      closeParen witness

private theorem executableMatchArmBody_eq_armBody
    {file : WorkspaceFile} {tokens : List Token}
    (fatArrow : MatchedTerminal file tokens (.symbol .fatArrow))
    (statements : List Statement) :
    executableMatchArmBody file fatArrow statements =
      RuleReduction.armBody fatArrow statements := by
  cases statements <;> rfl

/-- The match-arm executor realizes its exact source-rule reduction. -/
theorem executeMatchArmRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .matchArm origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .matchArm)) :
    RuleReduction file tokens .matchArm origin finish input
      (executeMatchArmRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let pipeAtom : EbnfExpr :=
    .atom (.terminal (.symbol .pipe))
  let patternAtom : EbnfExpr := .atom (.nonterminal .pattern)
  let arrowAtom : EbnfExpr :=
    .atom (.terminal (.symbol .fatArrow))
  let statementAtom : EbnfExpr := .atom (.nonterminal .armStatement)
  let children : List EbnfExpr := [pipeAtom, .list1 patternAtom,
    arrowAtom, .star statementAtom]
  change EbnfValue file tokens (.sequence children) at input
  generalize viewEq : EbnfValue.sequenceFlatView children input = viewed
  rcases viewed with ⟨rawPipe, rawPatterns, rawArrow, rawStatements, ⟨⟩⟩
  let pipe := EbnfValue.terminalView (.symbol .pipe) rawPipe
  let rawPatternValues := EbnfValue.list1View patternAtom rawPatterns
  let patterns := rawPatternValues.map (EbnfValue.ruleView .pattern)
  let arrow := EbnfValue.terminalView (.symbol .fatArrow) rawArrow
  let rawStatementValues := EbnfValue.starView statementAtom rawStatements
  let statements := rawStatementValues.map
    (EbnfValue.ruleView .armStatement)
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  have inputEq := EbnfValue.sequence_of_flat_view children input
  rw [viewEq] at inputEq
  have patternValuesEq :
      patterns.map (EbnfValue.ruleAtom .pattern) = rawPatternValues :=
    ruleNonemptyAtoms_of_views .pattern rawPatternValues
  have rawPatternsEq : EbnfValue.list1 patternAtom
      (patterns.map (EbnfValue.ruleAtom .pattern)) = rawPatterns := by
    rw [patternValuesEq]
    exact EbnfValue.list1_of_view patternAtom rawPatterns
  have statementValuesEq :
      statements.map (EbnfValue.ruleAtom .armStatement) =
        rawStatementValues :=
    ruleAtoms_of_views .armStatement rawStatementValues
  have rawStatementsEq : EbnfValue.star statementAtom
      (statements.map (EbnfValue.ruleAtom .armStatement)) =
        rawStatements := by
    rw [statementValuesEq]
    exact EbnfValue.star_of_view statementAtom rawStatements
  have resultEq : executeMatchArmRoot file tokens origin finish
      ready.1 ready.2.1 input = sourceLoc witness {
        patterns := patterns
        body := RuleReduction.armBody arrow statements
      } := by
    simp [executeMatchArmRoot, children, pipeAtom, patternAtom, arrowAtom,
      statementAtom, viewEq, rawPatternValues, patterns, arrow,
      rawStatementValues, statements, witness,
      executableMatchArmBody_eq_armBody]
  rw [resultEq, ← inputEq]
  simp only [children, EbnfValue.sequenceValuesBuild]
  rw [← EbnfValue.terminal_of_view (.symbol .pipe) rawPipe,
    ← rawPatternsEq,
    ← EbnfValue.terminal_of_view (.symbol .fatArrow) rawArrow,
    ← rawStatementsEq]
  exact .matchArm origin finish pipe patterns arrow statements witness

private theorem patternRuleAtoms_of_views
    {file : WorkspaceFile} {tokens : List Token}
    (inputs : List
      (EbnfValue file tokens (.atom (.nonterminal .pattern)))) :
    (inputs.map (EbnfValue.ruleView .pattern)).map
        (EbnfValue.ruleAtom .pattern) = inputs := by
  induction inputs with
  | nil => rfl
  | cons head tail induction =>
      simp [EbnfValue.rule_of_view, induction]

private theorem patternRuleList1_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens
      (.list1 (.atom (.nonterminal .pattern)))) :
    EbnfValue.list1 (.atom (.nonterminal .pattern))
      ((EbnfValue.list1View (.atom (.nonterminal .pattern)) input).map
        (EbnfValue.ruleView .pattern) |>.map
          (EbnfValue.ruleAtom .pattern)) = input := by
  let viewed := EbnfValue.list1View
    (.atom (.nonterminal .pattern)) input
  have mapEq : (viewed.map (EbnfValue.ruleView .pattern)).map
      (EbnfValue.ruleAtom .pattern) = viewed := by
    cases viewed with
    | mk head tail =>
        simp only [NonemptyList.map, NonemptyList.mk.injEq]
        exact ⟨EbnfValue.rule_of_view .pattern head,
          patternRuleAtoms_of_views tail⟩
  rw [mapEq]
  exact EbnfValue.list1_of_view
    (.atom (.nonterminal .pattern)) input

private theorem patternTupleStar_of_view
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens (.star
      (EbnfValue.fixedInfixTailExpr (.symbol .comma) .pattern))) :
    EbnfValue.star
      (EbnfValue.fixedInfixTailExpr (.symbol .comma) .pattern)
      (((EbnfValue.starView
        (EbnfValue.fixedInfixTailExpr (.symbol .comma) .pattern) input).map
          (EbnfValue.fixedInfixTailView (.symbol .comma) .pattern)).map
        (EbnfValue.fixedInfixTailValue (.symbol .comma) .pattern)) = input := by
  let rawRest := EbnfValue.starView
    (EbnfValue.fixedInfixTailExpr (.symbol .comma) .pattern) input
  have mapEq : ((rawRest.map (EbnfValue.fixedInfixTailView
      (.symbol .comma) .pattern)).map (EbnfValue.fixedInfixTailValue
        (.symbol .comma) .pattern)) = rawRest := by
    induction rawRest with
    | nil => rfl
    | cons head tail induction =>
        simp only [List.map_cons, List.cons.injEq]
        exact ⟨EbnfValue.fixedInfixTailValue_of_view
          (.symbol .comma) .pattern head, induction⟩
  rw [mapEq]
  exact EbnfValue.star_of_view
    (EbnfValue.fixedInfixTailExpr (.symbol .comma) .pattern) input

/-- The pattern executor realizes its exact source-rule reduction. -/
theorem executePatternRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .pattern origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .pattern)) :
    RuleReduction file tokens .pattern origin finish input
      (executePatternRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let underscoreAtom : EbnfExpr :=
    .atom (.terminal (.symbol .underscore))
  let literalAtom : EbnfExpr := .atom (.nonterminal .literal)
  let dotAtom : EbnfExpr := .atom (.terminal (.symbol .dot))
  let identifierAtom : EbnfExpr :=
    .atom (.terminal (.category .identifier))
  let comptimeAtom : EbnfExpr :=
    .atom (.terminal (.contextualKeyword .comptimeKw))
  let expressionAtom : EbnfExpr := .atom (.nonterminal .expression)
  let nameAtom : EbnfExpr := .atom (.nonterminal .qualifiedName)
  let openAtom : EbnfExpr := .atom (.terminal (.symbol .leftParen))
  let closeAtom : EbnfExpr := .atom (.terminal (.symbol .rightParen))
  let commaAtom : EbnfExpr := .atom (.terminal (.symbol .comma))
  let patternAtom : EbnfExpr := .atom (.nonterminal .pattern)
  let argumentsExpr : EbnfExpr :=
    .sequence [openAtom, .list1 patternAtom, closeAtom]
  let tupleTail := EbnfValue.fixedInfixTailExpr
    (.symbol .comma) .pattern
  let branches : List EbnfExpr := [underscoreAtom, literalAtom,
    .sequence [dotAtom, identifierAtom, .optional argumentsExpr],
    .sequence [comptimeAtom, expressionAtom],
    .sequence [nameAtom, .optional argumentsExpr],
    .sequence [openAtom, closeAtom],
    .sequence [openAtom, patternAtom, closeAtom],
    .sequence [openAtom, patternAtom, commaAtom, patternAtom,
      .star tupleTail, closeAtom]]
  change EbnfValue file tokens (.choice branches) at input
  generalize viewEq : EbnfValue.choiceView branches input = viewed
  rcases viewed with ⟨branch, raw⟩
  have inputEq := EbnfValue.choice_of_view branches input
  rw [viewEq] at inputEq
  have branchCases : branch = 0 ∨ branch = 1 ∨ branch = 2 ∨
      branch = 3 ∨ branch = 4 ∨ branch = 5 ∨ branch = 6 ∨
      branch = 7 := by
    have lengthEq : branches.length = 8 := by rfl
    have bound : branch.val < 8 := by simpa [lengthEq] using branch.isLt
    have cases : branch.val = 0 ∨ branch.val = 1 ∨ branch.val = 2 ∨
        branch.val = 3 ∨ branch.val = 4 ∨ branch.val = 5 ∨
        branch.val = 6 ∨ branch.val = 7 := by omega
    rcases cases with h | h | h | h | h | h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h)))))))
  let witness := ConsumedSpanWitness.compute file tokens origin finish ready.1 ready.2.1
  rcases branchCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · let underscore := EbnfValue.terminalView (.symbol .underscore) raw
    have underscoreEq := EbnfValue.terminal_of_view (.symbol .underscore) raw
    have resultEq : executePatternRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness
          (.wildcard (RuleReduction.terminalLoc underscore .wildcard)) := by
      rw [executePatternRoot, viewEq]; rfl
    rw [resultEq, ← inputEq, ← underscoreEq]
    exact .patternWildcard origin finish underscore witness
  · let literal := EbnfValue.ruleView .literal raw
    have literalEq := EbnfValue.rule_of_view .literal raw
    have resultEq : executePatternRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness (.literal literal) := by
      rw [executePatternRoot, viewEq]; rfl
    rw [resultEq, ← inputEq, ← literalEq]
    exact .patternLiteral origin finish literal witness
  · let viewed := EbnfValue.sequence3View dotAtom identifierAtom (.optional argumentsExpr) raw
    let dot := EbnfValue.terminalView (.symbol .dot) viewed.1
    let name := EbnfValue.terminalView (.category .identifier) viewed.2.1
    let rootArguments := (EbnfValue.optionalView argumentsExpr
      viewed.2.2).map fun argumentRaw =>
        let argumentView := EbnfValue.sequence3View
          openAtom (.list1 patternAtom) closeAtom argumentRaw
        (EbnfValue.list1View patternAtom argumentView.2.1).map
          (EbnfValue.ruleView .pattern)
    have rawEq := EbnfValue.sequence3_of_view dotAtom identifierAtom (.optional argumentsExpr) raw
    have dotEq := EbnfValue.terminal_of_view (.symbol .dot) viewed.1
    have nameEq := EbnfValue.terminal_of_view (.category .identifier) viewed.2.1
    have rootResultEq : executePatternRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness (.dotConstructor
          (RuleReduction.terminalLoc dot ())
          (RuleReduction.terminalLoc name name.identifierProjection.2)
          rootArguments) := by
      rw [executePatternRoot, viewEq]; rfl
    generalize optionalEq : EbnfValue.optionalView argumentsExpr
      viewed.2.2 = selected
    cases selected with
    | none =>
        have selectedEq : EbnfValue.optional argumentsExpr none =
            viewed.2.2 := by
          calc
            _ = EbnfValue.optional argumentsExpr
                (EbnfValue.optionalView argumentsExpr viewed.2.2) := by
              rw [optionalEq]
            _ = viewed.2.2 :=
              EbnfValue.optional_of_view argumentsExpr viewed.2.2
        have rootArgumentsEq : rootArguments = none := by
          simp [rootArguments, optionalEq]
        rw [rootResultEq, rootArgumentsEq, ← inputEq, ← rawEq,
          ← dotEq, ← nameEq, ← selectedEq]
        exact .patternDotConstructorWithoutArguments origin finish dot name
          name.identifierProjection.1 name.identifierProjection.2
          name.identifierProjection_projects witness
    | some argumentRaw =>
        let argumentView := EbnfValue.sequence3View
          openAtom (.list1 patternAtom) closeAtom argumentRaw
        let openParen := EbnfValue.terminalView
          (.symbol .leftParen) argumentView.1
        let arguments := (EbnfValue.list1View
          patternAtom argumentView.2.1).map (EbnfValue.ruleView .pattern)
        let closeParen := EbnfValue.terminalView
          (.symbol .rightParen) argumentView.2.2
        have selectedEq : EbnfValue.optional argumentsExpr
            (some argumentRaw) = viewed.2.2 := by
          calc
            _ = EbnfValue.optional argumentsExpr
                (EbnfValue.optionalView argumentsExpr viewed.2.2) := by
              rw [optionalEq]
            _ = viewed.2.2 :=
              EbnfValue.optional_of_view argumentsExpr viewed.2.2
        have argumentEq := EbnfValue.sequence3_of_view
          openAtom (.list1 patternAtom) closeAtom argumentRaw
        have openEq := EbnfValue.terminal_of_view
          (.symbol .leftParen) argumentView.1
        have argumentsEq : EbnfValue.list1 patternAtom
            (arguments.map (EbnfValue.ruleAtom .pattern)) =
              argumentView.2.1 :=
          patternRuleList1_of_view argumentView.2.1
        have closeEq := EbnfValue.terminal_of_view
          (.symbol .rightParen) argumentView.2.2
        have rootArgumentsEq : rootArguments = some arguments := by
          simp [rootArguments, optionalEq, arguments, argumentView,
            openAtom, closeAtom]
        rw [rootResultEq, rootArgumentsEq, ← inputEq, ← rawEq,
          ← dotEq, ← nameEq, ← selectedEq, ← argumentEq, ← openEq,
          ← argumentsEq, ← closeEq]
        exact .patternDotConstructorWithArguments origin finish dot name
          name.identifierProjection.1 name.identifierProjection.2
          name.identifierProjection_projects openParen arguments closeParen
          witness
  · let viewed := EbnfValue.sequence2View comptimeAtom expressionAtom raw
    let comptime := EbnfValue.terminalView (.contextualKeyword .comptimeKw) viewed.1
    let expression := EbnfValue.ruleView .expression viewed.2
    have rawEq := EbnfValue.sequence2_of_view comptimeAtom expressionAtom raw
    have comptimeEq := EbnfValue.terminal_of_view (.contextualKeyword .comptimeKw) viewed.1
    have expressionEq := EbnfValue.rule_of_view .expression viewed.2
    have resultEq : executePatternRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness (.comptime
          (RuleReduction.terminalLoc comptime .comptimeModifier)
          expression) := by
      rw [executePatternRoot, viewEq]; rfl
    rw [resultEq, ← inputEq, ← rawEq, ← comptimeEq, ← expressionEq]
    exact .patternComptime origin finish comptime expression witness
  · let viewed := EbnfValue.sequence2View
      nameAtom (.optional argumentsExpr) raw
    let name := EbnfValue.ruleView .qualifiedName viewed.1
    let rootArguments := (EbnfValue.optionalView argumentsExpr
      viewed.2).map fun argumentRaw =>
        let argumentView := EbnfValue.sequence3View
          openAtom (.list1 patternAtom) closeAtom argumentRaw
        (EbnfValue.list1View patternAtom argumentView.2.1).map
          (EbnfValue.ruleView .pattern)
    have rawEq := EbnfValue.sequence2_of_view
      nameAtom (.optional argumentsExpr) raw
    have nameEq := EbnfValue.rule_of_view .qualifiedName viewed.1
    have rootResultEq : executePatternRoot file tokens origin finish
        ready.1 ready.2.1 input =
          sourceLoc witness (.named name rootArguments) := by
      rw [executePatternRoot, viewEq]; rfl
    generalize optionalEq : EbnfValue.optionalView argumentsExpr
      viewed.2 = selected
    cases selected with
    | none =>
        have selectedEq : EbnfValue.optional argumentsExpr none = viewed.2 := by
          calc
            _ = EbnfValue.optional argumentsExpr
                (EbnfValue.optionalView argumentsExpr viewed.2) := by
              rw [optionalEq]
            _ = viewed.2 := EbnfValue.optional_of_view argumentsExpr viewed.2
        have rootArgumentsEq : rootArguments = none := by
          simp [rootArguments, optionalEq]
        rw [rootResultEq, rootArgumentsEq, ← inputEq, ← rawEq,
          ← nameEq, ← selectedEq]
        exact .patternNamedWithoutArguments origin finish name witness
    | some argumentRaw =>
        let argumentView := EbnfValue.sequence3View
          openAtom (.list1 patternAtom) closeAtom argumentRaw
        let openParen := EbnfValue.terminalView
          (.symbol .leftParen) argumentView.1
        let arguments := (EbnfValue.list1View
          patternAtom argumentView.2.1).map (EbnfValue.ruleView .pattern)
        let closeParen := EbnfValue.terminalView
          (.symbol .rightParen) argumentView.2.2
        have selectedEq : EbnfValue.optional argumentsExpr
            (some argumentRaw) = viewed.2 := by
          calc
            _ = EbnfValue.optional argumentsExpr
                (EbnfValue.optionalView argumentsExpr viewed.2) := by
              rw [optionalEq]
            _ = viewed.2 := EbnfValue.optional_of_view argumentsExpr viewed.2
        have argumentEq := EbnfValue.sequence3_of_view
          openAtom (.list1 patternAtom) closeAtom argumentRaw
        have openEq := EbnfValue.terminal_of_view
          (.symbol .leftParen) argumentView.1
        have argumentsEq : EbnfValue.list1 patternAtom
            (arguments.map (EbnfValue.ruleAtom .pattern)) =
              argumentView.2.1 :=
          patternRuleList1_of_view argumentView.2.1
        have closeEq := EbnfValue.terminal_of_view
          (.symbol .rightParen) argumentView.2.2
        have rootArgumentsEq : rootArguments = some arguments := by
          simp [rootArguments, optionalEq, arguments, argumentView,
            openAtom, closeAtom]
        rw [rootResultEq, rootArgumentsEq, ← inputEq, ← rawEq,
          ← nameEq, ← selectedEq, ← argumentEq, ← openEq,
          ← argumentsEq, ← closeEq]
        exact .patternNamedWithArguments origin finish name openParen
          arguments closeParen witness
  · let viewed := EbnfValue.sequence2View openAtom closeAtom raw
    let openParen := EbnfValue.terminalView (.symbol .leftParen) viewed.1
    let closeParen := EbnfValue.terminalView (.symbol .rightParen) viewed.2
    have rawEq := EbnfValue.sequence2_of_view openAtom closeAtom raw
    have openEq := EbnfValue.terminal_of_view (.symbol .leftParen) viewed.1
    have closeEq := EbnfValue.terminal_of_view (.symbol .rightParen) viewed.2
    have resultEq : executePatternRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness (.tuple []) := by
      rw [executePatternRoot, viewEq]; rfl
    rw [resultEq, ← inputEq, ← rawEq, ← openEq, ← closeEq]
    exact .patternEmptyTuple origin finish openParen closeParen witness
  · let viewed := EbnfValue.sequence3View
      openAtom patternAtom closeAtom raw
    let openParen := EbnfValue.terminalView (.symbol .leftParen) viewed.1
    let inner := EbnfValue.ruleView .pattern viewed.2.1
    let closeParen := EbnfValue.terminalView
      (.symbol .rightParen) viewed.2.2
    have rawEq := EbnfValue.sequence3_of_view
      openAtom patternAtom closeAtom raw
    have openEq := EbnfValue.terminal_of_view (.symbol .leftParen) viewed.1
    have innerEq := EbnfValue.rule_of_view .pattern viewed.2.1
    have closeEq := EbnfValue.terminal_of_view
      (.symbol .rightParen) viewed.2.2
    have resultEq : executePatternRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness (.group inner) := by
      rw [executePatternRoot, viewEq]; rfl
    rw [resultEq, ← inputEq, ← rawEq, ← openEq, ← innerEq, ← closeEq]
    exact .patternGroup origin finish openParen inner closeParen witness
  · let children : List EbnfExpr := [openAtom, patternAtom, commaAtom,
      patternAtom, .star tupleTail, closeAtom]
    let viewed := EbnfValue.sequenceFlatView children raw
    let openParen := EbnfValue.terminalView (.symbol .leftParen) viewed.1
    let first := EbnfValue.ruleView .pattern viewed.2.1
    let comma := EbnfValue.terminalView (.symbol .comma) viewed.2.2.1
    let second := EbnfValue.ruleView .pattern viewed.2.2.2.1
    let rawRest := EbnfValue.starView tupleTail viewed.2.2.2.2.1
    let rest := rawRest.map (EbnfValue.fixedInfixTailView
      (.symbol .comma) .pattern)
    let closeParen := EbnfValue.terminalView
      (.symbol .rightParen) viewed.2.2.2.2.2.1
    have rawEq := EbnfValue.sequence_of_flat_view children raw
    have openEq := EbnfValue.terminal_of_view (.symbol .leftParen) viewed.1
    have firstEq := EbnfValue.rule_of_view .pattern viewed.2.1
    have commaEq := EbnfValue.terminal_of_view
      (.symbol .comma) viewed.2.2.1
    have secondEq := EbnfValue.rule_of_view .pattern viewed.2.2.2.1
    have restEq : EbnfValue.star tupleTail
        (rest.map (EbnfValue.fixedInfixTailValue
          (.symbol .comma) .pattern)) = viewed.2.2.2.2.1 := by
      exact patternTupleStar_of_view viewed.2.2.2.2.1
    have closeEq := EbnfValue.terminal_of_view
      (.symbol .rightParen) viewed.2.2.2.2.2.1
    let rootRest := rawRest.map fun tail =>
      (EbnfValue.fixedInfixTailView
        (.symbol .comma) .pattern tail).2
    have resultEq : executePatternRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness
          (.tuple (first :: second :: rootRest)) := by
      rw [executePatternRoot, viewEq]; rfl
    have rootRestEq : rootRest = rest.map Prod.snd := by
      simp [rootRest, rest, List.map_map]
    rw [resultEq, rootRestEq, ← inputEq, ← rawEq]
    simp only [children, EbnfValue.sequenceValuesBuild]
    rw [← openEq, ← firstEq, ← commaEq, ← secondEq,
      ← restEq, ← closeEq]
    exact .patternTuple origin finish openParen first comma second rest
      closeParen witness

/-- Align one dotted module path tail with its parsed path component. -/
private def moduleRefTailData
    {file : WorkspaceFile} {tokens : List Token}
    (pair : MatchedTerminal file tokens (.symbol .dot) ×
      MatchedTerminal file tokens (.category .pathComponent)) :
    MatchedTerminal file tokens (.symbol .dot) ×
      RuleReduction.SpelledTerminalData file tokens
        (.category .pathComponent) PathSegment :=
  (pair.1, {
    matched := pair.2
    spelling := pair.2.pathProjection.1
    parsed := pair.2.pathProjection.2
  })

private theorem moduleRefTailData_values
    {file : WorkspaceFile} {tokens : List Token}
    (values : List (EbnfValue file tokens
      (EbnfValue.terminalPairTailExpr
        (.symbol .dot) (.category .pathComponent)))) :
    ((values.map (EbnfValue.terminalPairTailView
      (.symbol .dot) (.category .pathComponent))).map
        moduleRefTailData).map (fun entry =>
      EbnfValue.terminalPairTailValue
        (.symbol .dot) (.category .pathComponent)
        (entry.1, entry.2.matched)) = values := by
  induction values with
  | nil => rfl
  | cons head rest induction =>
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · simp only [moduleRefTailData]
        exact EbnfValue.terminalPairTailValue_of_view
          (.symbol .dot) (.category .pathComponent) head
      · exact induction

private theorem moduleRefTailData_projects
    {file : WorkspaceFile} {tokens : List Token}
    (values : List (EbnfValue file tokens
      (EbnfValue.terminalPairTailExpr
        (.symbol .dot) (.category .pathComponent))))
    (entry : MatchedTerminal file tokens (.symbol .dot) ×
      RuleReduction.SpelledTerminalData file tokens
        (.category .pathComponent) PathSegment)
    (member : entry ∈ (values.map (EbnfValue.terminalPairTailView
      (.symbol .dot) (.category .pathComponent))).map
        moduleRefTailData) :
    PathSegmentProjects entry.2.matched
      entry.2.spelling entry.2.parsed := by
  simp only [List.mem_map] at member
  rcases member with ⟨pair, _pairMember, rfl⟩
  exact pair.2.pathProjection_projects

/-- The module-reference executor realizes its exact root reduction. -/
theorem executeModuleRefRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .moduleRef origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .moduleRef)) :
    RuleReduction file tokens .moduleRef origin finish input
      (executeModuleRefRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let pathAtom : EbnfExpr :=
    .atom (.terminal (.category .pathComponent))
  let tail := EbnfValue.terminalPairTailExpr
    (.symbol .dot) (.category .pathComponent)
  let externalChildren : List EbnfExpr := [
    .atom (.terminal (.symbol .at)), pathAtom,
    .atom (.terminal (.symbol .dot)), pathAtom, .star tail]
  let localChildren : List EbnfExpr := [pathAtom, .star tail]
  change EbnfValue file tokens
    (.choice [.sequence externalChildren, .sequence localChildren]) at input
  generalize viewEq : EbnfValue.choice2View
    (.sequence externalChildren) (.sequence localChildren) input = viewed
  have normalizedViewEq := viewEq
  simp only [externalChildren, localChildren, pathAtom, tail] at normalizedViewEq
  have inputEq := EbnfValue.choice2_of_view
    (.sequence externalChildren) (.sequence localChildren) input
  rw [viewEq] at inputEq
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  rcases viewed with raw | raw
  · let viewed := EbnfValue.sequenceFlatView externalChildren raw
    change EbnfValue.choice
      [.sequence externalChildren, .sequence localChildren]
        ⟨0, raw⟩ = input at inputEq
    let rawAt := viewed.1
    let rawLibrary := viewed.2.1
    let rawDot := viewed.2.2.1
    let rawNext := viewed.2.2.2.1
    let rawStar := viewed.2.2.2.2.1
    have rawEq := EbnfValue.sequence_of_flat_view externalChildren raw
    have rawEq' : EbnfValue.sequence externalChildren
        (EbnfValue.sequenceValuesBuild externalChildren
          ⟨rawAt, rawLibrary, rawDot, rawNext, rawStar, ⟨⟩⟩) = raw :=
      rawEq
    let atToken := EbnfValue.terminalView (.symbol .at) rawAt
    let library := EbnfValue.terminalView
      (.category .pathComponent) rawLibrary
    let dot := EbnfValue.terminalView (.symbol .dot) rawDot
    let next := EbnfValue.terminalView
      (.category .pathComponent) rawNext
    let rawRest := EbnfValue.starView tail rawStar
    let libraryData : RuleReduction.SpelledTerminalData file tokens
        (.category .pathComponent) ExternalLibraryName := {
      matched := library
      spelling := library.pathProjection.1
      parsed := { segment := library.pathProjection.2 }
    }
    let nextData : RuleReduction.SpelledTerminalData file tokens
        (.category .pathComponent) PathSegment := {
      matched := next
      spelling := next.pathProjection.1
      parsed := next.pathProjection.2
    }
    let rest := rawRest.map (EbnfValue.terminalPairTailView
      (.symbol .dot) (.category .pathComponent))
    let restData := rest.map moduleRefTailData
    have restValuesEq := moduleRefTailData_values rawRest
    have restEq : EbnfValue.star tail
        (restData.map fun entry =>
          EbnfValue.terminalPairTailValue
            (.symbol .dot) (.category .pathComponent)
            (entry.1, entry.2.matched)) = rawStar := by
      rw [restValuesEq]
      exact EbnfValue.star_of_view tail rawStar
    have libraryProjects : ExternalLibraryProjects libraryData.matched
        libraryData.spelling libraryData.parsed := by
      rcases library.pathProjection_projects with
        ⟨token, valueEq, shape, parseEq⟩
      refine ⟨token, valueEq, shape, ?_⟩
      change (PathSegment.parse library.pathProjection.1).map
        (fun segment => ({ segment } : ExternalLibraryName)) =
          some { segment := library.pathProjection.2 }
      rw [parseEq]
      rfl
    have nextProjects : PathSegmentProjects nextData.matched
        nextData.spelling nextData.parsed :=
      next.pathProjection_projects
    have restProjects : ∀ entry, entry ∈ restData →
        PathSegmentProjects entry.2.matched
          entry.2.spelling entry.2.parsed :=
      moduleRefTailData_projects rawRest
    have resultEq : executeModuleRefRoot file tokens origin finish
        ready.1 ready.2.1 input = sourceLoc witness (.external
          (RuleReduction.terminalLoc atToken .externalSigil)
          (RuleReduction.terminalLoc libraryData.matched libraryData.parsed)
          {
            head := RuleReduction.terminalLoc nextData.matched nextData.parsed
            tail := restData.map fun entry =>
              RuleReduction.terminalLoc entry.2.matched entry.2.parsed
          }) := by
      simp [executeModuleRefRoot, normalizedViewEq, restData,
        moduleRefTailData, rest, libraryData,
        nextData, atToken, library, next, rawRest, rawAt, rawLibrary,
        rawNext, rawStar, viewed, externalChildren, localChildren, pathAtom,
        tail, witness, List.map_map, Function.comp_def,
        executableTerminalLoc, RuleReduction.terminalLoc]
    rw [resultEq, ← inputEq, ← rawEq',
      ← EbnfValue.terminal_of_view (.symbol .at) rawAt,
      ← EbnfValue.terminal_of_view (.category .pathComponent) rawLibrary,
      ← EbnfValue.terminal_of_view (.symbol .dot) rawDot,
      ← EbnfValue.terminal_of_view (.category .pathComponent) rawNext,
      ← restEq]
    exact .moduleRefExternal origin finish atToken libraryData dot nextData
      restData (.externalSigil atToken) libraryProjects nextProjects
      restProjects witness
  · let viewed := EbnfValue.sequence2View pathAtom (.star tail) raw
    change EbnfValue.choice
      [.sequence externalChildren, .sequence localChildren]
        ⟨1, raw⟩ = input at inputEq
    let rawFirst := viewed.1
    let rawStar := viewed.2
    have rawEq := EbnfValue.sequence2_of_view pathAtom (.star tail) raw
    have rawEq' : EbnfValue.sequence [pathAtom, .star tail]
        (EbnfValues.cons pathAtom [.star tail] rawFirst
          (EbnfValues.cons (.star tail) [] rawStar EbnfValues.nil)) = raw :=
      rawEq
    let first := EbnfValue.terminalView
      (.category .pathComponent) rawFirst
    let rawRest := EbnfValue.starView tail rawStar
    let rest := rawRest.map (EbnfValue.terminalPairTailView
      (.symbol .dot) (.category .pathComponent))
    let firstData : RuleReduction.SpelledTerminalData file tokens
        (.category .pathComponent) PathSegment := {
      matched := first
      spelling := first.pathProjection.1
      parsed := first.pathProjection.2
    }
    let restData := rest.map moduleRefTailData
    have restValuesEq := moduleRefTailData_values rawRest
    have restEq : EbnfValue.star tail
        (restData.map fun entry =>
          EbnfValue.terminalPairTailValue
            (.symbol .dot) (.category .pathComponent)
            (entry.1, entry.2.matched)) = rawStar := by
      rw [restValuesEq]
      exact EbnfValue.star_of_view tail rawStar
    have firstProjects : PathSegmentProjects firstData.matched
        firstData.spelling firstData.parsed :=
      first.pathProjection_projects
    have restProjects : ∀ entry, entry ∈ restData →
        PathSegmentProjects entry.2.matched
          entry.2.spelling entry.2.parsed :=
      moduleRefTailData_projects rawRest
    by_cases standardEq : firstData.spelling = "std"
    · have standardProjectionEq : first.pathProjection.1 = "std" :=
        standardEq
      let marker : RuleReduction.MarkerProjects file tokens
          firstData.matched .standardRoot :=
        .standardRoot firstData.matched firstData.parsed (by
          simpa [standardEq] using firstProjects)
      have resultEq : executeModuleRefRoot file tokens origin finish
          ready.1 ready.2.1 input = sourceLoc witness (.standard
            (RuleReduction.terminalLoc firstData.matched .standardRoot)
            (restData.map fun entry => RuleReduction.terminalLoc
              entry.2.matched entry.2.parsed)) := by
        simp [executeModuleRefRoot, normalizedViewEq, standardProjectionEq, firstData,
          restData, moduleRefTailData, rest, first, rawRest,
          rawFirst, rawStar, viewed, witness,
          externalChildren, localChildren, pathAtom, tail, List.map_map,
          Function.comp_def,
          executableTerminalLoc, RuleReduction.terminalLoc]
      rw [resultEq, ← inputEq, ← rawEq',
        ← EbnfValue.terminal_of_view
          (.category .pathComponent) rawFirst, ← restEq]
      exact .moduleRefStandard origin finish firstData.matched restData
        marker restProjects witness
    · have standardProjectionNe : first.pathProjection.1 ≠ "std" :=
        standardEq
      by_cases libraryEq : firstData.spelling = "lib"
      · have libraryProjectionEq : first.pathProjection.1 = "lib" :=
          libraryEq
        let marker : RuleReduction.MarkerProjects file tokens
            firstData.matched .libraryRoot :=
          .libraryRoot firstData.matched firstData.parsed (by
            simpa [libraryEq] using firstProjects)
        generalize restCaseEq : rest = selectedRest
        cases selectedRest with
        | nil =>
            have normalizedRestCaseEq := restCaseEq
            simp only [rest, rawRest, rawStar, viewed, pathAtom, tail] at normalizedRestCaseEq
            have restDataEq : restData = [] := by
              simp [restData, restCaseEq]
            rw [restDataEq] at restEq
            have resultEq : executeModuleRefRoot file tokens origin finish
                ready.1 ready.2.1 input = sourceLoc witness (.relative {
                  head := RuleReduction.terminalLoc
                    firstData.matched firstData.parsed
                  tail := []
                }) := by
              simp [executeModuleRefRoot, normalizedViewEq,
                libraryProjectionEq, normalizedRestCaseEq,
                firstData, first, rawFirst, viewed,
                externalChildren, localChildren, pathAtom, tail, witness,
                executableTerminalLoc,
                RuleReduction.terminalLoc]
            rw [resultEq, ← inputEq, ← rawEq',
              ← EbnfValue.terminal_of_view
                (.category .pathComponent) rawFirst, ← restEq]
            exact .moduleRefRelativeLibraryEmpty origin finish firstData
              firstProjects marker witness
        | cons next remaining =>
            have normalizedRestCaseEq := restCaseEq
            simp only [rest, rawRest, rawStar, viewed, pathAtom, tail] at normalizedRestCaseEq
            let nextData : RuleReduction.SpelledTerminalData file tokens
                (.category .pathComponent) PathSegment := {
              matched := next.2
              spelling := next.2.pathProjection.1
              parsed := next.2.pathProjection.2
            }
            let remainingData : List
                (MatchedTerminal file tokens (.symbol .dot) ×
                  RuleReduction.SpelledTerminalData file tokens
                    (.category .pathComponent) PathSegment) :=
              remaining.map fun entry => (entry.1, {
                matched := entry.2
                spelling := entry.2.pathProjection.1
                parsed := entry.2.pathProjection.2
              })
            have restDataEq : restData =
                (next.1, nextData) :: remainingData := by
              simp [restData, moduleRefTailData, restCaseEq,
                nextData, remainingData]
            rw [restDataEq] at restEq
            have nextProjects : PathSegmentProjects nextData.matched
                nextData.spelling nextData.parsed :=
              next.2.pathProjection_projects
            have remainingProjects : ∀ entry, entry ∈ remainingData →
                PathSegmentProjects entry.2.matched
                  entry.2.spelling entry.2.parsed := by
              intro entry member
              simp only [remainingData, List.mem_map] at member
              rcases member with ⟨entry, _entryMember, rfl⟩
              exact entry.2.pathProjection_projects
            have resultEq : executeModuleRefRoot file tokens origin finish
                ready.1 ready.2.1 input = sourceLoc witness (.libraryRoot
                  (RuleReduction.terminalLoc firstData.matched .libraryRoot) {
                    head := RuleReduction.terminalLoc
                      nextData.matched nextData.parsed
                    tail := remainingData.map fun entry =>
                      RuleReduction.terminalLoc
                        entry.2.matched entry.2.parsed
                  }) := by
              simp [executeModuleRefRoot, normalizedViewEq,
                libraryProjectionEq, normalizedRestCaseEq,
                firstData, nextData, remainingData, first,
                rawFirst, viewed, externalChildren,
                localChildren, pathAtom, tail, witness,
                List.map_map, Function.comp_def, executableTerminalLoc,
                RuleReduction.terminalLoc]
            rw [resultEq, ← inputEq, ← rawEq',
              ← EbnfValue.terminal_of_view
                (.category .pathComponent) rawFirst, ← restEq]
            exact .moduleRefLibraryRoot origin finish firstData.matched
              next.1 nextData remainingData marker nextProjects
              remainingProjects witness
      · have libraryProjectionNe : first.pathProjection.1 ≠ "lib" :=
          libraryEq
        have resultEq : executeModuleRefRoot file tokens origin finish
            ready.1 ready.2.1 input = sourceLoc witness (.relative {
              head := RuleReduction.terminalLoc
                firstData.matched firstData.parsed
              tail := restData.map fun entry => RuleReduction.terminalLoc
                entry.2.matched entry.2.parsed
            }) := by
          simp [executeModuleRefRoot, normalizedViewEq,
            standardProjectionNe, libraryProjectionNe,
            firstData, restData, rest, first, rawRest, rawFirst, rawStar,
            moduleRefTailData, viewed, externalChildren, localChildren,
            pathAtom, tail, witness,
            List.map_map,
            Function.comp_def, executableTerminalLoc,
            RuleReduction.terminalLoc]
        rw [resultEq, ← inputEq, ← rawEq',
          ← EbnfValue.terminal_of_view
            (.category .pathComponent) rawFirst, ← restEq]
        exact .moduleRefRelativeOther origin finish firstData restData
          firstProjects restProjects standardEq libraryEq witness

/-- The class-declaration executor realizes its exact root reduction. -/
theorem executeClassDeclRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .classDecl origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .classDecl)) :
    RuleReduction file tokens .classDecl origin finish input
      (executeClassDeclRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let genericAtom : EbnfExpr := .atom (.nonterminal .genericPrefix)
  let classAtom : EbnfExpr :=
    .atom (.terminal (.hardKeyword .classKw))
  let typeAtom : EbnfExpr := .atom (.nonterminal .typeAtom)
  let colonAtom : EbnfExpr := .atom (.terminal (.symbol .colon))
  let nameAtom : EbnfExpr := .atom (.terminal (.category .identifier))
  let parameterChild := EbnfValue.typeArgumentsExpr
  let openAtom : EbnfExpr := .atom (.terminal (.symbol .leftBrace))
  let methodAtom : EbnfExpr := .atom (.nonterminal .classMethod)
  let closeAtom : EbnfExpr := .atom (.terminal (.symbol .rightBrace))
  let children : List EbnfExpr := [.optional genericAtom, classAtom,
    typeAtom, colonAtom, nameAtom, .optional parameterChild, openAtom,
    .star methodAtom, closeAtom]
  change EbnfValue file tokens (.sequence children) at input
  generalize sequenceEq : EbnfValue.sequenceFlatView children input = values
  rcases values with ⟨rawGeneric, rawClass, rawMain, rawColon, rawName,
    rawParameters, rawOpen, rawMethods, rawClose, ⟨⟩⟩
  have inputEq := EbnfValue.sequence_of_flat_view children input
  rw [sequenceEq] at inputEq
  let rawGenericValue := EbnfValue.optionalView genericAtom rawGeneric
  let genericPrefix := rawGenericValue.map
    (EbnfValue.ruleView .genericPrefix)
  let classKw := EbnfValue.terminalView
    (.hardKeyword .classKw) rawClass
  let main := EbnfValue.ruleView .typeAtom rawMain
  let colon := EbnfValue.terminalView (.symbol .colon) rawColon
  let name := EbnfValue.terminalView (.category .identifier) rawName
  let nameData : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier := {
    matched := name
    spelling := name.identifierProjection.1
    parsed := name.identifierProjection.2
  }
  let rawParameterValue := EbnfValue.optionalView
    parameterChild rawParameters
  let parameterData := rawParameterValue.map EbnfValue.typeArgumentsView
  let openBrace := EbnfValue.terminalView (.symbol .leftBrace) rawOpen
  let rawMethodValues := EbnfValue.starView methodAtom rawMethods
  let methods := rawMethodValues.map (EbnfValue.ruleView .classMethod)
  let closeBrace := EbnfValue.terminalView
    (.symbol .rightBrace) rawClose
  have genericValuesEq : genericPrefix.map
      (EbnfValue.ruleAtom .genericPrefix) = rawGenericValue := by
    cases selected : rawGenericValue with
    | none => simp [genericPrefix, selected]
    | some raw =>
        simp [genericPrefix, selected, EbnfValue.rule_of_view]
  have genericEq : EbnfValue.optional genericAtom
      (genericPrefix.map (EbnfValue.ruleAtom .genericPrefix)) =
        rawGeneric := by
    rw [genericValuesEq]
    exact EbnfValue.optional_of_view genericAtom rawGeneric
  have parameterValuesEq : parameterData.map
      EbnfValue.typeArgumentsValue = rawParameterValue := by
    cases selected : rawParameterValue with
    | none => simp [parameterData, selected]
    | some raw =>
        simp [parameterData, selected,
          EbnfValue.typeArgumentsValue_of_view]
  have parametersEq : EbnfValue.optional parameterChild
      (parameterData.map EbnfValue.typeArgumentsValue) = rawParameters := by
    rw [parameterValuesEq]
    exact EbnfValue.optional_of_view parameterChild rawParameters
  have methodsValuesEq : methods.map
      (EbnfValue.ruleAtom .classMethod) = rawMethodValues :=
    ruleAtoms_of_views .classMethod rawMethodValues
  have methodsEq : EbnfValue.star methodAtom
      (methods.map (EbnfValue.ruleAtom .classMethod)) = rawMethods := by
    rw [methodsValuesEq]
    exact EbnfValue.star_of_view methodAtom rawMethods
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  let parameterInput :
      (MatchedTerminal file tokens (.symbol .leftParen) ×
        (NonemptyList TypeExpr ×
          (MatchedTerminal file tokens (.symbol .rightParen) × Unit))) →
        EbnfValue file tokens EbnfValue.typeArgumentsExpr := fun value =>
    EbnfValue.sequence [
      .atom (.terminal (.symbol .leftParen)),
      .list1 (.atom (.nonterminal .type)),
      .atom (.terminal (.symbol .rightParen))]
      (EbnfValues.cons _ _
        (EbnfValue.terminalAtom (.symbol .leftParen) value.1)
        (EbnfValues.cons _ _
          (EbnfValue.list1 _
            (value.2.1.map (EbnfValue.ruleAtom .type)))
          (EbnfValues.cons _ _
            (EbnfValue.terminalAtom
              (.symbol .rightParen) value.2.2.1)
            EbnfValues.nil)))
  have parameterInputEq : parameterInput =
      @EbnfValue.typeArgumentsValue file tokens := by
    funext value
    rfl
  have constructorParametersEq : EbnfValue.optional parameterChild
      (parameterData.map parameterInput) = rawParameters := by
    rw [parameterInputEq]
    exact parametersEq
  let rebuilt : EbnfValue file tokens (.sequence children) :=
    EbnfValue.sequence children
      (EbnfValue.sequenceValuesBuild children
        (EbnfValue.optional genericAtom
            (genericPrefix.map (EbnfValue.ruleAtom .genericPrefix)),
          EbnfValue.terminalAtom (.hardKeyword .classKw) classKw,
          EbnfValue.ruleAtom .typeAtom main,
          EbnfValue.terminalAtom (.symbol .colon) colon,
          EbnfValue.terminalAtom (.category .identifier) name,
          EbnfValue.optional parameterChild
            (parameterData.map parameterInput),
          EbnfValue.terminalAtom (.symbol .leftBrace) openBrace,
          EbnfValue.star methodAtom
            (methods.map (EbnfValue.ruleAtom .classMethod)),
          EbnfValue.terminalAtom (.symbol .rightBrace) closeBrace, ()))
  have rebuiltEq : rebuilt = input := by
    dsimp only [rebuilt]
    rw [genericEq,
      EbnfValue.terminal_of_view (.hardKeyword .classKw) rawClass,
      EbnfValue.rule_of_view .typeAtom rawMain,
      EbnfValue.terminal_of_view (.symbol .colon) rawColon,
      EbnfValue.terminal_of_view (.category .identifier) rawName,
      constructorParametersEq,
      EbnfValue.terminal_of_view (.symbol .leftBrace) rawOpen,
      methodsEq,
      EbnfValue.terminal_of_view (.symbol .rightBrace) rawClose]
    exact inputEq
  have resultEq : executeClassDeclRoot file tokens origin finish
      ready.1 ready.2.1 input = sourceLoc witness {
        genericPrefix := genericPrefix
        main := main
        className := RuleReduction.terminalLoc
          name name.identifierProjection.2
        parameters := parameterData.map fun value => value.2.1
        methods := methods
      } := by
    simp [executeClassDeclRoot, children, genericAtom, classAtom,
      typeAtom, colonAtom, nameAtom, parameterChild, openAtom, methodAtom,
      closeAtom, sequenceEq, genericPrefix, rawGenericValue,
      main, name, parameterData, rawParameterValue, methods,
      rawMethodValues, witness,
      RuleReduction.terminalLoc]
  have transportSelf
      (value : EbnfValue file tokens (.sequence [
        .optional (.atom (.nonterminal .genericPrefix)),
        .atom (.terminal (.hardKeyword .classKw)),
        .atom (.nonterminal .typeAtom),
        .atom (.terminal (.symbol .colon)),
        .atom (.terminal (.category .identifier)),
        .optional (.sequence [
          .atom (.terminal (.symbol .leftParen)),
          .list1 (.atom (.nonterminal .type)),
          .atom (.terminal (.symbol .rightParen))]),
        .atom (.terminal (.symbol .leftBrace)),
        .star (.atom (.nonterminal .classMethod)),
        .atom (.terminal (.symbol .rightBrace))]))
      (shape : (.sequence [
        .optional (.atom (.nonterminal .genericPrefix)),
        .atom (.terminal (.hardKeyword .classKw)),
        .atom (.nonterminal .typeAtom),
        .atom (.terminal (.symbol .colon)),
        .atom (.terminal (.category .identifier)),
        .optional (.sequence [
          .atom (.terminal (.symbol .leftParen)),
          .list1 (.atom (.nonterminal .type)),
          .atom (.terminal (.symbol .rightParen))]),
        .atom (.terminal (.symbol .leftBrace)),
        .star (.atom (.nonterminal .classMethod)),
        .atom (.terminal (.symbol .rightBrace))]) =
          m2cV1.rhs .classDecl) :
      EbnfValue.transport shape value = value := by
    rw [show shape = (by rfl) from Subsingleton.elim _ _]
    rfl
  have reduces := RuleReduction.classDecl origin finish genericPrefix
    classKw main colon nameData
    parameterData openBrace methods closeBrace
      name.identifierProjection_projects witness
  rw [transportSelf] at reduces
  have outputEq : sourceLoc witness ({
        genericPrefix := genericPrefix
        main := main
        className := RuleReduction.terminalLoc
          name name.identifierProjection.2
        parameters := RuleReduction.arguments parameterData
        methods := methods
      } : ClassDeclPayload) = sourceLoc witness ({
        genericPrefix := genericPrefix
        main := main
        className := RuleReduction.terminalLoc
          name name.identifierProjection.2
        parameters := parameterData.map fun value => value.2.1
        methods := methods
      } : ClassDeclPayload) := by
    cases parameterData <;> rfl
  have normalizedOutputReduces := outputEq ▸ reduces
  have normalizedReduces : RuleReduction file tokens .classDecl
      origin finish rebuilt (sourceLoc witness {
        genericPrefix := genericPrefix
        main := main
        className := RuleReduction.terminalLoc
          name name.identifierProjection.2
        parameters := parameterData.map fun value => value.2.1
        methods := methods
      }) := by
    simpa [rebuilt, children, genericAtom, classAtom, typeAtom,
      colonAtom, nameAtom, parameterChild, openAtom, methodAtom,
      closeAtom, nameData, parameterInput,
      EbnfValue.typeArgumentsValue,
      EbnfValue.typeArgumentsExpr, EbnfValue.sequenceValuesBuild]
      using normalizedOutputReduces
  have inputReduces := rebuiltEq ▸ normalizedReduces
  exact resultEq.symm ▸ inputReduces

/-- The instance-declaration executor realizes its exact root reduction. -/
theorem executeInstanceDeclRoot_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (ready : RuleReductionReady file tokens .instanceDecl origin finish)
    (input : EbnfValue file tokens (m2cV1.rhs .instanceDecl)) :
    RuleReduction file tokens .instanceDecl origin finish input
      (executeInstanceDeclRoot file tokens origin finish
        ready.1 ready.2.1 input) := by
  let genericAtom : EbnfExpr := .atom (.nonterminal .genericPrefix)
  let defaultAtom : EbnfExpr :=
    .atom (.terminal (.hardKeyword .defaultKw))
  let instanceAtom : EbnfExpr :=
    .atom (.terminal (.hardKeyword .instanceKw))
  let mainAtom : EbnfExpr := .atom (.nonterminal .typeAtom)
  let colonAtom : EbnfExpr := .atom (.terminal (.symbol .colon))
  let classAtom : EbnfExpr := .atom (.nonterminal .qualifiedName)
  let parameterChild := EbnfValue.typeArgumentsExpr
  let openAtom : EbnfExpr := .atom (.terminal (.symbol .leftBrace))
  let methodAtom : EbnfExpr := .atom (.nonterminal .instanceMethod)
  let closeAtom : EbnfExpr := .atom (.terminal (.symbol .rightBrace))
  let children : List EbnfExpr := [.optional genericAtom,
    .optional defaultAtom, instanceAtom, mainAtom, colonAtom, classAtom,
    .optional parameterChild, openAtom, .star methodAtom, closeAtom]
  change EbnfValue file tokens (.sequence children) at input
  generalize sequenceEq : EbnfValue.sequenceFlatView children input = values
  rcases values with ⟨rawGeneric, rawDefault, rawInstance, rawMain,
    rawColon, rawClass, rawParameters, rawOpen, rawMethods, rawClose, ⟨⟩⟩
  have inputEq := EbnfValue.sequence_of_flat_view children input
  rw [sequenceEq] at inputEq
  let rawGenericValue := EbnfValue.optionalView genericAtom rawGeneric
  let genericPrefix := rawGenericValue.map
    (EbnfValue.ruleView .genericPrefix)
  let rawDefaultValue := EbnfValue.optionalView defaultAtom rawDefault
  let defaultToken := rawDefaultValue.map
    (EbnfValue.terminalView (.hardKeyword .defaultKw))
  let instanceKw := EbnfValue.terminalView
    (.hardKeyword .instanceKw) rawInstance
  let main := EbnfValue.ruleView .typeAtom rawMain
  let colon := EbnfValue.terminalView (.symbol .colon) rawColon
  let className := EbnfValue.ruleView .qualifiedName rawClass
  let rawParameterValue := EbnfValue.optionalView
    parameterChild rawParameters
  let parameterData := rawParameterValue.map EbnfValue.typeArgumentsView
  let openBrace := EbnfValue.terminalView (.symbol .leftBrace) rawOpen
  let rawMethodValues := EbnfValue.starView methodAtom rawMethods
  let methods := rawMethodValues.map (EbnfValue.ruleView .instanceMethod)
  let closeBrace := EbnfValue.terminalView
    (.symbol .rightBrace) rawClose
  have genericValuesEq : genericPrefix.map
      (EbnfValue.ruleAtom .genericPrefix) = rawGenericValue := by
    cases selected : rawGenericValue with
    | none => simp [genericPrefix, selected]
    | some raw =>
        simp [genericPrefix, selected, EbnfValue.rule_of_view]
  have genericEq : EbnfValue.optional genericAtom
      (genericPrefix.map (EbnfValue.ruleAtom .genericPrefix)) =
        rawGeneric := by
    rw [genericValuesEq]
    exact EbnfValue.optional_of_view genericAtom rawGeneric
  have defaultValuesEq : defaultToken.map
      (EbnfValue.terminalAtom (.hardKeyword .defaultKw)) =
        rawDefaultValue := by
    cases selected : rawDefaultValue with
    | none => simp [defaultToken, selected]
    | some raw =>
        simp [defaultToken, selected, EbnfValue.terminal_of_view]
  have defaultEq : EbnfValue.optional defaultAtom
      (defaultToken.map
        (EbnfValue.terminalAtom (.hardKeyword .defaultKw))) =
        rawDefault := by
    rw [defaultValuesEq]
    exact EbnfValue.optional_of_view defaultAtom rawDefault
  have parameterValuesEq : parameterData.map
      EbnfValue.typeArgumentsValue = rawParameterValue := by
    cases selected : rawParameterValue with
    | none => simp [parameterData, selected]
    | some raw =>
        simp [parameterData, selected,
          EbnfValue.typeArgumentsValue_of_view]
  have parametersEq : EbnfValue.optional parameterChild
      (parameterData.map EbnfValue.typeArgumentsValue) = rawParameters := by
    rw [parameterValuesEq]
    exact EbnfValue.optional_of_view parameterChild rawParameters
  have methodValuesEq : methods.map
      (EbnfValue.ruleAtom .instanceMethod) = rawMethodValues :=
    ruleAtoms_of_views .instanceMethod rawMethodValues
  have methodsEq : EbnfValue.star methodAtom
      (methods.map (EbnfValue.ruleAtom .instanceMethod)) = rawMethods := by
    rw [methodValuesEq]
    exact EbnfValue.star_of_view methodAtom rawMethods
  let witness := ConsumedSpanWitness.compute
    file tokens origin finish ready.1 ready.2.1
  let parameterInput :
      (MatchedTerminal file tokens (.symbol .leftParen) ×
        (NonemptyList TypeExpr ×
          (MatchedTerminal file tokens (.symbol .rightParen) × Unit))) →
        EbnfValue file tokens EbnfValue.typeArgumentsExpr := fun value =>
    EbnfValue.sequence [
      .atom (.terminal (.symbol .leftParen)),
      .list1 (.atom (.nonterminal .type)),
      .atom (.terminal (.symbol .rightParen))]
      (EbnfValues.cons _ _
        (EbnfValue.terminalAtom (.symbol .leftParen) value.1)
        (EbnfValues.cons _ _
          (EbnfValue.list1 _
            (value.2.1.map (EbnfValue.ruleAtom .type)))
          (EbnfValues.cons _ _
            (EbnfValue.terminalAtom
              (.symbol .rightParen) value.2.2.1)
            EbnfValues.nil)))
  have parameterInputEq : parameterInput =
      @EbnfValue.typeArgumentsValue file tokens := by
    funext value
    rfl
  have constructorParametersEq : EbnfValue.optional parameterChild
      (parameterData.map parameterInput) = rawParameters := by
    rw [parameterInputEq]
    exact parametersEq
  let rebuilt : EbnfValue file tokens (.sequence children) :=
    EbnfValue.sequence children
      (EbnfValue.sequenceValuesBuild children
        (EbnfValue.optional genericAtom
            (genericPrefix.map (EbnfValue.ruleAtom .genericPrefix)),
          EbnfValue.optional defaultAtom
            (defaultToken.map
              (EbnfValue.terminalAtom (.hardKeyword .defaultKw))),
          EbnfValue.terminalAtom (.hardKeyword .instanceKw) instanceKw,
          EbnfValue.ruleAtom .typeAtom main,
          EbnfValue.terminalAtom (.symbol .colon) colon,
          EbnfValue.ruleAtom .qualifiedName className,
          EbnfValue.optional parameterChild
            (parameterData.map parameterInput),
          EbnfValue.terminalAtom (.symbol .leftBrace) openBrace,
          EbnfValue.star methodAtom
            (methods.map (EbnfValue.ruleAtom .instanceMethod)),
          EbnfValue.terminalAtom (.symbol .rightBrace) closeBrace, ()))
  have rebuiltEq : rebuilt = input := by
    dsimp only [rebuilt]
    rw [genericEq, defaultEq,
      EbnfValue.terminal_of_view (.hardKeyword .instanceKw) rawInstance,
      EbnfValue.rule_of_view .typeAtom rawMain,
      EbnfValue.terminal_of_view (.symbol .colon) rawColon,
      EbnfValue.rule_of_view .qualifiedName rawClass,
      constructorParametersEq,
      EbnfValue.terminal_of_view (.symbol .leftBrace) rawOpen,
      methodsEq,
      EbnfValue.terminal_of_view (.symbol .rightBrace) rawClose]
    exact inputEq
  let executorParameters := rawParameterValue.map fun raw =>
    let viewed := EbnfValue.sequence3View
      (.atom (.terminal (.symbol .leftParen)))
      (.list1 (.atom (.nonterminal .type)))
      (.atom (.terminal (.symbol .rightParen))) raw
    (EbnfValue.list1View (.atom (.nonterminal .type))
      viewed.2.1).map (EbnfValue.ruleView .type)
  have executorParametersEq : executorParameters =
      parameterData.map fun value => value.2.1 := by
    cases selected : rawParameterValue with
    | none =>
        simp only [executorParameters, parameterData, selected, Option.map]
        rfl
    | some raw =>
        simp only [executorParameters, parameterData, selected, Option.map]
        rfl
  have resultEq : executeInstanceDeclRoot file tokens origin finish
      ready.1 ready.2.1 input = sourceLoc witness {
        genericPrefix := genericPrefix
        «default» := defaultToken.map fun terminal =>
          RuleReduction.terminalLoc terminal .defaultModifier
        main := main
        className := className
        parameters := parameterData.map fun value => value.2.1
        methods := methods
      } := by
    calc
      _ = sourceLoc witness ({
          genericPrefix := genericPrefix
          «default» := defaultToken.map fun terminal =>
            RuleReduction.terminalLoc terminal .defaultModifier
          main := main
          className := className
          parameters := executorParameters
          methods := methods
        } : InstanceDeclPayload) := by
          have sequenceEq' := sequenceEq
          simp only [children, genericAtom, defaultAtom, instanceAtom,
            mainAtom, colonAtom, classAtom, parameterChild, openAtom,
            methodAtom, closeAtom, EbnfValue.typeArgumentsExpr] at sequenceEq'
          simp only [executeInstanceDeclRoot, sequenceEq']
          rfl
      _ = _ := by
        rw [executorParametersEq]
  have transportSelf
      (value : EbnfValue file tokens (.sequence [
        .optional (.atom (.nonterminal .genericPrefix)),
        .optional (.atom (.terminal (.hardKeyword .defaultKw))),
        .atom (.terminal (.hardKeyword .instanceKw)),
        .atom (.nonterminal .typeAtom),
        .atom (.terminal (.symbol .colon)),
        .atom (.nonterminal .qualifiedName),
        .optional (.sequence [
          .atom (.terminal (.symbol .leftParen)),
          .list1 (.atom (.nonterminal .type)),
          .atom (.terminal (.symbol .rightParen))]),
        .atom (.terminal (.symbol .leftBrace)),
        .star (.atom (.nonterminal .instanceMethod)),
        .atom (.terminal (.symbol .rightBrace))]))
      (shape : (.sequence [
        .optional (.atom (.nonterminal .genericPrefix)),
        .optional (.atom (.terminal (.hardKeyword .defaultKw))),
        .atom (.terminal (.hardKeyword .instanceKw)),
        .atom (.nonterminal .typeAtom),
        .atom (.terminal (.symbol .colon)),
        .atom (.nonterminal .qualifiedName),
        .optional (.sequence [
          .atom (.terminal (.symbol .leftParen)),
          .list1 (.atom (.nonterminal .type)),
          .atom (.terminal (.symbol .rightParen))]),
        .atom (.terminal (.symbol .leftBrace)),
        .star (.atom (.nonterminal .instanceMethod)),
        .atom (.terminal (.symbol .rightBrace))]) =
          m2cV1.rhs .instanceDecl) :
      EbnfValue.transport shape value = value := by
    rw [show shape = (by rfl) from Subsingleton.elim _ _]
    rfl
  have argumentsEq : RuleReduction.arguments parameterData =
      parameterData.map fun value => value.2.1 := by
    cases parameterData <;> rfl
  cases selectedDefault : defaultToken with
  | none =>
      have reduces := RuleReduction.instanceDecl origin finish genericPrefix
        none instanceKw main colon className parameterData openBrace methods
        closeBrace (fun terminal _ => .defaultModifier terminal) witness
      rw [transportSelf, argumentsEq] at reduces
      have normalizedReduces : RuleReduction file tokens .instanceDecl
          origin finish rebuilt (sourceLoc witness {
            genericPrefix := genericPrefix
            «default» := none
            main := main
            className := className
            parameters := parameterData.map fun value => value.2.1
            methods := methods
          }) := by
        simpa [rebuilt, children, genericAtom, defaultAtom, instanceAtom,
          mainAtom, colonAtom, classAtom, parameterChild, openAtom,
          methodAtom, closeAtom, parameterInput, selectedDefault,
          EbnfValue.typeArgumentsValue, EbnfValue.typeArgumentsExpr,
          EbnfValue.sequenceValuesBuild] using reduces
      have inputReduces := rebuiltEq ▸ normalizedReduces
      have resultEq' := resultEq
      rw [selectedDefault] at resultEq'
      exact resultEq'.symm ▸ inputReduces
  | some terminal =>
      have reduces := RuleReduction.instanceDecl origin finish genericPrefix
        (some terminal) instanceKw main colon className parameterData
        openBrace methods closeBrace
        (fun value _ => .defaultModifier value) witness
      rw [transportSelf, argumentsEq] at reduces
      have normalizedReduces : RuleReduction file tokens .instanceDecl
          origin finish rebuilt (sourceLoc witness {
            genericPrefix := genericPrefix
            «default» := some
              (RuleReduction.terminalLoc terminal .defaultModifier)
            main := main
            className := className
            parameters := parameterData.map fun value => value.2.1
            methods := methods
          }) := by
        simpa [rebuilt, children, genericAtom, defaultAtom, instanceAtom,
          mainAtom, colonAtom, classAtom, parameterChild, openAtom,
          methodAtom, closeAtom, parameterInput, selectedDefault,
          EbnfValue.typeArgumentsValue, EbnfValue.typeArgumentsExpr,
          EbnfValue.sequenceValuesBuild, RuleReduction.marker,
          RuleReduction.terminalLoc] using reduces
      have inputReduces := rebuiltEq ▸ normalizedReduces
      have resultEq' := resultEq
      rw [selectedDefault] at resultEq'
      exact resultEq'.symm ▸ inputReduces

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
  | moduleRef =>
      exact executeModuleRefRoot_reduces origin finish ready input
  | importDecl =>
      exact executeImportDeclRoot_reduces origin finish ready input
  | exportDecl =>
      exact executeExportDeclRoot_reduces origin finish ready input
  | importEntry =>
      exact executeImportEntryRoot_reduces origin finish ready input
  | localExportEntry =>
      exact executeLocalExportEntryRoot_reduces origin finish ready input
  | remoteExportEntry =>
      exact executeRemoteExportEntryRoot_reduces origin finish ready input
  | optionalComma =>
      exact executeOptionalCommaRoot_reduces origin finish ready input
  | predicateList =>
      exact executePredicateListRoot_reduces origin finish ready input
  | predicate =>
      exact executePredicateRoot_reduces origin finish ready input
  | functionSignature =>
      exact executeFunctionSignatureRoot_reduces origin finish ready input
  | instanceMethod =>
      exact executeInstanceMethodRoot_reduces origin finish ready input
  | armStatement =>
      exact executeArmStatementRoot_reduces origin finish ready input
  | matchArm =>
      exact executeMatchArmRoot_reduces origin finish ready input
  | statement =>
      exact executeStatementRoot_reduces origin finish ready input
  | terminalExpression =>
      exact executeTerminalExpressionRoot_reduces origin finish ready input
  | pattern =>
      exact executePatternRoot_reduces origin finish ready input
  | expression =>
      exact executeExpressionRoot_reduces origin finish ready input
  | annotation =>
      exact executeAnnotationRoot_reduces origin finish ready input
  | conditional =>
      exact executeConditionalRoot_reduces origin finish ready input
  | blockStatement =>
      exact executeBlockStatementRoot_reduces origin finish ready input
  | functionDecl =>
      exact executeFunctionDeclRoot_reduces origin finish ready input
  | classMethod =>
      exact executeClassMethodRoot_reduces origin finish ready input
  | letStatement =>
      exact executeLetStatementRoot_reduces origin finish ready input
  | letBinding =>
      exact executeLetBindingRoot_reduces origin finish ready input
  | breakStatement =>
      exact executeBreakStatementRoot_reduces origin finish ready input
  | continueStatement =>
      exact executeContinueStatementRoot_reduces origin finish ready input
  | assemblyStatement =>
      exact executeAssemblyStatementRoot_reduces origin finish ready input
  | ifStatement =>
      exact executeIfStatementRoot_reduces origin finish ready input
  | matchStatement =>
      exact executeMatchStatementRoot_reduces origin finish ready input
  | returnStatement =>
      exact executeReturnStatementRoot_reduces origin finish ready input
  | assignmentStatement =>
      exact executeAssignmentStatementRoot_reduces origin finish ready input
  | parameter => exact executeParameterRoot_reduces origin finish ready input
  | dataDecl =>
      exact executeDataDeclRoot_reduces origin finish ready input
  | contractDecl =>
      exact executeContractDeclRoot_reduces origin finish ready input
  | dataConstructor =>
      exact executeDataConstructorRoot_reduces origin finish ready input
  | typeAliasDecl =>
      exact executeTypeAliasDeclRoot_reduces origin finish ready input
  | classDecl =>
      exact executeClassDeclRoot_reduces origin finish ready input
  | instanceDecl =>
      exact executeInstanceDeclRoot_reduces origin finish ready input
  | fieldDecl => exact executeFieldDeclRoot_reduces origin finish ready input
  | fallbackDecl =>
      exact executeFallbackDeclRoot_reduces origin finish ready input
  | contractConstructorDecl =>
      exact executeContractConstructorDeclRoot_reduces
        origin finish ready input
  | pragmaDecl => exact executePragmaDeclRoot_reduces origin finish ready input
  | genericPrefix =>
      exact executeGenericPrefixRoot_reduces origin finish ready input
  | forallClause =>
      exact executeForallClauseRoot_reduces origin finish ready input
  | forallBinder =>
      exact executeForallBinderRoot_reduces origin finish ready input
  | exportItem =>
      exact executeExportItemRoot_reduces origin finish ready input
  | constructorSelection =>
      exact executeConstructorSelectionRoot_reduces origin finish ready input
  | hidingClause =>
      exact executeHidingClauseRoot_reduces origin finish ready input
  | body => exact executeBodyRoot_reduces origin finish ready input
  | «type» => exact executeTypeRoot_reduces origin finish ready input
  | typeAtom =>
      exact executeTypeAtomRoot_reduces origin finish ready input
  | qualifiedName =>
      exact executeQualifiedNameRoot_reduces origin finish ready input
  | forStatement =>
      exact executeForStatementRoot_reduces origin finish ready input
  | forInitItem =>
      exact executeForInitItemRoot_reduces origin finish ready input
  | forPostItem =>
      exact executeForPostItemRoot_reduces origin finish ready input
  | expressionStatement =>
      exact executeExpressionStatementRoot_reduces origin finish ready input
  | contractMember =>
      exact executeContractMemberRoot_reduces origin finish ready input
  | assignmentOperator =>
      exact executeAssignmentOperatorRoot_reduces origin finish ready input
  | logicalOr => exact executeLogicalOrRoot_reduces origin finish ready input
  | logicalAnd => exact executeLogicalAndRoot_reduces origin finish ready input
  | equality => exact executeEqualityRoot_reduces origin finish ready input
  | relational => exact executeRelationalRoot_reduces origin finish ready input
  | bitOr => exact executeBitOrRoot_reduces origin finish ready input
  | bitXor => exact executeBitXorRoot_reduces origin finish ready input
  | bitAnd => exact executeBitAndRoot_reduces origin finish ready input
  | additive => exact executeAdditiveRoot_reduces origin finish ready input
  | multiplicative => exact executeMultiplicativeRoot_reduces origin finish ready input
  | «prefix» => exact executePrefixRoot_reduces origin finish ready input
  | postfixExpr => exact executePostfixRoot_reduces origin finish ready input
  | postfixPart =>
      exact executePostfixPartRoot_reduces origin finish ready input
  | atomExpr => exact executeAtomRoot_reduces origin finish ready input
  | literalValue => exact executeLiteralRoot_reduces origin finish ready input
  | lambdaExpr => exact executeLambdaRoot_reduces origin finish ready input

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

/-- The total production executor realizes the exact declarative action for
all eleven generated production shapes. -/
theorem executeProductionAction_reduces
    {file : WorkspaceFile} {tokens : List Token}
    (production : ProductionId)
    (origin finish : Boundary tokens)
    (ready : ActionReductionReady file tokens (.actionFor production)
      origin finish)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (input : GrammarSymbolValues file tokens production.rhs) :
    ActionReduces file tokens (.actionFor production) origin finish input
      (executeProductionAction file tokens origin finish production
        owned ordered input) := by
  cases production with
  | root rule =>
      exact executeRootAction_reduces rule (executableRootRule rule)
        origin finish ready input
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

/-- Every declarative production action returns the total executor's result. -/
theorem ActionReduces.eq_executeProductionAction
    {file : WorkspaceFile} {tokens : List Token}
    {production : ProductionId}
    {origin finish : Boundary tokens}
    (ready : ActionReductionReady file tokens (.actionFor production)
      origin finish)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    {input : GrammarSymbolValues file tokens production.rhs}
    {output : NonterminalValue file tokens production.lhs}
    (reduces : ActionReduces file tokens (.actionFor production)
      origin finish input output) :
    output = executeProductionAction file tokens origin finish production
      owned ordered input :=
  ActionReduces.functional reduces
    (executeProductionAction_reduces production origin finish ready owned
      ordered input)

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

private theorem actionReductionReady_of_moduleInterval
    {file : WorkspaceFile} {tokens : List Token}
    {production : ProductionId}
    {origin finish : Boundary tokens}
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val)
    (moduleInterval : production = .root .module →
      origin = Boundary.start tokens ∧
        finish = Boundary.afterLogicalEOF tokens) :
    ActionReductionReady file tokens (.actionFor production)
      origin finish := by
  cases production with
  | root rule =>
      exact ⟨owned, ordered, fun ruleEq =>
        moduleInterval (by simp [ruleEq])⟩
  | atom site => trivial
  | seq site => trivial
  | group site => trivial
  | choice site branch => trivial
  | opt site branch => trivial
  | star site branch => trivial
  | plus site branch => trivial
  | list0 site branch => trivial
  | list1 site => trivial
  | tail site branch => trivial

namespace Chart

/-- The computed dot-zero prefix is declaratively coherent. -/
theorem ContextualPrefixValue.zero_coherent
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (item : ContextualItemKey tokens)
    (reached : ContextualReach file tokens memo correct final item)
    (atZero : item.raw.dot.val = 0) :
    CoherentPrefix file tokens memo correct final item
      (ContextualPrefixValue.zero item atZero).value := by
  exact .zero item reached atZero

/-- A computed witnessed scan preserves declarative prefix coherence. -/
theorem ContextualPrefixValue.scan_coherent
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (edge : WitnessedContextualScannedEdge file tokens)
    (edgeReached : ContextualEdgeReach file tokens memo correct final
      edge.toPacked.val)
    (prior : ContextualPrefixValue file tokens edge.before)
    (priorCoherent : CoherentPrefix file tokens memo correct final
      edge.before prior.value) :
    CoherentPrefix file tokens memo correct final edge.after
      (ContextualPrefixValue.scan edge prior).value := by
  exact .scan edge.before edge.after edge.cursor prior.value edge.witness
    (by simpa using edgeReached) priorCoherent

/-- A computed witnessed completion preserves declarative prefix coherence. -/
theorem ContextualPrefixValue.complete_coherent
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (edge : WitnessedContextualCompletedEdge file tokens)
    (edgeReached : ContextualEdgeReach file tokens memo correct final
      edge.toPacked.val)
    (prior : ContextualPrefixValue file tokens edge.waiting)
    (child : ContextualReductionValue file tokens edge.finished)
    (priorCoherent : CoherentPrefix file tokens memo correct final
      edge.waiting prior.value)
    (childCoherent : CoherentReduction file tokens memo correct final
      edge.finished child.value) :
    CoherentPrefix file tokens memo correct final edge.after
      (ContextualPrefixValue.complete edge prior child).value := by
  exact .complete edge.waiting edge.finished edge.after edge.shared
    prior.value child.value edge.witness (by simpa using edgeReached)
    priorCoherent childCoherent

/-- Applying the total action to a coherent complete prefix computes a
declaratively coherent reduction. -/
theorem ContextualReductionValue.reduce_coherent
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (owned : TokensOwnedBy file tokens)
    (item : ContextualItemKey tokens)
    (reached : ContextualReach file tokens memo correct final item)
    (isComplete : CompleteItem item.raw)
    (prior : ContextualPrefixValue file tokens item)
    (priorCoherent : CoherentPrefix file tokens memo correct final
      item prior.value)
    (moduleInterval : item.raw.production = .root .module →
      item.raw.origin = Boundary.start tokens ∧
        item.raw.current = Boundary.afterLogicalEOF tokens) :
    CoherentReduction file tokens memo correct final item
      (ContextualReductionValue.reduce owned item
        (contextualReach_ordered reached) isComplete prior).value := by
  let ordered := contextualReach_ordered reached
  let ready := actionReductionReady_of_moduleInterval owned ordered
    moduleInterval
  exact .reduce item prior.value _ reached isComplete priorCoherent
    (executeProductionAction_reduces item.raw.production item.raw.origin
      item.raw.current ready owned ordered
      (PrefixValues.fullValue item isComplete prior.value))

/-- Every successful executable readiness check yields a declaratively
coherent reduction. -/
theorem ContextualReductionValue.reduce?_coherent
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (owned : TokensOwnedBy file tokens)
    (item : ContextualItemKey tokens)
    (reached : ContextualReach file tokens memo correct final item)
    (prior : ContextualPrefixValue file tokens item)
    (priorCoherent : CoherentPrefix file tokens memo correct final
      item prior.value)
    (result : ContextualReductionValue file tokens item)
    (selected : ContextualReductionValue.reduce? owned item prior =
      some result) :
    CoherentReduction file tokens memo correct final item result.value := by
  rcases (ContextualReductionValue.reduce?_eq_some_iff
    owned item prior result).mp selected with
    ⟨_ordered, complete, moduleInterval, rfl⟩
  exact ContextualReductionValue.reduce_coherent owned item reached complete
    prior priorCoherent moduleInterval

namespace ContextualValueFrontierState

/-- Item identities present in the dependent prefix ledger. -/
def prefixKeys
    {file : WorkspaceFile} {tokens : List Token}
    (state : ContextualValueFrontierState file tokens) :
    List (ContextualItemKey tokens) :=
  state.prefixes.map ContextualPrefixLedgerEntry.item

/-- Item identities present in the dependent reduction ledger. -/
def reductionKeys
    {file : WorkspaceFile} {tokens : List Token}
    (state : ContextualValueFrontierState file tokens) :
    List (ContextualItemKey tokens) :=
  state.reductions.map ContextualReductionLedgerEntry.item

/-- Every semantic item identity is stored at most once, and every queued
identity denotes an already retained prefix. -/
def WellFormed
    {file : WorkspaceFile} {tokens : List Token}
    (state : ContextualValueFrontierState file tokens) : Prop :=
  state.prefixKeys.Nodup ∧
    state.reductionKeys.Nodup ∧
    state.queue.Nodup ∧
    (∀ item, item ∈ state.queue → item ∈ state.prefixKeys) ∧
    ∀ item, item ∈ state.reductionKeys → item ∈ state.prefixKeys

/-- Executable prefix membership is exactly key-ledger membership. -/
theorem prefixMemberBool_eq_true_iff
    {file : WorkspaceFile} {tokens : List Token}
    (state : ContextualValueFrontierState file tokens)
    (item : ContextualItemKey tokens) :
    state.prefixMemberBool item = true ↔ item ∈ state.prefixKeys := by
  simp only [prefixMemberBool, prefixKeys, List.any_eq_true,
    List.mem_map]
  constructor
  · rintro ⟨entry, member, equal⟩
    exact ⟨entry, member, of_decide_eq_true equal⟩
  · rintro ⟨entry, member, equal⟩
    exact ⟨entry, member, by simp [equal]⟩

/-- Executable reduction membership is exactly key-ledger membership. -/
theorem reductionMemberBool_eq_true_iff
    {file : WorkspaceFile} {tokens : List Token}
    (state : ContextualValueFrontierState file tokens)
    (item : ContextualItemKey tokens) :
    state.reductionMemberBool item = true ↔
      item ∈ state.reductionKeys := by
  simp only [reductionMemberBool, reductionKeys, List.any_eq_true,
    List.mem_map]
  constructor
  · rintro ⟨entry, member, equal⟩
    exact ⟨entry, member, of_decide_eq_true equal⟩
  · rintro ⟨entry, member, equal⟩
    exact ⟨entry, member, by simp [equal]⟩

/-- The empty semantic frontier satisfies all ledger and queue invariants. -/
@[simp] theorem empty_wellFormed
    (file : WorkspaceFile) (tokens : List Token) :
    (empty file tokens).WellFormed := by
  simp [WellFormed, prefixKeys, reductionKeys, empty]

/-- Prefix insertion preserves key uniqueness and enqueues a key at most
once. -/
theorem insertPrefix_wellFormed
    {file : WorkspaceFile} {tokens : List Token}
    (state : ContextualValueFrontierState file tokens)
    (item : ContextualItemKey tokens)
    (value : ContextualPrefixValue file tokens item)
    (wellFormed : state.WellFormed) :
    (state.insertPrefix item value).WellFormed := by
  by_cases present : state.prefixMemberBool item = true
  · rw [insertPrefix_of_present state item value present]
    exact wellFormed
  · have absent : state.prefixMemberBool item = false := by
      cases equal : state.prefixMemberBool item <;> simp_all
    have itemFresh : item ∉ state.prefixKeys := by
      intro member
      exact present ((prefixMemberBool_eq_true_iff state item).mpr member)
    have itemQueueFresh : item ∉ state.queue := by
      intro member
      exact itemFresh (wellFormed.2.2.2.1 item member)
    rcases wellFormed with
      ⟨prefixUnique, reductionUnique, queueUnique, queueSubset,
        reductionSubset⟩
    simp only [WellFormed, prefixKeys, reductionKeys, insertPrefix, absent,
      Bool.false_eq_true, ↓reduceIte, List.map_append, List.map_cons,
      List.map_nil]
    refine ⟨?_, reductionUnique, ?_, ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨by simpa only [prefixKeys] using prefixUnique, by simp, ?_⟩
      intro old oldMember new newMember
      simp only [List.mem_singleton] at newMember
      subst new
      intro equal
      exact itemFresh (equal ▸ oldMember)
    · rw [List.nodup_append]
      refine ⟨queueUnique, by simp, ?_⟩
      intro old oldMember new newMember
      simp only [List.mem_singleton] at newMember
      subst new
      intro equal
      exact itemQueueFresh (equal ▸ oldMember)
    · intro candidate member
      rw [List.mem_append] at member ⊢
      rcases member with old | new
      · exact Or.inl (queueSubset candidate old)
      · exact Or.inr (by simpa using new)
    · intro candidate member
      rw [List.mem_append]
      exact Or.inl (reductionSubset candidate member)

/-- Reduction insertion preserves the invariant when its prefix key is
already retained; it never creates a second queue identity. -/
theorem insertReduction_wellFormed
    {file : WorkspaceFile} {tokens : List Token}
    (state : ContextualValueFrontierState file tokens)
    (item : ContextualItemKey tokens)
    (value : ContextualReductionValue file tokens item)
    (wellFormed : state.WellFormed)
    (prefixPresent : state.prefixMemberBool item = true) :
    (state.insertReduction item value).WellFormed := by
  by_cases present : state.reductionMemberBool item = true
  · rw [insertReduction_of_present state item value present]
    exact wellFormed
  · have absent : state.reductionMemberBool item = false := by
      cases equal : state.reductionMemberBool item <;> simp_all
    have itemFresh : item ∉ state.reductionKeys := by
      intro member
      exact present ((reductionMemberBool_eq_true_iff state item).mpr member)
    rcases wellFormed with
      ⟨prefixUnique, reductionUnique, queueUnique, queueSubset,
        reductionSubset⟩
    simp only [WellFormed, prefixKeys, reductionKeys, insertReduction,
      absent, Bool.false_eq_true, ↓reduceIte, List.map_append, List.map_cons,
      List.map_nil]
    refine ⟨prefixUnique, ?_, queueUnique, queueSubset, ?_⟩
    · rw [List.nodup_append]
      refine ⟨by simpa only [reductionKeys] using reductionUnique,
        by simp, ?_⟩
      intro old oldMember new newMember
      simp only [List.mem_singleton] at newMember
      subst new
      intro equal
      exact itemFresh (equal ▸ oldMember)
    · intro candidate member
      rw [List.mem_append] at member
      rcases member with old | new
      · exact reductionSubset candidate old
      · have candidateEq : candidate = item := by simpa using new
        subst candidate
        exact (prefixMemberBool_eq_true_iff state item).mp prefixPresent

/-- Removing the oldest queue key preserves all persistent-ledger and queue
invariants. -/
theorem dequeue?_wellFormed
    {file : WorkspaceFile} {tokens : List Token}
    (state next : ContextualValueFrontierState file tokens)
    (item : ContextualItemKey tokens)
    (wellFormed : state.WellFormed)
    (selected : state.dequeue? = some (item, next)) :
    next.WellFormed := by
  unfold dequeue? at selected
  cases queueEq : state.queue with
  | nil => simp [queueEq] at selected
  | cons head tail =>
      simp only [queueEq, Option.some.injEq, Prod.mk.injEq] at selected
      rcases selected with ⟨_headEq, nextEq⟩
      subst next
      rcases wellFormed with
        ⟨prefixUnique, reductionUnique, queueUnique, queueSubset,
          reductionSubset⟩
      simp only [WellFormed, prefixKeys, reductionKeys]
      refine ⟨prefixUnique, reductionUnique,
        (List.nodup_cons.mp (queueEq ▸ queueUnique)).2, ?_,
        reductionSubset⟩
      intro candidate member
      exact queueSubset candidate
        (queueEq.symm ▸ List.mem_cons_of_mem _ member)

private instance completeItemDecidable
    {tokens : List Token} (item : DottedItem tokens) :
    Decidable (CompleteItem item) := by
  unfold CompleteItem
  infer_instance

/-- Strong persistent form of the requested queue invariant. -/
def CompletePrefixesReduced
    {file : WorkspaceFile} {tokens : List Token}
    (state : ContextualValueFrontierState file tokens) : Prop :=
  ∀ item, item ∈ state.prefixKeys → CompleteItem item.raw →
    item ∈ state.reductionKeys

/-- The executable semantic frontier invariant. -/
def ExecutableWellFormed
    {file : WorkspaceFile} {tokens : List Token}
    (state : ContextualValueFrontierState file tokens) : Prop :=
  state.WellFormed ∧ CompletePrefixesReduced state

/-- The persistent invariant implies the exact requested queue condition. -/
theorem queued_complete_has_reduction
    {file : WorkspaceFile} {tokens : List Token}
    (state : ContextualValueFrontierState file tokens)
    (wellFormed : ExecutableWellFormed state)
    (item : ContextualItemKey tokens)
    (queued : item ∈ state.queue)
    (complete : CompleteItem item.raw) :
    item ∈ state.reductionKeys := by
  exact wellFormed.2 item (wellFormed.1.2.2.2.1 item queued) complete
@[simp] theorem empty_executableWellFormed
    (file : WorkspaceFile) (tokens : List Token) :
    ExecutableWellFormed
      (ContextualValueFrontierState.empty file tokens) := by
  constructor
  · exact ContextualValueFrontierState.empty_wellFormed file tokens
  · intro item member _complete
    simp [ContextualValueFrontierState.prefixKeys,
      ContextualValueFrontierState.empty] at member

private theorem insertPrefix_prefixKeys_of_absent
    {file : WorkspaceFile} {tokens : List Token}
    (state : ContextualValueFrontierState file tokens)
    (item : ContextualItemKey tokens)
    (prior : ContextualPrefixValue file tokens item)
    (absent : state.prefixMemberBool item = false) :
    (state.insertPrefix item prior).prefixKeys =
      state.prefixKeys ++ [item] := by
  simp [ContextualValueFrontierState.prefixKeys,
    ContextualValueFrontierState.insertPrefix, absent]

private theorem insertPrefix_reductionKeys_of_absent
    {file : WorkspaceFile} {tokens : List Token}
    (state : ContextualValueFrontierState file tokens)
    (item : ContextualItemKey tokens)
    (prior : ContextualPrefixValue file tokens item)
    (absent : state.prefixMemberBool item = false) :
    (state.insertPrefix item prior).reductionKeys = state.reductionKeys := by
  simp [ContextualValueFrontierState.reductionKeys,
    ContextualValueFrontierState.insertPrefix, absent]

private theorem insertReduction_prefixKeys
    {file : WorkspaceFile} {tokens : List Token}
    (state : ContextualValueFrontierState file tokens)
    (item : ContextualItemKey tokens)
    (value : ContextualReductionValue file tokens item) :
    (state.insertReduction item value).prefixKeys = state.prefixKeys := by
  by_cases present : state.reductionMemberBool item = true
  · rw [ContextualValueFrontierState.insertReduction_of_present
      state item value present]
  · have absent : state.reductionMemberBool item = false := by
      cases equal : state.reductionMemberBool item <;> simp_all
    simp [ContextualValueFrontierState.prefixKeys,
      ContextualValueFrontierState.insertReduction, absent]

private theorem insertReduction_contains
    {file : WorkspaceFile} {tokens : List Token}
    (state : ContextualValueFrontierState file tokens)
    (item : ContextualItemKey tokens)
    (value : ContextualReductionValue file tokens item) :
    item ∈ (state.insertReduction item value).reductionKeys := by
  by_cases present : state.reductionMemberBool item = true
  · rw [ContextualValueFrontierState.insertReduction_of_present
      state item value present]
    exact (ContextualValueFrontierState.reductionMemberBool_eq_true_iff
      state item).mp present
  · have absent : state.reductionMemberBool item = false := by
      cases equal : state.reductionMemberBool item <;> simp_all
    simp [ContextualValueFrontierState.reductionKeys,
      ContextualValueFrontierState.insertReduction, absent]

private theorem insertReduction_retains
    {file : WorkspaceFile} {tokens : List Token}
    (state : ContextualValueFrontierState file tokens)
    (item : ContextualItemKey tokens)
    (value : ContextualReductionValue file tokens item)
    (candidate : ContextualItemKey tokens)
    (member : candidate ∈ state.reductionKeys) :
    candidate ∈ (state.insertReduction item value).reductionKeys := by
  by_cases present : state.reductionMemberBool item = true
  · rw [ContextualValueFrontierState.insertReduction_of_present
      state item value present]
    exact member
  · have absent : state.reductionMemberBool item = false := by
      cases equal : state.reductionMemberBool item <;> simp_all
    simp only [ContextualValueFrontierState.reductionKeys,
      ContextualValueFrontierState.insertReduction, absent,
      Bool.false_eq_true, ↓reduceIte, List.map_append, List.map_cons,
      List.map_nil, List.mem_append]
    exact Or.inl member

private theorem prefix_present_after_fresh_insert
    {file : WorkspaceFile} {tokens : List Token}
    (state : ContextualValueFrontierState file tokens)
    (item : ContextualItemKey tokens)
    (prior : ContextualPrefixValue file tokens item)
    (absent : state.prefixMemberBool item = false) :
    (state.insertPrefix item prior).prefixMemberBool item = true := by
  rw [ContextualValueFrontierState.prefixMemberBool_eq_true_iff]
  simp [ContextualValueFrontierState.prefixKeys,
    ContextualValueFrontierState.insertPrefix, absent]

private theorem completePrefixesReduced_insertPrefix_incomplete
    {file : WorkspaceFile} {tokens : List Token}
    (state : ContextualValueFrontierState file tokens)
    (item : ContextualItemKey tokens)
    (prior : ContextualPrefixValue file tokens item)
    (reduced : CompletePrefixesReduced state)
    (absent : state.prefixMemberBool item = false)
    (incomplete : ¬ CompleteItem item.raw) :
    CompletePrefixesReduced (state.insertPrefix item prior) := by
  intro candidate member complete
  rw [insertPrefix_prefixKeys_of_absent state item prior absent] at member
  rw [insertPrefix_reductionKeys_of_absent state item prior absent]
  rw [List.mem_append] at member
  rcases member with old | equal
  · exact reduced candidate old complete
  · have candidateEq : candidate = item := by simpa using equal
    subst candidate
    exact False.elim (incomplete complete)

private theorem completePrefixesReduced_insertReduction
    {file : WorkspaceFile} {tokens : List Token}
    (state : ContextualValueFrontierState file tokens)
    (item : ContextualItemKey tokens)
    (value : ContextualReductionValue file tokens item)
    (reduced : CompletePrefixesReduced state) :
    CompletePrefixesReduced (state.insertReduction item value) := by
  intro candidate member complete
  rw [insertReduction_prefixKeys state item value] at member
  exact insertReduction_retains state item value candidate
    (reduced candidate member complete)

private theorem completePrefixesReduced_insertComplete
    {file : WorkspaceFile} {tokens : List Token}
    (state : ContextualValueFrontierState file tokens)
    (item : ContextualItemKey tokens)
    (prior : ContextualPrefixValue file tokens item)
    (value : ContextualReductionValue file tokens item)
    (reduced : CompletePrefixesReduced state)
    (absent : state.prefixMemberBool item = false) :
    CompletePrefixesReduced
      ((state.insertPrefix item prior).insertReduction item value) := by
  let withPrefix := state.insertPrefix item prior
  intro candidate member complete
  rw [insertReduction_prefixKeys withPrefix item value] at member
  rw [insertPrefix_prefixKeys_of_absent state item prior absent] at member
  rw [List.mem_append] at member
  rcases member with old | new
  · have oldReduction : candidate ∈ state.reductionKeys :=
      reduced candidate old complete
    have retainedByPrefix : candidate ∈ withPrefix.reductionKeys := by
      rw [insertPrefix_reductionKeys_of_absent state item prior absent]
      exact oldReduction
    exact insertReduction_retains withPrefix item value candidate
      retainedByPrefix
  · have candidateEq : candidate = item := by simpa using new
    subst candidate
    exact insertReduction_contains withPrefix item value

/-- The pure helper preserves both key discipline and complete-value
availability in all success branches, including the duplicate no-op. -/
theorem insertCandidate?_preserves
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (state : ContextualValueFrontierState file tokens)
    (item : ContextualItemKey tokens)
    (prior : ContextualPrefixValue file tokens item)
    (before : ExecutableWellFormed state)
    (result : CandidateInsertResult file tokens)
    (selected : insertCandidate? owned state item prior = some result) :
    ExecutableWellFormed result.state := by
  by_cases present : state.prefixMemberBool item = true
  · simp [insertCandidate?, present] at selected
    subst result
    exact before
  · have absent : state.prefixMemberBool item = false := by
      cases equal : state.prefixMemberBool item <;> simp_all
    by_cases complete : CompleteItem item.raw
    · cases reductionEq : ContextualReductionValue.reduce? owned item prior with
      | none =>
          simp [insertCandidate?, absent, complete, reductionEq] at selected
      | some reduction =>
          have resultEq :
              ({ kind := CandidateInsertKind.insertedComplete
                 state := (state.insertPrefix item prior).insertReduction
                   item reduction } : CandidateInsertResult file tokens) =
                result := by
            exact Option.some.inj (by
              simpa [insertCandidate?, absent, complete, reductionEq]
                using selected)
          subst result
          constructor
          · apply ContextualValueFrontierState.insertReduction_wellFormed
            · exact ContextualValueFrontierState.insertPrefix_wellFormed
                state item prior before.1
            · exact prefix_present_after_fresh_insert state item prior absent
          · exact completePrefixesReduced_insertComplete state item prior
              reduction before.2 absent
    · simp [insertCandidate?, present, complete] at selected
      subst result
      exact ⟨ContextualValueFrontierState.insertPrefix_wellFormed
          state item prior before.1,
        completePrefixesReduced_insertPrefix_incomplete state item prior
          before.2 absent complete⟩

/-- Queue consumption keeps the persistent reduction availability needed by
later completion traversals. -/
theorem dequeue?_preserves
    {file : WorkspaceFile} {tokens : List Token}
    (state next : ContextualValueFrontierState file tokens)
    (item : ContextualItemKey tokens)
    (before : ExecutableWellFormed state)
    (selected : state.dequeue? = some (item, next)) :
    ExecutableWellFormed next := by
  constructor
  · exact ContextualValueFrontierState.dequeue?_wellFormed
      state next item before.1 selected
  · unfold ContextualValueFrontierState.dequeue? at selected
    cases queueEq : state.queue with
    | nil => simp [queueEq] at selected
    | cons head tail =>
        simp only [queueEq, Option.some.injEq, Prod.mk.injEq] at selected
        rcases selected with ⟨_headEq, nextEq⟩
        subst next
        exact before.2

end ContextualValueFrontierState

end Chart

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

namespace Solcore.Surface.Multi

open Solcore.Workspace

/-- Absence of the canonical completed module item in a successful executable
chart rules out every declarative source-backed root. -/
theorem executeObservedContextualWorklist?_noSourceBackedRoot_of_completeModuleRootItem_eq_false
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result)
    (absent : result.containsCompleteModuleRootItem = false) :
    ¬ ∃ module, SourceBackedRoot file tokens module := by
  intro sourceRoot
  rcases sourceRoot with
    ⟨_module, memo, correct, final, reached, _complete, _coherent⟩
  let resultCorrect := executeObservedContextualWorklist?_phaseBCorrect
    file tokens owned result selected
  let resultFinal := Chart.executeObservedContextualWorklist?_allGuardsFinal
    file tokens owned result selected
  have memoEq : memo = result.memo :=
    phaseBCorrect_final_memo_unique
      correct final resultCorrect resultFinal
  subst memo
  have reachedResult : ContextualReach file tokens result.memo
      resultCorrect resultFinal
      (CanonicalCompleteRootItem tokens .module
        (Boundary.start tokens) (Boundary.afterLogicalEOF tokens) .plain) :=
    reached
  have correspondence :=
    executeObservedContextualWorklist?_correspondence
      file tokens owned result selected
  have rootMember : CanonicalCompleteRootItem tokens .module
      (Boundary.start tokens) (Boundary.afterLogicalEOF tokens) .plain ∈
        result.items :=
    (correspondence.1 _).mpr reachedResult
  have present :=
    (Chart.ContextualWorklistResult.containsCompleteModuleRootItem_eq_true_iff
      result).mpr rootMember
  rw [absent] at present
  contradiction

/-- Once the completed module root is absent, an executable ordinary
diagnostic candidate needs only the G10 exclusion premise to become a fully
certified parser diagnostic. -/
theorem executeObservedContextualWorklist?_unexpectedDiagnosticCandidate?_applies_of_completeModuleRootItem_eq_false
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result)
    (span : SourceSpan) (found : Found)
    (expected : NonemptyList Expected)
    (candidate : result.unexpectedDiagnosticCandidate? file =
      some (.unexpected span found expected))
    (absent : result.containsCompleteModuleRootItem = false)
    (notRepeated : ∀ cursor level operator,
      ¬ RepeatedNonAssociativeAt file tokens result.memo
        (executeObservedContextualWorklist?_phaseBCorrect
          file tokens owned result selected)
        (Chart.executeObservedContextualWorklist?_allGuardsFinal
          file tokens owned result selected)
        cursor level operator) :
    ParseDiagnostic.Applies file tokens
      (.unexpected span found expected) := by
  let correct := executeObservedContextualWorklist?_phaseBCorrect
    file tokens owned result selected
  let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
    file tokens owned result selected
  rcases
      (executeObservedContextualWorklist?_unexpectedDiagnosticCandidate?_eq_some_iff
        file tokens owned result selected span found expected).mp candidate with
    ⟨cursor, greatest, canonical, foundAt⟩
  exact .unexpected file tokens result.memo correct final cursor span found
    expected
    (executeObservedContextualWorklist?_noSourceBackedRoot_of_completeModuleRootItem_eq_false
      file tokens owned result selected absent)
    greatest canonical foundAt (notRepeated cursor)

/-- The rootless ordinary branch supplies root absence itself; only exclusion
of a repeated non-associative candidate remains to certify its result. -/
theorem executeObservedContextualWorklist?_rootlessUnexpectedDiagnosticCandidate?_applies
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result)
    (span : SourceSpan) (found : Found)
    (expected : NonemptyList Expected)
    (candidate : result.rootlessUnexpectedDiagnosticCandidate? file =
      some (.unexpected span found expected))
    (notRepeated : ∀ cursor level operator,
      ¬ RepeatedNonAssociativeAt file tokens result.memo
        (executeObservedContextualWorklist?_phaseBCorrect
          file tokens owned result selected)
        (Chart.executeObservedContextualWorklist?_allGuardsFinal
          file tokens owned result selected)
        cursor level operator) :
    ParseDiagnostic.Applies file tokens
      (.unexpected span found expected) := by
  rcases
      (Chart.ContextualWorklistResult.rootlessUnexpectedDiagnosticCandidate?_eq_some_iff
        file result (.unexpected span found expected)).mp candidate with
    ⟨absent, ordinary⟩
  exact
    executeObservedContextualWorklist?_unexpectedDiagnosticCandidate?_applies_of_completeModuleRootItem_eq_false
      file tokens owned result selected span found expected ordinary absent
        notRepeated

end Solcore.Surface.Multi
namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

/-- Chart's raw nonassociative-operator observation is exactly the
declarative matched-terminal relation. -/
theorem chart_observedNonAssociativeOperatorAt?_eq_some_iff
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (boundary : Boundary tokens)
    (observation : Chart.NonAssociativeOperatorObservation) :
    Chart.observedNonAssociativeOperatorAt? file tokens boundary =
        some observation ↔
      FoundNonAssociativeOperatorAt file tokens boundary
        observation.level observation.operator := by
  rcases observation with ⟨observedLevel, observedOperator⟩
  unfold Chart.observedNonAssociativeOperatorAt?
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨found, foundEq, classified⟩
    unfold Chart.observedFoundAt? at foundEq
    split at foundEq <;> rename_i inRange
    · simp only [Option.some.injEq] at foundEq
      cases foundEq
      let cursor : TerminalCursor tokens := ⟨boundary.val, by omega⟩
      have atBoundary : cursor.beforeBoundary = boundary := Fin.ext rfl
      let token := tokens[boundary.val]
      have terminalAt : TerminalAt file tokens cursor (.retained token)
          token.span := .retained cursor token inRange
            (List.getElem?_eq_getElem inRange)
            (owned token (List.getElem_mem inRange))
      cases payloadEq : token.payload
      all_goals simp only [token] at payloadEq
      all_goals rw [payloadEq] at classified
      all_goals try simp at classified
      next symbol =>
        cases symbol <;> simp at classified
        all_goals
          rcases classified with ⟨rfl, rfl⟩
          first
          | exact FoundNonAssociativeOperatorAt.less {
              cursor := cursor
              value := .retained token
              span := token.span
              «at» := terminalAt
              «matches» := by
                simpa only [TerminalMatches] using payloadEq
            } atBoundary
          | exact FoundNonAssociativeOperatorAt.greater {
              cursor := cursor
              value := .retained token
              span := token.span
              «at» := terminalAt
              «matches» := by
                simpa only [TerminalMatches] using payloadEq
            } atBoundary
          | exact FoundNonAssociativeOperatorAt.lessEqual {
              cursor := cursor
              value := .retained token
              span := token.span
              «at» := terminalAt
              «matches» := by
                simpa only [TerminalMatches] using payloadEq
            } atBoundary
          | exact FoundNonAssociativeOperatorAt.greaterEqual {
              cursor := cursor
              value := .retained token
              span := token.span
              «at» := terminalAt
              «matches» := by
                simpa only [TerminalMatches] using payloadEq
            } atBoundary
          | exact FoundNonAssociativeOperatorAt.equal {
              cursor := cursor
              value := .retained token
              span := token.span
              «at» := terminalAt
              «matches» := by
                simpa only [TerminalMatches] using payloadEq
            } atBoundary
          | exact FoundNonAssociativeOperatorAt.notEqual {
              cursor := cursor
              value := .retained token
              span := token.span
              «at» := terminalAt
              «matches» := by
                simpa only [TerminalMatches] using payloadEq
            } atBoundary
    · split at foundEq
      · simp only [Option.some.injEq] at foundEq
        cases foundEq
        simp at classified
      · contradiction
  · intro found
    cases found with
    | less terminal atCursor =>
        cases terminal with
        | mk cursor value span terminalAt matchedEvidence =>
            cases value with
            | retained token =>
                have payloadEq : token.payload = .symbol .less :=
                  matchedEvidence
                cases terminalAt with
                | retained _ retainedInRange lookup valid =>
                  have rebuilt : TerminalAt file tokens cursor
                      (.retained token) token.span :=
                    .retained cursor token retainedInRange lookup valid
                  have foundAt : FoundAt file tokens boundary token.span
                    (.token (.symbol .less)) := by
                    simpa only [payloadEq] using
                      FoundAt.retained cursor boundary token atCursor rebuilt
                  have observed := (chart_observedFoundAt?_eq_some_iff
                    owned boundary {
                      span := token.span
                      found := .token (.symbol .less)
                    }).mpr foundAt
                  exact ⟨_, observed, by
                    simp [RuleReduction.terminalLoc]⟩
            | endOfFile => simp [TerminalMatches] at matchedEvidence
    | greater terminal atCursor =>
        cases terminal with
        | mk cursor value span terminalAt matchedEvidence =>
            cases value with
            | retained token =>
                have payloadEq : token.payload = .symbol .greater :=
                  matchedEvidence
                cases terminalAt with
                | retained _ retainedInRange lookup valid =>
                  have rebuilt : TerminalAt file tokens cursor
                      (.retained token) token.span :=
                    .retained cursor token retainedInRange lookup valid
                  have foundAt : FoundAt file tokens boundary token.span
                    (.token (.symbol .greater)) := by
                    simpa only [payloadEq] using
                      FoundAt.retained cursor boundary token atCursor rebuilt
                  have observed := (chart_observedFoundAt?_eq_some_iff
                    owned boundary {
                      span := token.span
                      found := .token (.symbol .greater)
                    }).mpr foundAt
                  exact ⟨_, observed, by
                    simp [RuleReduction.terminalLoc]⟩
            | endOfFile => simp [TerminalMatches] at matchedEvidence
    | lessEqual terminal atCursor =>
        cases terminal with
        | mk cursor value span terminalAt matchedEvidence =>
            cases value with
            | retained token =>
                have payloadEq : token.payload = .symbol .lessEqual :=
                  matchedEvidence
                cases terminalAt with
                | retained _ retainedInRange lookup valid =>
                  have rebuilt : TerminalAt file tokens cursor
                      (.retained token) token.span :=
                    .retained cursor token retainedInRange lookup valid
                  have foundAt : FoundAt file tokens boundary token.span
                    (.token (.symbol .lessEqual)) := by
                    simpa only [payloadEq] using
                      FoundAt.retained cursor boundary token atCursor rebuilt
                  have observed := (chart_observedFoundAt?_eq_some_iff
                    owned boundary {
                      span := token.span
                      found := .token (.symbol .lessEqual)
                    }).mpr foundAt
                  exact ⟨_, observed, by
                    simp [RuleReduction.terminalLoc]⟩
            | endOfFile => simp [TerminalMatches] at matchedEvidence
    | greaterEqual terminal atCursor =>
        cases terminal with
        | mk cursor value span terminalAt matchedEvidence =>
            cases value with
            | retained token =>
                have payloadEq : token.payload = .symbol .greaterEqual :=
                  matchedEvidence
                cases terminalAt with
                | retained _ retainedInRange lookup valid =>
                  have rebuilt : TerminalAt file tokens cursor
                      (.retained token) token.span :=
                    .retained cursor token retainedInRange lookup valid
                  have foundAt : FoundAt file tokens boundary token.span
                    (.token (.symbol .greaterEqual)) := by
                    simpa only [payloadEq] using
                      FoundAt.retained cursor boundary token atCursor rebuilt
                  have observed := (chart_observedFoundAt?_eq_some_iff
                    owned boundary {
                      span := token.span
                      found := .token (.symbol .greaterEqual)
                    }).mpr foundAt
                  exact ⟨_, observed, by
                    simp [RuleReduction.terminalLoc]⟩
            | endOfFile => simp [TerminalMatches] at matchedEvidence
    | equal terminal atCursor =>
        cases terminal with
        | mk cursor value span terminalAt matchedEvidence =>
            cases value with
            | retained token =>
                have payloadEq : token.payload = .symbol .equalEqual :=
                  matchedEvidence
                cases terminalAt with
                | retained _ retainedInRange lookup valid =>
                  have rebuilt : TerminalAt file tokens cursor
                      (.retained token) token.span :=
                    .retained cursor token retainedInRange lookup valid
                  have foundAt : FoundAt file tokens boundary token.span
                    (.token (.symbol .equalEqual)) := by
                    simpa only [payloadEq] using
                      FoundAt.retained cursor boundary token atCursor rebuilt
                  have observed := (chart_observedFoundAt?_eq_some_iff
                    owned boundary {
                      span := token.span
                      found := .token (.symbol .equalEqual)
                    }).mpr foundAt
                  exact ⟨_, observed, by
                    simp [RuleReduction.terminalLoc]⟩
            | endOfFile => simp [TerminalMatches] at matchedEvidence
    | notEqual terminal atCursor =>
        cases terminal with
        | mk cursor value span terminalAt matchedEvidence =>
            cases value with
            | retained token =>
                have payloadEq : token.payload = .symbol .notEqual :=
                  matchedEvidence
                cases terminalAt with
                | retained _ retainedInRange lookup valid =>
                  have rebuilt : TerminalAt file tokens cursor
                      (.retained token) token.span :=
                    .retained cursor token retainedInRange lookup valid
                  have foundAt : FoundAt file tokens boundary token.span
                    (.token (.symbol .notEqual)) := by
                    simpa only [payloadEq] using
                      FoundAt.retained cursor boundary token atCursor rebuilt
                  have observed := (chart_observedFoundAt?_eq_some_iff
                    owned boundary {
                      span := token.span
                      found := .token (.symbol .notEqual)
                    }).mpr foundAt
                  exact ⟨_, observed, by
                    simp [RuleReduction.terminalLoc]⟩
            | endOfFile => simp [TerminalMatches] at matchedEvidence


end Solcore.Surface.Multi
namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

/-- At a selected greatest cursor, the canonical retained root list is
exactly the declarative nonassociative root frontier. -/
theorem executeObservedContextualWorklist?_nonAssociativeRootItemsAt_mem_iff
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result)
    (cursor : Boundary tokens)
    (greatestSelected : result.greatestCurrent? = some cursor)
    (level : NonAssociativeLevel)
    (item : ContextualItemKey tokens) :
    item ∈ result.nonAssociativeRootItemsAt cursor level ↔
      item = CanonicalCompleteRootItem tokens
          (Chart.nonAssociativeRootRule level)
          item.raw.origin cursor item.context ∧
        let correct := executeObservedContextualWorklist?_phaseBCorrect
          file tokens owned result selected
        let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
          file tokens owned result selected
        FrontierReach file tokens result.memo correct final cursor item := by
  let correct := executeObservedContextualWorklist?_phaseBCorrect
    file tokens owned result selected
  let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
    file tokens owned result selected
  change item ∈ result.nonAssociativeRootItemsAt cursor level ↔
    item = CanonicalCompleteRootItem tokens
        (Chart.nonAssociativeRootRule level)
        item.raw.origin cursor item.context ∧
      FrontierReach file tokens result.memo correct final cursor item
  have greatest : GreatestReachableCursor
      file tokens result.memo correct final cursor :=
    (executeObservedContextualWorklist?_greatestCurrent?_eq_some_iff
      file tokens owned result selected cursor).mp greatestSelected
  have correspondence := executeObservedContextualWorklist?_correspondence
    file tokens owned result selected
  change
    (∀ candidate, candidate ∈ result.items ↔
      ContextualReach file tokens result.memo correct final candidate) ∧ _
      at correspondence
  rw [Chart.ContextualWorklistResult.nonAssociativeRootItemsAt_mem_iff]
  constructor
  · rintro ⟨member, rootEq⟩
    exact ⟨rootEq, greatest,
      (correspondence.1 item).mp member,
      congrArg (fun candidate => candidate.raw.current) rootEq⟩
  · rintro ⟨rootEq, frontier⟩
    exact ⟨(correspondence.1 item).mpr frontier.2.1, rootEq⟩

/-- Stable declarative enumeration of all reached canonical complete roots at
one nonassociative level. -/
def canonicalNonAssociativeRootItems
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (cursor : Boundary tokens)
    (level : NonAssociativeLevel) : List (ContextualItemKey tokens) :=
  (allContextualItems tokens).filter fun item =>
    @decide (ContextualReach file tokens memo correct final item)
        (contextualReachDecision owned correct final item) &&
      Chart.isNonAssociativeRootItemAt cursor level item

/-- Membership in the canonical declarative list is exactly one reached
canonical complete-root coordinate. -/
theorem canonicalNonAssociativeRootItems_mem_iff
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (cursor : Boundary tokens)
    (level : NonAssociativeLevel)
    (item : ContextualItemKey tokens) :
    item ∈ canonicalNonAssociativeRootItems
        owned correct final cursor level ↔
      ContextualReach file tokens memo correct final item ∧
        item = CanonicalCompleteRootItem tokens
          (Chart.nonAssociativeRootRule level)
          item.raw.origin cursor item.context := by
  simp [canonicalNonAssociativeRootItems,
    Chart.isNonAssociativeRootItemAt, allContextualItems_complete]

/-- Successful execution computes exactly the stable declarative root list at
its selected greatest cursor. -/
theorem executeObservedContextualWorklist?_nonAssociativeRootItemsAt_eq_canonical
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result)
    (cursor : Boundary tokens)
    (level : NonAssociativeLevel) :
    result.nonAssociativeRootItemsAt cursor level =
      canonicalNonAssociativeRootItems owned
        (executeObservedContextualWorklist?_phaseBCorrect
          file tokens owned result selected)
        (Chart.executeObservedContextualWorklist?_allGuardsFinal
          file tokens owned result selected)
        cursor level := by
  let correct := executeObservedContextualWorklist?_phaseBCorrect
    file tokens owned result selected
  let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
    file tokens owned result selected
  change result.nonAssociativeRootItemsAt cursor level =
    canonicalNonAssociativeRootItems owned correct final cursor level
  have correspondence := executeObservedContextualWorklist?_correspondence
    file tokens owned result selected
  change
    (∀ item, item ∈ result.items ↔
      ContextualReach file tokens result.memo correct final item) ∧ _
      at correspondence
  unfold Chart.ContextualWorklistResult.nonAssociativeRootItemsAt
  unfold canonicalNonAssociativeRootItems
  apply List.filter_congr
  intro item _member
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,
    Chart.ContextualWorklistResult.containsRetainedContextualItem_eq_true_iff,
    decide_eq_true_iff]
  exact and_congr (correspondence.1 item) Iff.rfl

/-- The selected structural G10 frontier is exactly the greatest declarative
cursor, its matched nonassociative operator, and the canonical reached root
list for that same level. -/
theorem executeObservedContextualWorklist?_nonAssociativeFrontierCandidates?_eq_some_iff
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result)
    (frontier : Chart.NonAssociativeFrontierCandidates tokens) :
    result.nonAssociativeFrontierCandidates? file = some frontier ↔
      let correct := executeObservedContextualWorklist?_phaseBCorrect
        file tokens owned result selected
      let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
        file tokens owned result selected
      GreatestReachableCursor
          file tokens result.memo correct final frontier.cursor ∧
        FoundNonAssociativeOperatorAt file tokens frontier.cursor
          frontier.level frontier.operator ∧
        frontier.roots = canonicalNonAssociativeRootItems
          owned correct final frontier.cursor frontier.level := by
  let correct := executeObservedContextualWorklist?_phaseBCorrect
    file tokens owned result selected
  let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
    file tokens owned result selected
  change result.nonAssociativeFrontierCandidates? file = some frontier ↔
    GreatestReachableCursor
        file tokens result.memo correct final frontier.cursor ∧
      FoundNonAssociativeOperatorAt file tokens frontier.cursor
        frontier.level frontier.operator ∧
      frontier.roots = canonicalNonAssociativeRootItems
        owned correct final frontier.cursor frontier.level
  rw [Chart.ContextualWorklistResult.nonAssociativeFrontierCandidates?_eq_some_iff]
  rw [executeObservedContextualWorklist?_greatestCurrent?_eq_some_iff
    file tokens owned result selected frontier.cursor]
  rw [chart_observedNonAssociativeOperatorAt?_eq_some_iff
    owned frontier.cursor]
  rw [executeObservedContextualWorklist?_nonAssociativeRootItemsAt_eq_canonical
      file tokens owned result selected frontier.cursor frontier.level]

/-- Exact factorization of the declarative G10 witness through the proof-free
structural frontier.  Only the semantic completed/group tests remain carried
by the declarative candidate until executable root values land. -/
theorem executeObservedContextualWorklist?_repeatedNonAssociativeAt_iff_frontierCandidates
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result)
    (cursor : Boundary tokens)
    (level : NonAssociativeLevel)
    (operator : Located InfixOperator) :
    let correct := executeObservedContextualWorklist?_phaseBCorrect
      file tokens owned result selected
    let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
      file tokens owned result selected
    RepeatedNonAssociativeAt file tokens result.memo correct final
        cursor level operator ↔
      ∃ frontier : Chart.NonAssociativeFrontierCandidates tokens,
        result.nonAssociativeFrontierCandidates? file = some frontier ∧
        frontier.cursor = cursor ∧
        frontier.level = level ∧
        frontier.operator = operator ∧
        ∃ candidate : NonAssociativeFrontierValue
            file tokens result.memo correct final cursor level,
          CanonicalCompleteRootItem tokens
              (Chart.nonAssociativeRootRule level)
              candidate.origin cursor candidate.context ∈ frontier.roots ∧
          ∃ first : Located InfixOperator,
            CompletedNonAssociative level candidate first ∧
            ¬ ExplicitGroupBoundary level candidate := by
  let correct := executeObservedContextualWorklist?_phaseBCorrect
    file tokens owned result selected
  let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
    file tokens owned result selected
  change RepeatedNonAssociativeAt file tokens result.memo correct final
      cursor level operator ↔
    ∃ frontier : Chart.NonAssociativeFrontierCandidates tokens,
      result.nonAssociativeFrontierCandidates? file = some frontier ∧
      frontier.cursor = cursor ∧
      frontier.level = level ∧
      frontier.operator = operator ∧
      ∃ candidate : NonAssociativeFrontierValue
          file tokens result.memo correct final cursor level,
        CanonicalCompleteRootItem tokens
            (Chart.nonAssociativeRootRule level)
            candidate.origin cursor candidate.context ∈ frontier.roots ∧
        ∃ first : Located InfixOperator,
          CompletedNonAssociative level candidate first ∧
          ¬ ExplicitGroupBoundary level candidate
  constructor
  · rintro ⟨candidate, first, completed, ungrouped, found⟩
    let frontier : Chart.NonAssociativeFrontierCandidates tokens := {
      cursor := cursor
      level := level
      operator := operator
      roots := canonicalNonAssociativeRootItems
        owned correct final cursor level
    }
    have frontierEq : result.nonAssociativeFrontierCandidates? file =
        some frontier :=
      (executeObservedContextualWorklist?_nonAssociativeFrontierCandidates?_eq_some_iff
          file tokens owned result selected frontier).mpr
        ⟨candidate.frontier.1, found, rfl⟩
    have rootMember : CanonicalCompleteRootItem tokens
        (Chart.nonAssociativeRootRule level)
        candidate.origin cursor candidate.context ∈ frontier.roots := by
      change CanonicalCompleteRootItem tokens
          (Chart.nonAssociativeRootRule level)
          candidate.origin cursor candidate.context ∈
        canonicalNonAssociativeRootItems
          owned correct final cursor level
      apply (canonicalNonAssociativeRootItems_mem_iff
        owned correct final cursor level _).mpr
      exact ⟨candidate.root.1, rfl⟩
    exact ⟨frontier, frontierEq, rfl, rfl, rfl,
      candidate, rootMember, first, completed, ungrouped⟩
  · rintro ⟨frontier, frontierEq, cursorEq, levelEq, operatorEq,
      candidate, _rootMember, first, completed, ungrouped⟩
    have exactFrontier :=
      (executeObservedContextualWorklist?_nonAssociativeFrontierCandidates?_eq_some_iff
          file tokens owned result selected frontier).mp frontierEq
    have found : FoundNonAssociativeOperatorAt
        file tokens cursor level operator := by
      simpa only [cursorEq, levelEq, operatorEq] using exactFrontier.2.1
    exact ⟨candidate, first, completed, ungrouped, found⟩

end Solcore.Surface.Multi

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

/-- On successful execution, the proof-free root-shape bit is exactly the
declarative pair of completions selecting a present outer optional. -/
theorem executeObservedContextualWorklist?_completedNonAssociativeRootBool_eq_true_iff_edges
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result)
    (root : ContextualItemKey tokens) :
    result.completedNonAssociativeRootBool root = true ↔
      let correct := executeObservedContextualWorklist?_phaseBCorrect
        file tokens owned result selected
      let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
        file tokens owned result selected
      ∃ rootWaiting sequence rootShared,
        ContextualEdgeReach file tokens result.memo correct final
          (.completed rootWaiting sequence root rootShared) ∧
        ∃ sequenceWaiting optional optionalShared site,
          ContextualEdgeReach file tokens result.memo correct final
            (.completed sequenceWaiting optional sequence optionalShared) ∧
          optional.raw.production = .opt site .some := by
  let correct := executeObservedContextualWorklist?_phaseBCorrect
    file tokens owned result selected
  let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
    file tokens owned result selected
  change Chart.retainedRootHasPresentOptional result.edges root = true ↔
    ∃ rootWaiting sequence rootShared,
      ContextualEdgeReach file tokens result.memo correct final
        (.completed rootWaiting sequence root rootShared) ∧
      ∃ sequenceWaiting optional optionalShared site,
        ContextualEdgeReach file tokens result.memo correct final
          (.completed sequenceWaiting optional sequence optionalShared) ∧
        optional.raw.production = .opt site .some
  have correspondence := executeObservedContextualWorklist?_correspondence
    file tokens owned result selected
  change
    (∀ item, item ∈ result.items ↔
      ContextualReach file tokens result.memo correct final item) ∧
    (∀ key, (∃ retained, retained ∈ result.edges ∧ retained.val = key) ↔
      ContextualEdgeReach file tokens result.memo correct final key) ∧
    CompletionBackpointerUnique file tokens result.memo correct final
      at correspondence
  rw [Chart.retainedRootHasPresentOptional_eq_true_iff]
  constructor
  · rintro ⟨rootEdge, rootMember, rootWaiting, sequence, rootShared,
      rootShape, optionalEdge, optionalMember, sequenceWaiting, optional,
      optionalShared, site, optionalShape, production⟩
    exact ⟨rootWaiting, sequence, rootShared,
      (correspondence.2.1 _).mp ⟨rootEdge, rootMember, rootShape⟩,
      sequenceWaiting, optional, optionalShared, site,
      (correspondence.2.1 _).mp
        ⟨optionalEdge, optionalMember, optionalShape⟩,
      production⟩
  · rintro ⟨rootWaiting, sequence, rootShared, rootReached,
      sequenceWaiting, optional, optionalShared, site, optionalReached,
      production⟩
    obtain ⟨rootEdge, rootMember, rootShape⟩ :=
      (correspondence.2.1 _).mpr rootReached
    obtain ⟨optionalEdge, optionalMember, optionalShape⟩ :=
      (correspondence.2.1 _).mpr optionalReached
    exact ⟨rootEdge, rootMember, rootWaiting, sequence, rootShared,
      rootShape, optionalEdge, optionalMember, sequenceWaiting, optional,
      optionalShared, site, optionalShape, production⟩

end Solcore.Surface.Multi
namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

/-- The proof-free present-optional root bit of one executed coherent
nonassociative candidate forces a completed source operator value. -/
theorem executeObservedContextualWorklist?_completedNonAssociativeRootBool_eq_true_implies_completed
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : Chart.ContextualWorklistResult file tokens)
    (selected : Chart.executeObservedContextualWorklist? file tokens owned =
      some result)
    (cursor : Boundary tokens) (level : NonAssociativeLevel) :
    let correct := executeObservedContextualWorklist?_phaseBCorrect
      file tokens owned result selected
    let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
      file tokens owned result selected
    ∀ candidate : NonAssociativeFrontierValue file tokens result.memo
        correct final cursor level,
      result.completedNonAssociativeRootBool
          (CanonicalCompleteRootItem tokens level.rule candidate.origin
            cursor candidate.context) = true →
        ∃ first, CompletedNonAssociative level candidate first := by
  let correct := executeObservedContextualWorklist?_phaseBCorrect
    file tokens owned result selected
  let final := Chart.executeObservedContextualWorklist?_allGuardsFinal
    file tokens owned result selected
  change ∀ candidate : NonAssociativeFrontierValue file tokens result.memo
      correct final cursor level,
    result.completedNonAssociativeRootBool
        (CanonicalCompleteRootItem tokens level.rule candidate.origin cursor
          candidate.context) = true →
      ∃ first, CompletedNonAssociative level candidate first
  intro candidate marked
  let root := CanonicalCompleteRootItem tokens level.rule candidate.origin
    cursor candidate.context
  have edgeShape :=
    (executeObservedContextualWorklist?_completedNonAssociativeRootBool_eq_true_iff_edges
      file tokens owned result selected root).mp marked
  rcases edgeShape with ⟨rootWaiting, sequence, rootShared, rootReached,
    sequenceWaiting, optional, optionalShared, site, optionalReached,
    optionalProduction⟩
  have correspondence := executeObservedContextualWorklist?_correspondence
    file tokens owned result selected
  obtain ⟨first, completed⟩ := g10CompletedValue_of_presentCompletionEdges
    correspondence.2.2 candidate.root.2.2 rootReached optionalReached
      optionalProduction
  exact ⟨first,
    (completedNonAssociative_iff_value level candidate first).mpr completed⟩

end Solcore.Surface.Multi
