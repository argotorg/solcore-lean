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

end Solcore.Surface.Multi
