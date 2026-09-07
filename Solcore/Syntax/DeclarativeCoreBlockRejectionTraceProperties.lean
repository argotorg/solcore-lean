import Solcore.Syntax.DeclarativeCoreBlockRejectionTraceGrammar
import Solcore.Syntax.DeclarativeCoreBlockTraceProperties
import Solcore.Syntax.DeclarativeRejectionDiagnosticProperties

/-! Exact raw-block rejection traces and exclusion of successful traces.
All functionality assumptions belong to the abstract statement judgments;
fixed source/byte context determines primitive brace reports independently. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
    Remainder → List ParseDiagnostic → Prop}
  {statementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
  {ordinaryRejects : Remainder → Remainder → Prop}
  {source : SourceId} {endByte : Nat} {policy : CoreBlockTailPolicy}

/-- Erasure preserves the exact first rejecting statement/closing stage. -/
theorem CoreBlockItemsTraceRejects.ordinary
    (successErases : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        statementOrdinary input statement output)
    (rejectErases : ∀ {input rejected diagnostic trace},
      statementRejects source endByte input rejected diagnostic trace → ordinaryRejects input rejected)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : CoreBlockItemsTraceRejects statementTrace statementRejects source endByte
      input rejected diagnostic trace) :
    CoreBlockItemsRejects statementOrdinary ordinaryRejects input rejected := by
  induction rejection with
  | missingClose absent atEnd reported => exact .missingClose absent atEnd
  | statementRejected inside absent statement =>
      exact .statementRejected inside absent (rejectErases statement)
  | laterRejected inside absent statement progress tail ih =>
      exact .laterRejected inside absent (successErases statement) progress ih

/-- A raw-block rejection refines its established ordinary rejection grammar. -/
theorem CoreBlockTraceRejects.ordinary
    (successErases : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        statementOrdinary input statement output)
    (rejectErases : ∀ {input rejected diagnostic trace},
      statementRejects source endByte input rejected diagnostic trace → ordinaryRejects input rejected)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : CoreBlockTraceRejects statementTrace statementRejects policy source endByte
      input rejected diagnostic trace) :
    CoreBlockRejects statementOrdinary ordinaryRejects policy input rejected := by
  cases rejection with
  | openingMissing absent reported => exact .openingMissing absent
  | itemsRejected span opening items =>
      exact .itemsRejected span opening (items.ordinary successErases rejectErases)

/-- Tail policy cannot change a rejection that returns before tail validation. -/
theorem CoreBlockTraceRejects.withPolicy
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : CoreBlockTraceRejects statementTrace statementRejects policy source endByte
      input rejected diagnostic trace) (otherPolicy : CoreBlockTailPolicy) :
    CoreBlockTraceRejects statementTrace statementRejects otherPolicy source endByte
      input rejected diagnostic trace := by
  cases rejection with
  | openingMissing absent reported => exact .openingMissing absent reported
  | itemsRejected span opening items => exact .itemsRejected span opening items

variable
  (successUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
    statementTrace source endByte input left afterLeft leftTrace →
    statementTrace source endByte input right afterRight rightTrace →
      left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
  (rejectUnique : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
    statementRejects source endByte input afterLeft leftReport leftTrace →
    statementRejects source endByte input afterRight rightReport rightTrace →
      afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace)
  (disjoint : ∀ {input rejected diagnostic trace},
    statementRejects source endByte input rejected diagnostic trace →
      ¬ ∃ statement output events, statementTrace source endByte input statement output events)

include successUnique rejectUnique disjoint in
/-- The first rejecting endpoint, full report, and ordered preceding events
are unique; at-end and next-statement branches cannot compete. -/
theorem CoreBlockItemsTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : CoreBlockItemsTraceRejects statementTrace statementRejects source endByte
      input afterLeft leftReport leftTrace)
    (right : CoreBlockItemsTraceRejects statementTrace statementRejects source endByte
      input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  induction left generalizing afterRight rightReport rightTrace with
  | missingClose absent atEnd reported =>
      cases right with
      | missingClose _ _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | statementRejected inside _ _ | laterRejected inside _ _ _ _ =>
          exact False.elim (Nat.not_lt_of_ge atEnd inside)
  | statementRejected inside absent statement =>
      cases right with
      | missingClose _ atEnd _ => exact False.elim (Nat.not_lt_of_ge atEnd inside)
      | statementRejected _ _ other => exact rejectUnique statement other
      | laterRejected _ _ other _ _ => exact False.elim (disjoint statement ⟨_, _, _, other⟩)
  | laterRejected inside absent statement progress tail ih =>
      cases right with
      | missingClose _ atEnd _ => exact False.elim (Nat.not_lt_of_ge atEnd inside)
      | statementRejected _ _ other => exact False.elim (disjoint other ⟨_, _, _, statement⟩)
      | laterRejected _ _ other _ otherTail =>
          rcases successUnique statement other with ⟨rfl, rfl, rfl⟩
          rcases ih otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

include successUnique rejectUnique disjoint in
/-- Exact opening recognition and exact item rejection fix the full result.
No delayed validation trace is present in either rejecting branch. -/
theorem CoreBlockTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : CoreBlockTraceRejects statementTrace statementRejects policy source endByte
      input afterLeft leftReport leftTrace)
    (right : CoreBlockTraceRejects statementTrace statementRejects policy source endByte
      input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | openingMissing absent reported =>
      cases right with
      | openingMissing _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | itemsRejected span opening _ => exact False.elim (absent ⟨span, opening.1⟩)
  | itemsRejected span opening items =>
      cases right with
      | openingMissing absent _ => exact False.elim (absent ⟨span, opening.1⟩)
      | itemsRejected otherSpan otherOpening otherItems =>
          cases opening.output_unique otherOpening
          exact items.result_unique successUnique rejectUnique disjoint otherItems

include successUnique disjoint in
/-- A rejected item chain excludes every successful closing chain, regardless
of what later block-tail validation would have reported. -/
theorem CoreBlockItemsTraceRejects.disjoint_success
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : CoreBlockItemsTraceRejects statementTrace statementRejects source endByte
      input rejected diagnostic trace) :
    ¬ ∃ statements closingSpan output events,
      CoreBlockItemsTraceParses statementTrace source endByte input statements closingSpan output events := by
  induction rejection with
  | missingClose absent atEnd reported =>
      rintro ⟨_, _, _, _, parsed⟩
      cases parsed with
      | close span token => exact absent ⟨_, token.1⟩
      | next inside _ _ _ _ => exact Nat.not_lt_of_ge atEnd inside
  | statementRejected inside absent statement =>
      rintro ⟨_, _, _, _, parsed⟩
      cases parsed with
      | close span token => exact absent ⟨_, token.1⟩
      | next _ _ other _ _ => exact disjoint statement ⟨_, _, _, other⟩
  | laterRejected inside absent statement progress tail ih =>
      rintro ⟨_, _, _, _, parsed⟩
      cases parsed with
      | close span token => exact absent ⟨_, token.1⟩
      | next _ _ other _ otherTail =>
          cases (successUnique statement other).2.1
          exact ih ⟨_, _, _, _, otherTail⟩

include successUnique disjoint in
/-- An exact raw rejection excludes all full successful traces. -/
theorem CoreBlockTraceRejects.disjoint_success
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : CoreBlockTraceRejects statementTrace statementRejects policy source endByte
      input rejected diagnostic trace) :
    ¬ ∃ body output events,
      CoreBlockTraceParses statementTrace policy source endByte input body output events := by
  rintro ⟨_, _, _, parsed⟩
  cases rejection with
  | openingMissing absent reported =>
      cases parsed with
      | parsed opening closing token items validated => exact absent ⟨opening, token.1⟩
  | itemsRejected span opening items =>
      cases parsed with
      | parsed otherOpening closing token otherItems validated =>
          cases opening.output_unique token
          exact items.disjoint_success successUnique disjoint ⟨_, _, _, _, otherItems⟩

end Solcore.Syntax.DeclarativeGrammar
