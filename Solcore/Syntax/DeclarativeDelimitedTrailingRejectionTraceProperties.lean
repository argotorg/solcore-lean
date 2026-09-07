import Solcore.Syntax.DeclarativeDelimitedTrailingRejectionTraceGrammar
import Solcore.Syntax.DeclarativeRejectionDiagnosticProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Ordinary erasure and full rejection functionality for trailing-enabled lists.
All child functionality assumptions remain independent of parser execution. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {α : Type}
  {elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {ordinaryParses : Remainder → α → Remainder → Prop}
  {ordinaryRejects : Remainder → Remainder → Prop}
  {source : SourceId} {endByte : Nat} {opening closing : Symbol} {allowEmpty : Bool} {context : ParseContext}

theorem TrailingDelimitedTailTraceRejects.ordinary
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ordinaryParses input value output)
    (rejectErases : ∀ {input rejected diagnostic trace}, elementRejects source endByte input rejected diagnostic trace →
      ordinaryRejects input rejected)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TrailingDelimitedTailTraceRejects closing context elementTrace elementRejects
      source endByte input rejected diagnostic trace) :
    DelimitedTailRejects closing true ordinaryParses ordinaryRejects input rejected := by
  induction rejection with
  | delimiterMissing commaAbsent closingAbsent reported => exact .delimiterMissing commaAbsent closingAbsent
  | elementRejected commaSpan comma closingAbsent child =>
      rcases comma with ⟨token, rfl⟩
      exact .elementRejected commaSpan token (.absent closingAbsent) (rejectErases child)
  | laterRejected commaSpan comma closingAbsent child progress tail ih =>
      rcases comma with ⟨token, rfl⟩
      exact .laterRejected commaSpan token (.absent closingAbsent) (successErases child) progress ih

theorem TrailingDelimitedListTraceRejects.ordinary
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ordinaryParses input value output)
    (rejectErases : ∀ {input rejected diagnostic trace}, elementRejects source endByte input rejected diagnostic trace →
      ordinaryRejects input rejected)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace elementRejects
      source endByte input rejected diagnostic trace) :
    DelimitedListRejects opening closing allowEmpty true ordinaryParses ordinaryRejects input rejected := by
  cases rejection with
  | openingMissing absent reported => exact .openingMissing absent
  | firstRejected openingSpan opening continues child =>
      rcases opening with ⟨token, rfl⟩
      exact .firstRejected openingSpan token continues (rejectErases child)
  | tailRejected openingSpan opening continues child progress tail =>
      rcases opening with ⟨token, rfl⟩
      exact .tailRejected openingSpan token continues (successErases child) progress
        (tail.ordinary successErases rejectErases)

variable
  (successUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
    elementTrace source endByte input left afterLeft leftTrace →
    elementTrace source endByte input right afterRight rightTrace →
      left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
  (rejectUnique : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
    elementRejects source endByte input afterLeft leftReport leftTrace →
    elementRejects source endByte input afterRight rightReport rightTrace →
      afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace)
  (disjoint : ∀ {input rejected diagnostic trace},
    elementRejects source endByte input rejected diagnostic trace →
      ¬ ∃ value output events, elementTrace source endByte input value output events)

include successUnique rejectUnique disjoint in
theorem TrailingDelimitedTailTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : TrailingDelimitedTailTraceRejects closing context elementTrace elementRejects source endByte
      input afterLeft leftReport leftTrace)
    (right : TrailingDelimitedTailTraceRejects closing context elementTrace elementRejects source endByte
      input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  induction left generalizing afterRight rightReport rightTrace with
  | delimiterMissing commaAbsent closingAbsent reported =>
      cases right with
      | delimiterMissing _ _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | elementRejected span comma _ _ | laterRejected span comma _ _ _ _ =>
          exact False.elim (commaAbsent ⟨span, comma.1⟩)
  | elementRejected span comma closingAbsent child =>
      cases right with
      | delimiterMissing commaAbsent _ _ => exact False.elim (commaAbsent ⟨span, comma.1⟩)
      | elementRejected _ otherComma _ other =>
          cases comma.output_unique otherComma
          exact rejectUnique child other
      | laterRejected _ otherComma _ other _ _ =>
          cases comma.output_unique otherComma
          exact False.elim (disjoint child ⟨_, _, _, other⟩)
  | laterRejected span comma closingAbsent child progress tail ih =>
      cases right with
      | delimiterMissing commaAbsent _ _ => exact False.elim (commaAbsent ⟨span, comma.1⟩)
      | elementRejected _ otherComma _ other =>
          cases comma.output_unique otherComma
          exact False.elim (disjoint other ⟨_, _, _, child⟩)
      | laterRejected _ otherComma _ other _ otherTail =>
          cases comma.output_unique otherComma
          rcases successUnique child other with ⟨rfl, rfl, rfl⟩
          rcases ih otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

include successUnique rejectUnique disjoint in
theorem TrailingDelimitedListTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : TrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace elementRejects
      source endByte input afterLeft leftReport leftTrace)
    (right : TrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace elementRejects
      source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | openingMissing absent reported =>
      cases right with
      | openingMissing _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | firstRejected span opening _ _ | tailRejected span opening _ _ _ _ =>
          exact False.elim (absent ⟨span, opening.1⟩)
  | firstRejected span opening continues child =>
      cases right with
      | openingMissing absent _ => exact False.elim (absent ⟨span, opening.1⟩)
      | firstRejected _ otherOpening _ other =>
          cases opening.output_unique otherOpening
          exact rejectUnique child other
      | tailRejected _ otherOpening _ other _ _ =>
          cases opening.output_unique otherOpening
          exact False.elim (disjoint child ⟨_, _, _, other⟩)
  | tailRejected span opening continues child progress tail =>
      cases right with
      | openingMissing absent _ => exact False.elim (absent ⟨span, opening.1⟩)
      | firstRejected _ otherOpening _ other =>
          cases opening.output_unique otherOpening
          exact False.elim (disjoint other ⟨_, _, _, child⟩)
      | tailRejected _ otherOpening _ other _ otherTail =>
          cases opening.output_unique otherOpening
          rcases successUnique child other with ⟨rfl, rfl, rfl⟩
          rcases tail.result_unique successUnique rejectUnique disjoint otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

include successUnique disjoint in
theorem TrailingDelimitedTailTraceRejects.disjoint_success
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TrailingDelimitedTailTraceRejects closing context elementTrace elementRejects
      source endByte input rejected diagnostic trace) :
    ¬ ∃ values closingSpan output events,
      TrailingDelimitedTailTraceParses closing elementTrace source endByte input values closingSpan output events := by
  induction rejection with
  | delimiterMissing commaAbsent closingAbsent reported =>
      rintro ⟨_, _, _, _, parsed⟩
      cases parsed with
      | close _ token => exact closingAbsent ⟨_, token.1⟩
      | trailing span comma _ | next span comma _ _ _ _ => exact commaAbsent ⟨span, comma.1⟩
  | elementRejected span comma closingAbsent child =>
      rintro ⟨_, _, _, _, parsed⟩
      cases parsed with
      | close commaAbsent _ => exact commaAbsent ⟨span, comma.1⟩
      | trailing _ otherComma closing =>
          cases comma.output_unique otherComma
          exact closingAbsent ⟨_, closing.1⟩
      | next _ otherComma _ other _ _ =>
          cases comma.output_unique otherComma
          exact disjoint child ⟨_, _, _, other⟩
  | laterRejected span comma closingAbsent child progress tail ih =>
      rintro ⟨_, _, _, _, parsed⟩
      cases parsed with
      | close commaAbsent _ => exact commaAbsent ⟨span, comma.1⟩
      | trailing _ otherComma closing =>
          cases comma.output_unique otherComma
          exact closingAbsent ⟨_, closing.1⟩
      | next _ otherComma _ other _ otherTail =>
          cases comma.output_unique otherComma
          cases (successUnique child other).2.1
          exact ih ⟨_, _, _, _, otherTail⟩

include successUnique disjoint in
theorem TrailingDelimitedListTraceRejects.disjoint_success
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace elementRejects
      source endByte input rejected diagnostic trace) :
    ¬ ∃ values output events,
      TrailingDelimitedListTraceParses opening closing allowEmpty elementTrace source endByte input values output events := by
  rintro ⟨_, _, _, parsed⟩
  cases rejection with
  | openingMissing absent reported =>
      cases parsed with
      | empty span _ _ token _ | nonempty span _ token _ _ _ _ => exact absent ⟨span, token.1⟩
  | firstRejected span opening continues child =>
      cases parsed with
      | empty _ _ allowed otherOpening closing =>
          cases opening.output_unique otherOpening
          subst allowEmpty
          cases continues with
          | absent absent => exact absent ⟨_, closing.1⟩
      | nonempty _ _ otherOpening _ other _ _ =>
          cases opening.output_unique otherOpening
          exact disjoint child ⟨_, _, _, other⟩
  | tailRejected span opening continues child progress tail =>
      cases parsed with
      | empty _ _ allowed otherOpening closing =>
          cases opening.output_unique otherOpening
          subst allowEmpty
          cases continues with
          | absent absent => exact absent ⟨_, closing.1⟩
      | nonempty _ _ otherOpening _ other _ otherTail =>
          cases opening.output_unique otherOpening
          cases (successUnique child other).2.1
          exact tail.disjoint_success successUnique disjoint ⟨_, _, _, _, otherTail⟩

end Solcore.Syntax.DeclarativeGrammar
