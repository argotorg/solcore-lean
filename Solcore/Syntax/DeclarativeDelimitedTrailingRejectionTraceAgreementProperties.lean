import Solcore.Syntax.DeclarativeDelimitedTrailingTraceAgreementProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingRejectionTraceGrammar
import Solcore.Syntax.DeclarativeRejectionDiagnosticProperties

/-! Cross-relation rejected outcomes and both directions of disjointness for
trailing-enabled lists. Primitive guards and ordered reports remain unchanged. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {α : Type} {opening closing : Symbol} {allowEmpty : Bool} {context : ParseContext}
  {leftParses rightParses : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
  {leftRejects rightRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}
  (agreement : TraceOutcomeAgreement leftParses leftRejects rightParses rightRejects source endByte)

include agreement in
theorem TrailingDelimitedTailTraceRejects.result_agree
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : TrailingDelimitedTailTraceRejects closing context leftParses leftRejects source endByte
      input afterLeft leftReport leftTrace)
    (right : TrailingDelimitedTailTraceRejects closing context rightParses rightRejects source endByte
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
          exact agreement.rejectResultAgree child other
      | laterRejected _ otherComma _ other _ _ =>
          cases comma.output_unique otherComma
          exact False.elim (agreement.rejectSuccessDisjoint child other)
  | laterRejected span comma closingAbsent child progress tail ih =>
      cases right with
      | delimiterMissing commaAbsent _ _ => exact False.elim (commaAbsent ⟨span, comma.1⟩)
      | elementRejected _ otherComma _ other =>
          cases comma.output_unique otherComma
          exact False.elim (agreement.successRejectDisjoint child other)
      | laterRejected _ otherComma _ other _ otherTail =>
          cases comma.output_unique otherComma
          rcases agreement.successResultAgree child other with ⟨rfl, rfl, rfl⟩
          rcases ih otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

include agreement in
theorem TrailingDelimitedListTraceRejects.result_agree
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : TrailingDelimitedListTraceRejects opening closing allowEmpty context leftParses leftRejects
      source endByte input afterLeft leftReport leftTrace)
    (right : TrailingDelimitedListTraceRejects opening closing allowEmpty context rightParses rightRejects
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
          exact agreement.rejectResultAgree child other
      | tailRejected _ otherOpening _ other _ _ =>
          cases opening.output_unique otherOpening
          exact False.elim (agreement.rejectSuccessDisjoint child other)
  | tailRejected span opening continues child progress tail =>
      cases right with
      | openingMissing absent _ => exact False.elim (absent ⟨span, opening.1⟩)
      | firstRejected _ otherOpening _ other =>
          cases opening.output_unique otherOpening
          exact False.elim (agreement.successRejectDisjoint child other)
      | tailRejected _ otherOpening _ other _ otherTail =>
          cases opening.output_unique otherOpening
          rcases agreement.successResultAgree child other with ⟨rfl, rfl, rfl⟩
          rcases tail.result_agree agreement otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

include agreement in
theorem TrailingDelimitedTailTraceRejects.disjoint_success_of_agreement
    {input rejected output : Remainder} {diagnostic : ParseDiagnostic}
    {trace events : List ParseDiagnostic} {values : List α} {closingSpan : SourceSpan}
    (rejection : TrailingDelimitedTailTraceRejects closing context leftParses leftRejects
      source endByte input rejected diagnostic trace)
    (parsed : TrailingDelimitedTailTraceParses closing rightParses source endByte
      input values closingSpan output events) : False := by
  induction rejection generalizing values closingSpan output events with
  | delimiterMissing commaAbsent closingAbsent reported =>
      cases parsed with
      | close _ token => exact closingAbsent ⟨_, token.1⟩
      | trailing span comma _ | next span comma _ _ _ _ => exact commaAbsent ⟨span, comma.1⟩
  | elementRejected span comma closingAbsent child =>
      cases parsed with
      | close commaAbsent _ => exact commaAbsent ⟨span, comma.1⟩
      | trailing _ otherComma closing =>
          cases comma.output_unique otherComma
          exact closingAbsent ⟨_, closing.1⟩
      | next _ otherComma _ other _ _ =>
          cases comma.output_unique otherComma
          exact agreement.rejectSuccessDisjoint child other
  | laterRejected span comma closingAbsent child progress tail ih =>
      cases parsed with
      | close commaAbsent _ => exact commaAbsent ⟨span, comma.1⟩
      | trailing _ otherComma closing =>
          cases comma.output_unique otherComma
          exact closingAbsent ⟨_, closing.1⟩
      | next _ otherComma _ other _ otherTail =>
          cases comma.output_unique otherComma
          cases (agreement.successResultAgree child other).2.1
          exact ih otherTail

include agreement in
theorem TrailingDelimitedListTraceRejects.disjoint_success_of_agreement
    {input rejected output : Remainder} {diagnostic : ParseDiagnostic}
    {trace events : List ParseDiagnostic} {values : DelimitedList α}
    (rejection : TrailingDelimitedListTraceRejects opening closing allowEmpty context leftParses leftRejects
      source endByte input rejected diagnostic trace)
    (parsed : TrailingDelimitedListTraceParses opening closing allowEmpty rightParses
      source endByte input values output events) : False := by
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
          exact agreement.rejectSuccessDisjoint child other
  | tailRejected span opening continues child progress tail =>
      cases parsed with
      | empty _ _ allowed otherOpening closing =>
          cases opening.output_unique otherOpening
          subst allowEmpty
          cases continues with
          | absent absent => exact absent ⟨_, closing.1⟩
      | nonempty _ _ otherOpening _ other _ otherTail =>
          cases opening.output_unique otherOpening
          cases (agreement.successResultAgree child other).2.1
          exact tail.disjoint_success_of_agreement agreement otherTail

include agreement in
theorem TrailingDelimitedTailTraceParses.disjoint_rejection_of_agreement
    {input rejected output : Remainder} {diagnostic : ParseDiagnostic}
    {trace events : List ParseDiagnostic} {values : List α} {closingSpan : SourceSpan}
    (parsed : TrailingDelimitedTailTraceParses closing leftParses source endByte
      input values closingSpan output events)
    (rejection : TrailingDelimitedTailTraceRejects closing context rightParses rightRejects
      source endByte input rejected diagnostic trace) : False :=
  rejection.disjoint_success_of_agreement agreement.symm parsed

include agreement in
theorem TrailingDelimitedListTraceParses.disjoint_rejection_of_agreement
    {input rejected output : Remainder} {diagnostic : ParseDiagnostic}
    {trace events : List ParseDiagnostic} {values : DelimitedList α}
    (parsed : TrailingDelimitedListTraceParses opening closing allowEmpty leftParses
      source endByte input values output events)
    (rejection : TrailingDelimitedListTraceRejects opening closing allowEmpty context rightParses rightRejects
      source endByte input rejected diagnostic trace) : False :=
  rejection.disjoint_success_of_agreement agreement.symm parsed

include agreement in
theorem trailingDelimitedTailTraceOutcomeAgreement :
    TraceOutcomeAgreement
      (fun source endByte input (value : List α × SourceSpan) output events =>
        TrailingDelimitedTailTraceParses closing leftParses source endByte input value.1 value.2 output events)
      (TrailingDelimitedTailTraceRejects closing context leftParses leftRejects)
      (fun source endByte input (value : List α × SourceSpan) output events =>
        TrailingDelimitedTailTraceParses closing rightParses source endByte input value.1 value.2 output events)
      (TrailingDelimitedTailTraceRejects closing context rightParses rightRejects) source endByte where
  successResultAgree left right := by
    rcases left.result_agree agreement.successResultAgree right with ⟨values, closingSpan, output, events⟩
    exact ⟨Prod.ext values closingSpan, output, events⟩
  rejectResultAgree := TrailingDelimitedTailTraceRejects.result_agree agreement
  successRejectDisjoint := TrailingDelimitedTailTraceParses.disjoint_rejection_of_agreement agreement
  rejectSuccessDisjoint := TrailingDelimitedTailTraceRejects.disjoint_success_of_agreement agreement

include agreement in
theorem trailingDelimitedListTraceOutcomeAgreement :
    TraceOutcomeAgreement
      (TrailingDelimitedListTraceParses opening closing allowEmpty leftParses)
      (TrailingDelimitedListTraceRejects opening closing allowEmpty context leftParses leftRejects)
      (TrailingDelimitedListTraceParses opening closing allowEmpty rightParses)
      (TrailingDelimitedListTraceRejects opening closing allowEmpty context rightParses rightRejects)
      source endByte where
  successResultAgree := TrailingDelimitedListTraceParses.result_agree agreement.successResultAgree
  rejectResultAgree := TrailingDelimitedListTraceRejects.result_agree agreement
  successRejectDisjoint := TrailingDelimitedListTraceParses.disjoint_rejection_of_agreement agreement
  rejectSuccessDisjoint := TrailingDelimitedListTraceRejects.disjoint_success_of_agreement agreement

end Solcore.Syntax.DeclarativeGrammar
