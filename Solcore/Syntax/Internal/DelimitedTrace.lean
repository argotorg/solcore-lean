import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar
import Solcore.Syntax.Parser.Diagnostic
import Solcore.Syntax.DeclarativeRejectionDiagnosticGrammar
import Solcore.Syntax.DeclarativeRejectionDiagnosticProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties
import Solcore.Syntax.Internal.TraceBasics

/-!
Exact diagnostic traces of delimited lists, with and without a trailing
separator: trace grammars, unique outcomes, and protection of earlier events.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedNoTrailingTraceGrammar
/-! Independent no-trailing delimited traces. Commas precede closing guards;
after a comma the child is called directly, even on the closing symbol.
Child carrier/window preservation is not built into the grammar. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive NoTrailingDelimitedTailTraceParses {α : Type} (closing : Symbol)
    (elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → List α → SourceSpan → Remainder → List ParseDiagnostic → Prop where
  | close {input output : Remainder} {closingSpan : SourceSpan}
      (commaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .comma))
      (closingToken : ExactTokenParses (.symbol closing) input closingSpan output) :
      NoTrailingDelimitedTailTraceParses closing elementTrace source endByte
        input [] closingSpan output []
  | next {input afterComma afterElement output : Remainder}
      {value : α} {elements : List α} {closingSpan : SourceSpan}
      {elementEvents tailEvents : List ParseDiagnostic} (commaSpan : SourceSpan)
      (commaToken : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (elementParsed : elementTrace source endByte afterComma value afterElement elementEvents)
      (progress : afterComma.cursor < afterElement.cursor)
      (tail : NoTrailingDelimitedTailTraceParses closing elementTrace source endByte
        afterElement elements closingSpan output tailEvents) :
      NoTrailingDelimitedTailTraceParses closing elementTrace source endByte
        input (value :: elements) closingSpan output (elementEvents ++ tailEvents)

inductive NoTrailingDelimitedListTraceParses {α : Type} (opening closing : Symbol)
    (allowEmpty : Bool)
    (elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → DelimitedList α → Remainder → List ParseDiagnostic → Prop where
  | empty {input afterOpening output : Remainder} (openingSpan closingSpan : SourceSpan)
      (allowed : allowEmpty = true)
      (openingToken : ExactTokenParses (.symbol opening) input openingSpan afterOpening)
      (closingToken : ExactTokenParses (.symbol closing) afterOpening closingSpan output) :
      NoTrailingDelimitedListTraceParses opening closing allowEmpty elementTrace source endByte input
        { span := SourceSpan.cover openingSpan closingSpan, elements := [] } output []
  | nonempty {input afterOpening afterFirst output : Remainder}
      {first : α} {rest : List α} {firstEvents tailEvents : List ParseDiagnostic}
      (openingSpan closingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol opening) input openingSpan afterOpening)
      (continues : PreferredCloseNotTaken closing allowEmpty afterOpening)
      (firstParsed : elementTrace source endByte afterOpening first afterFirst firstEvents)
      (progress : afterOpening.cursor < afterFirst.cursor)
      (tail : NoTrailingDelimitedTailTraceParses closing elementTrace source endByte
        afterFirst rest closingSpan output tailEvents) :
      NoTrailingDelimitedListTraceParses opening closing allowEmpty elementTrace source endByte input
        { span := SourceSpan.cover openingSpan closingSpan, elements := first :: rest }
        output (firstEvents ++ tailEvents)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedNoTrailingRejectionTraceGrammar
/-! Independent no-trailing list rejection traces. Commas have priority over
closing delimiters, even when those symbols coincide. After a comma the child
runs directly; its events precede, and never include, the uncommitted report. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive NoTrailingDelimitedTailTraceRejects {α : Type}
    (closing : Symbol) (context : ParseContext)
    (elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | delimiterMissing {input : Remainder} {diagnostic : ParseDiagnostic}
      (commaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .comma))
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol closing))
      (reported : RejectAtReports source endByte
        { head := .symbol .comma, tail := [.symbol closing] } context input diagnostic) :
      NoTrailingDelimitedTailTraceRejects closing context elementTrace elementRejects source endByte
        input input diagnostic []
  | elementRejected {input afterComma rejected : Remainder}
      {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (childRejected : elementRejects source endByte afterComma rejected diagnostic trace) :
      NoTrailingDelimitedTailTraceRejects closing context elementTrace elementRejects source endByte
        input rejected diagnostic trace
  | laterRejected {input afterComma afterElement rejected : Remainder} {value : α}
      {diagnostic : ParseDiagnostic} {childEvents tailEvents : List ParseDiagnostic} (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (childParsed : elementTrace source endByte afterComma value afterElement childEvents)
      (progress : afterComma.cursor < afterElement.cursor)
      (tailRejected : NoTrailingDelimitedTailTraceRejects closing context elementTrace elementRejects
        source endByte afterElement rejected diagnostic tailEvents) :
      NoTrailingDelimitedTailTraceRejects closing context elementTrace elementRejects source endByte
        input rejected diagnostic (childEvents ++ tailEvents)

inductive NoTrailingDelimitedListTraceRejects {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (context : ParseContext)
    (elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | openingMissing {input : Remainder} {diagnostic : ParseDiagnostic}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol opening))
      (reported : RejectAtReports source endByte { head := .symbol opening, tail := [] }
        context input diagnostic) :
      NoTrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace elementRejects
        source endByte input input diagnostic []
  | firstRejected {input afterOpening rejected : Remainder}
      {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol opening) input openingSpan afterOpening)
      (continues : PreferredCloseNotTaken closing allowEmpty afterOpening)
      (childRejected : elementRejects source endByte afterOpening rejected diagnostic trace) :
      NoTrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace elementRejects
        source endByte input rejected diagnostic trace
  | tailRejected {input afterOpening afterFirst rejected : Remainder} {value : α}
      {diagnostic : ParseDiagnostic} {childEvents tailEvents : List ParseDiagnostic} (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol opening) input openingSpan afterOpening)
      (continues : PreferredCloseNotTaken closing allowEmpty afterOpening)
      (childParsed : elementTrace source endByte afterOpening value afterFirst childEvents)
      (progress : afterOpening.cursor < afterFirst.cursor)
      (tailRejected : NoTrailingDelimitedTailTraceRejects closing context elementTrace elementRejects
        source endByte afterFirst rejected diagnostic tailEvents) :
      NoTrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace elementRejects
        source endByte input rejected diagnostic (childEvents ++ tailEvents)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedNoTrailingRejectionTraceProperties
/-! Ordinary erasure and full rejection functionality for no-trailing lists.
All child functionality assumptions remain independent of parser execution. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {α : Type}
  {elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {ordinaryParses : Remainder → α → Remainder → Prop}
  {ordinaryRejects : Remainder → Remainder → Prop}
  {source : SourceId} {endByte : Nat} {opening closing : Symbol} {allowEmpty : Bool} {context : ParseContext}

theorem NoTrailingDelimitedTailTraceRejects.ordinary
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ordinaryParses input value output)
    (rejectErases : ∀ {input rejected diagnostic trace}, elementRejects source endByte input rejected diagnostic trace →
      ordinaryRejects input rejected)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NoTrailingDelimitedTailTraceRejects closing context elementTrace elementRejects
      source endByte input rejected diagnostic trace) :
    DelimitedTailRejects closing false ordinaryParses ordinaryRejects input rejected := by
  induction rejection with
  | delimiterMissing commaAbsent closingAbsent reported => exact .delimiterMissing commaAbsent closingAbsent
  | elementRejected commaSpan comma child =>
      rcases comma with ⟨token, rfl⟩
      exact .elementRejected commaSpan token .disabled (rejectErases child)
  | laterRejected commaSpan comma child progress tail ih =>
      rcases comma with ⟨token, rfl⟩
      exact .laterRejected commaSpan token .disabled (successErases child) progress ih

theorem NoTrailingDelimitedListTraceRejects.ordinary
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ordinaryParses input value output)
    (rejectErases : ∀ {input rejected diagnostic trace}, elementRejects source endByte input rejected diagnostic trace →
      ordinaryRejects input rejected)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NoTrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace elementRejects
      source endByte input rejected diagnostic trace) :
    DelimitedListRejects opening closing allowEmpty false ordinaryParses ordinaryRejects input rejected := by
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
theorem NoTrailingDelimitedTailTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : NoTrailingDelimitedTailTraceRejects closing context elementTrace elementRejects source endByte
      input afterLeft leftReport leftTrace)
    (right : NoTrailingDelimitedTailTraceRejects closing context elementTrace elementRejects source endByte
      input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  induction left generalizing afterRight rightReport rightTrace with
  | delimiterMissing commaAbsent closingAbsent reported =>
      cases right with
      | delimiterMissing _ _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | elementRejected span comma _ | laterRejected span comma _ _ _ =>
          exact False.elim (commaAbsent ⟨span, comma.1⟩)
  | elementRejected span comma child =>
      cases right with
      | delimiterMissing commaAbsent _ _ => exact False.elim (commaAbsent ⟨span, comma.1⟩)
      | elementRejected _ otherComma other =>
          cases comma.output_unique otherComma
          exact rejectUnique child other
      | laterRejected _ otherComma other _ _ =>
          cases comma.output_unique otherComma
          exact False.elim (disjoint child ⟨_, _, _, other⟩)
  | laterRejected span comma child progress tail ih =>
      cases right with
      | delimiterMissing commaAbsent _ _ => exact False.elim (commaAbsent ⟨span, comma.1⟩)
      | elementRejected _ otherComma other =>
          cases comma.output_unique otherComma
          exact False.elim (disjoint other ⟨_, _, _, child⟩)
      | laterRejected _ otherComma other _ otherTail =>
          cases comma.output_unique otherComma
          rcases successUnique child other with ⟨rfl, rfl, rfl⟩
          rcases ih otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

include successUnique rejectUnique disjoint in
theorem NoTrailingDelimitedListTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : NoTrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace elementRejects
      source endByte input afterLeft leftReport leftTrace)
    (right : NoTrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace elementRejects
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
theorem NoTrailingDelimitedTailTraceRejects.disjoint_success
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NoTrailingDelimitedTailTraceRejects closing context elementTrace elementRejects
      source endByte input rejected diagnostic trace) :
    ¬ ∃ values closingSpan output events,
      NoTrailingDelimitedTailTraceParses closing elementTrace source endByte input values closingSpan output events := by
  induction rejection with
  | delimiterMissing commaAbsent closingAbsent reported =>
      rintro ⟨_, _, _, _, parsed⟩
      cases parsed with
      | close _ token => exact closingAbsent ⟨_, token.1⟩
      | next span comma _ _ _ => exact commaAbsent ⟨span, comma.1⟩
  | elementRejected span comma child =>
      rintro ⟨_, _, _, _, parsed⟩
      cases parsed with
      | close commaAbsent _ => exact commaAbsent ⟨span, comma.1⟩
      | next _ otherComma other _ _ =>
          cases comma.output_unique otherComma
          exact disjoint child ⟨_, _, _, other⟩
  | laterRejected span comma child progress tail ih =>
      rintro ⟨_, _, _, _, parsed⟩
      cases parsed with
      | close commaAbsent _ => exact commaAbsent ⟨span, comma.1⟩
      | next _ otherComma other _ otherTail =>
          cases comma.output_unique otherComma
          cases (successUnique child other).2.1
          exact ih ⟨_, _, _, _, otherTail⟩

include successUnique disjoint in
theorem NoTrailingDelimitedListTraceRejects.disjoint_success
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NoTrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace elementRejects
      source endByte input rejected diagnostic trace) :
    ¬ ∃ values output events,
      NoTrailingDelimitedListTraceParses opening closing allowEmpty elementTrace source endByte input values output events := by
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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedNoTrailingTraceProperties
/-! Erasure and structural laws. Only whole-list erasure needs the separate
child carrier/end-index law demanded by the older ordinary list grammar. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {α : Type} {opening closing : Symbol} {allowEmpty : Bool}
  {elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
  {elementParses : Remainder → α → Remainder → Prop} {source : SourceId} {endByte : Nat}

theorem NoTrailingDelimitedTailTraceParses.ordinary
    (elementOrdinary : ∀ {input value output trace},
      elementTrace source endByte input value output trace → elementParses input value output)
    {input output : Remainder} {values : List α} {closingSpan : SourceSpan}
    {trace : List ParseDiagnostic}
    (parsed : NoTrailingDelimitedTailTraceParses closing elementTrace source endByte
      input values closingSpan output trace) :
    NoTrailingDelimitedTailParses closing elementParses input values closingSpan output := by
  induction parsed with
  | close absent token => rw [token.2]; exact .close absent token.1
  | next span comma element progress tail ih =>
      rcases comma with ⟨token, rfl⟩
      exact .next token (elementOrdinary element) progress ih

theorem NoTrailingDelimitedTailTraceParses.output_window
    (elementWindow : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {values : List α} {closingSpan : SourceSpan}
    {trace : List ParseDiagnostic}
    (parsed : NoTrailingDelimitedTailTraceParses closing elementTrace source endByte
      input values closingSpan output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  induction parsed with
  | close absent token => rw [token.2]; exact ⟨rfl, rfl⟩
  | next span comma element progress tail ih =>
      rcases comma with ⟨token, rfl⟩
      have frame := elementWindow element
      exact ⟨ih.1.trans frame.1, ih.2.trans frame.2⟩

theorem NoTrailingDelimitedTailTraceParses.progress
    {input output : Remainder} {values : List α} {closingSpan : SourceSpan}
    {trace : List ParseDiagnostic}
    (parsed : NoTrailingDelimitedTailTraceParses closing elementTrace source endByte
      input values closingSpan output trace) : input.cursor < output.cursor := by
  induction parsed with
  | close absent token => rw [token.2]; exact Nat.lt_succ_self _
  | next span comma element progress tail ih =>
      rcases comma with ⟨token, rfl⟩
      exact Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self _) progress) ih

theorem NoTrailingDelimitedListTraceParses.output_window
    (elementWindow : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {values : DelimitedList α} {trace : List ParseDiagnostic}
    (parsed : NoTrailingDelimitedListTraceParses opening closing allowEmpty elementTrace source endByte
      input values output trace) : output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | empty _ _ _ marker finish => rw [finish.2, marker.2]; exact ⟨rfl, rfl⟩
  | nonempty _ _ marker _ first _ tail =>
      have tailFrame := tail.output_window elementWindow
      have firstFrame := elementWindow first
      rcases marker with ⟨_, rfl⟩
      exact ⟨tailFrame.1.trans firstFrame.1, tailFrame.2.trans firstFrame.2⟩

/-- A tail can never close on a comma: that branch always starts another child. -/
theorem NoTrailingDelimitedTailTraceParses.closing_ne_comma
    {input output : Remainder} {values : List α} {closingSpan : SourceSpan}
    {trace : List ParseDiagnostic}
    (parsed : NoTrailingDelimitedTailTraceParses closing elementTrace source endByte
      input values closingSpan output trace) : closing ≠ .comma := by
  induction parsed with
  | close absent finish => intro same; subst closing; exact absent ⟨_, finish.1⟩
  | next _ _ _ _ _ ih => exact ih

theorem NoTrailingDelimitedListTraceParses.ordinary
    (elementOrdinary : ∀ {input value output trace},
      elementTrace source endByte input value output trace → elementParses input value output)
    (elementWindow : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {values : DelimitedList α} {trace : List ParseDiagnostic}
    (parsed : NoTrailingDelimitedListTraceParses opening closing allowEmpty elementTrace source endByte
      input values output trace) :
    if allowEmpty then NoTrailingDelimitedListParses opening closing elementParses input values output
    else NonemptyNoTrailingDelimitedListParses opening closing elementParses input values output := by
  have frame := parsed.output_window elementWindow
  cases parsed with
  | empty openingSpan closingSpan allowed marker finish =>
      rw [allowed]
      rcases marker with ⟨marker, rfl⟩
      rcases finish with ⟨finish, rfl⟩
      simpa only [Bool.true_eq, ↓reduceIte, Nat.add_assoc] using
        NoTrailingDelimitedListParses.empty (elementParses := elementParses)
          openingSpan closingSpan marker finish
  | nonempty openingSpan closingSpan marker continues first progress tail =>
      rcases marker with ⟨marker, rfl⟩
      have ordinary : NonemptyNoTrailingDelimitedListParses opening closing elementParses
          input { span := SourceSpan.cover openingSpan closingSpan, elements := _ } output :=
        ⟨openingSpan, _, _, _, closingSpan, frame.1, frame.2, marker,
          elementOrdinary first, progress, tail.ordinary elementOrdinary, rfl, rfl⟩
      cases continues with
      | disabled => exact ordinary
      | absent absent => exact .nonempty absent ordinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedNoTrailingTraceExactnessProperties
/-! Exact success functionality includes every element, both covering endpoints,
the complete remainder, and every ordered diagnostic occurrence. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {α : Type} {opening closing : Symbol} {allowEmpty : Bool}
  {elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem NoTrailingDelimitedTailTraceParses.result_unique
    (elementUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      elementTrace source endByte input left afterLeft leftTrace →
      elementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : List α}
    {leftClosing rightClosing : SourceSpan} {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : NoTrailingDelimitedTailTraceParses closing elementTrace source endByte
      input left leftClosing afterLeft leftTrace)
    (rightParsed : NoTrailingDelimitedTailTraceParses closing elementTrace source endByte
      input right rightClosing afterRight rightTrace) :
    left = right ∧ leftClosing = rightClosing ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  induction leftParsed generalizing right rightClosing afterRight rightTrace with
  | close absent finish =>
      cases rightParsed with
      | close _ rightFinish =>
          rcases finish.result_unique rightFinish with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, rfl⟩
      | next span comma _ _ _ => exact False.elim (absent ⟨span, comma.1⟩)
  | next span comma element progress tail ih =>
      cases rightParsed with
      | close absent _ => exact False.elim (absent ⟨span, comma.1⟩)
      | next rightSpan rightComma rightElement _ rightTail =>
          rcases comma.result_unique rightComma with ⟨rfl, rfl⟩
          rcases elementUnique element rightElement with ⟨rfl, rfl, rfl⟩
          rcases ih rightTail with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, rfl⟩

theorem NoTrailingDelimitedListTraceParses.result_unique
    (elementUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      elementTrace source endByte input left afterLeft leftTrace →
      elementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : DelimitedList α}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : NoTrailingDelimitedListTraceParses opening closing allowEmpty elementTrace
      source endByte input left afterLeft leftTrace)
    (rightParsed : NoTrailingDelimitedListTraceParses opening closing allowEmpty elementTrace
      source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | empty openingSpan closingSpan allowed marker finish =>
      cases rightParsed with
      | empty rightOpening rightClosing _ rightMarker rightFinish =>
          rcases marker.result_unique rightMarker with ⟨rfl, rfl⟩
          rcases finish.result_unique rightFinish with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩
      | nonempty _ _ rightMarker continues _ _ _ =>
          rcases marker.result_unique rightMarker with ⟨rfl, rfl⟩
          rw [allowed] at continues
          cases continues with
          | absent absent => exact False.elim (absent ⟨closingSpan, finish.1⟩)
  | nonempty openingSpan closingSpan marker continues first progress tail =>
      cases rightParsed with
      | empty _ rightClosing allowed rightMarker finish =>
          rcases marker.result_unique rightMarker with ⟨rfl, rfl⟩
          rw [allowed] at continues
          cases continues with
          | absent absent => exact False.elim (absent ⟨rightClosing, finish.1⟩)
      | nonempty _ _ rightMarker _ rightFirst _ rightTail =>
          rcases marker.result_unique rightMarker with ⟨rfl, rfl⟩
          rcases elementUnique first rightFirst with ⟨rfl, rfl, rfl⟩
          rcases tail.result_unique elementUnique rightTail with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedNoTrailingTraceOutcomeProperties
/-! Joint exactness for no-trailing list traces under independent child laws.
The result fixes ASTs, remainders, reports, and complete event lists. It neither
asserts that an outcome exists nor identifies a concrete child implementation. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem noTrailingDelimitedListTraceExactOutcomeSpec {α : Type}
    {elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
    {elementRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat}
    (opening closing : Symbol) (allowEmpty : Bool) (context : ParseContext)
    (elements : TraceExactOutcomeSpec elementTrace elementRejects source endByte) :
    TraceExactOutcomeSpec
      (NoTrailingDelimitedListTraceParses opening closing allowEmpty elementTrace)
      (NoTrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace elementRejects)
      source endByte where
  successResultUnique := NoTrailingDelimitedListTraceParses.result_unique elements.successResultUnique
  rejectResultUnique := NoTrailingDelimitedListTraceRejects.result_unique elements.successResultUnique
    elements.rejectResultUnique elements.successRejectDisjoint
  successRejectDisjoint := NoTrailingDelimitedListTraceRejects.disjoint_success elements.successResultUnique
    elements.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedNoTrailingTraceProtectionProperties
/-! No-trailing lists add no delimiter events. Protected child events retain
their complete order and multiplicity, including on rejection. The separate
uncommitted rejection report is not asserted to be protected. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {α : Type} {opening closing : Symbol} {allowEmpty : Bool} {context : ParseContext}
  {elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat} {text : String} {lexical : List SourceSpan}

theorem NoTrailingDelimitedTailTraceParses.cascadeFilters
    (elementProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {values : List α} {closingSpan : SourceSpan}
    {trace : List ParseDiagnostic}
    (parsed : NoTrailingDelimitedTailTraceParses closing elementTrace source endByte
      input values closingSpan output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  induction parsed with
  | close => exact .nil
  | next _ _ element _ _ ih => exact (elementProtected element).append ih

theorem NoTrailingDelimitedListTraceParses.cascadeFilters
    (elementProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {values : DelimitedList α} {trace : List ParseDiagnostic}
    (parsed : NoTrailingDelimitedListTraceParses opening closing allowEmpty elementTrace source endByte
      input values output trace) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | empty => exact .nil
  | nonempty _ _ _ _ first _ tail =>
      exact (elementProtected first).append (tail.cascadeFilters elementProtected)

theorem NoTrailingDelimitedTailTraceRejects.cascadeFilters
    (successProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected diagnostic trace},
      elementRejects source endByte input rejected diagnostic trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NoTrailingDelimitedTailTraceRejects closing context elementTrace elementRejects
      source endByte input rejected diagnostic trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  induction rejection with
  | delimiterMissing => exact .nil
  | elementRejected _ _ child => exact rejectProtected child
  | laterRejected _ _ child _ _ ih => exact (successProtected child).append ih

theorem NoTrailingDelimitedListTraceRejects.cascadeFilters
    (successProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected diagnostic trace},
      elementRejects source endByte input rejected diagnostic trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NoTrailingDelimitedListTraceRejects opening closing allowEmpty context
      elementTrace elementRejects source endByte input rejected diagnostic trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | openingMissing => exact .nil
  | firstRejected _ _ _ child => exact rejectProtected child
  | tailRejected _ _ _ child _ tail =>
      exact (successProtected child).append (tail.cascadeFilters successProtected rejectProtected)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedTrailingTraceGrammar
/-! Independent trailing-enabled delimited traces. Commas precede closing guards;
after a comma the closing symbol is preferred over another child.
Child carrier/window preservation is not built into the grammar. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive TrailingDelimitedTailTraceParses {α : Type} (closing : Symbol)
    (elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → List α → SourceSpan → Remainder → List ParseDiagnostic → Prop where
  | close {input output : Remainder} {closingSpan : SourceSpan}
      (commaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .comma))
      (closingToken : ExactTokenParses (.symbol closing) input closingSpan output) :
      TrailingDelimitedTailTraceParses closing elementTrace source endByte
        input [] closingSpan output []
  | trailing {input afterComma output : Remainder} {closingSpan : SourceSpan}
      (commaSpan : SourceSpan)
      (commaToken : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (closingToken : ExactTokenParses (.symbol closing) afterComma closingSpan output) :
      TrailingDelimitedTailTraceParses closing elementTrace source endByte
        input [] closingSpan output []
  | next {input afterComma afterElement output : Remainder}
      {value : α} {elements : List α} {closingSpan : SourceSpan}
      {elementEvents tailEvents : List ParseDiagnostic} (commaSpan : SourceSpan)
      (commaToken : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex afterComma.cursor (.symbol closing))
      (elementParsed : elementTrace source endByte afterComma value afterElement elementEvents)
      (progress : afterComma.cursor < afterElement.cursor)
      (tail : TrailingDelimitedTailTraceParses closing elementTrace source endByte
        afterElement elements closingSpan output tailEvents) :
      TrailingDelimitedTailTraceParses closing elementTrace source endByte
        input (value :: elements) closingSpan output (elementEvents ++ tailEvents)

inductive TrailingDelimitedListTraceParses {α : Type} (opening closing : Symbol)
    (allowEmpty : Bool)
    (elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → DelimitedList α → Remainder → List ParseDiagnostic → Prop where
  | empty {input afterOpening output : Remainder} (openingSpan closingSpan : SourceSpan)
      (allowed : allowEmpty = true)
      (openingToken : ExactTokenParses (.symbol opening) input openingSpan afterOpening)
      (closingToken : ExactTokenParses (.symbol closing) afterOpening closingSpan output) :
      TrailingDelimitedListTraceParses opening closing allowEmpty elementTrace source endByte input
        { span := SourceSpan.cover openingSpan closingSpan, elements := [] } output []
  | nonempty {input afterOpening afterFirst output : Remainder}
      {first : α} {rest : List α} {firstEvents tailEvents : List ParseDiagnostic}
      (openingSpan closingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol opening) input openingSpan afterOpening)
      (continues : PreferredCloseNotTaken closing allowEmpty afterOpening)
      (firstParsed : elementTrace source endByte afterOpening first afterFirst firstEvents)
      (progress : afterOpening.cursor < afterFirst.cursor)
      (tail : TrailingDelimitedTailTraceParses closing elementTrace source endByte
        afterFirst rest closingSpan output tailEvents) :
      TrailingDelimitedListTraceParses opening closing allowEmpty elementTrace source endByte input
        { span := SourceSpan.cover openingSpan closingSpan, elements := first :: rest }
        output (firstEvents ++ tailEvents)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedTrailingRejectionTraceGrammar
/-! Independent trailing-enabled list rejection traces. Commas have priority over
closing delimiters, even when those symbols coincide. After a comma an immediate
closing delimiter bypasses the child; rejection requires its absence. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive TrailingDelimitedTailTraceRejects {α : Type}
    (closing : Symbol) (context : ParseContext)
    (elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | delimiterMissing {input : Remainder} {diagnostic : ParseDiagnostic}
      (commaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .comma))
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol closing))
      (reported : RejectAtReports source endByte
        { head := .symbol .comma, tail := [.symbol closing] } context input diagnostic) :
      TrailingDelimitedTailTraceRejects closing context elementTrace elementRejects source endByte
        input input diagnostic []
  | elementRejected {input afterComma rejected : Remainder}
      {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex
        afterComma.cursor (.symbol closing))
      (childRejected : elementRejects source endByte afterComma rejected diagnostic trace) :
      TrailingDelimitedTailTraceRejects closing context elementTrace elementRejects source endByte
        input rejected diagnostic trace
  | laterRejected {input afterComma afterElement rejected : Remainder} {value : α}
      {diagnostic : ParseDiagnostic} {childEvents tailEvents : List ParseDiagnostic} (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex
        afterComma.cursor (.symbol closing))
      (childParsed : elementTrace source endByte afterComma value afterElement childEvents)
      (progress : afterComma.cursor < afterElement.cursor)
      (tailRejected : TrailingDelimitedTailTraceRejects closing context elementTrace elementRejects
        source endByte afterElement rejected diagnostic tailEvents) :
      TrailingDelimitedTailTraceRejects closing context elementTrace elementRejects source endByte
        input rejected diagnostic (childEvents ++ tailEvents)

inductive TrailingDelimitedListTraceRejects {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (context : ParseContext)
    (elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | openingMissing {input : Remainder} {diagnostic : ParseDiagnostic}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol opening))
      (reported : RejectAtReports source endByte { head := .symbol opening, tail := [] }
        context input diagnostic) :
      TrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace elementRejects
        source endByte input input diagnostic []
  | firstRejected {input afterOpening rejected : Remainder}
      {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol opening) input openingSpan afterOpening)
      (continues : PreferredCloseNotTaken closing allowEmpty afterOpening)
      (childRejected : elementRejects source endByte afterOpening rejected diagnostic trace) :
      TrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace elementRejects
        source endByte input rejected diagnostic trace
  | tailRejected {input afterOpening afterFirst rejected : Remainder} {value : α}
      {diagnostic : ParseDiagnostic} {childEvents tailEvents : List ParseDiagnostic} (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol opening) input openingSpan afterOpening)
      (continues : PreferredCloseNotTaken closing allowEmpty afterOpening)
      (childParsed : elementTrace source endByte afterOpening value afterFirst childEvents)
      (progress : afterOpening.cursor < afterFirst.cursor)
      (tailRejected : TrailingDelimitedTailTraceRejects closing context elementTrace elementRejects
        source endByte afterFirst rejected diagnostic tailEvents) :
      TrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace elementRejects
        source endByte input rejected diagnostic (childEvents ++ tailEvents)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedTrailingRejectionTraceProperties
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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedTrailingRejectionTraceProtectionProperties
/-! Trailing-enabled lists add no delimiter events. Protected child events retain
their complete order and multiplicity, including on rejection. The separate
uncommitted rejection report is not asserted to be protected. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {α : Type} {opening closing : Symbol} {allowEmpty : Bool} {context : ParseContext}
  {elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat} {text : String} {lexical : List SourceSpan}

theorem TrailingDelimitedTailTraceRejects.cascadeFilters
    (successProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected diagnostic trace},
      elementRejects source endByte input rejected diagnostic trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TrailingDelimitedTailTraceRejects closing context elementTrace elementRejects
      source endByte input rejected diagnostic trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  induction rejection with
  | delimiterMissing => exact .nil
  | elementRejected _ _ _ child => exact rejectProtected child
  | laterRejected _ _ _ child _ _ ih => exact (successProtected child).append ih

theorem TrailingDelimitedListTraceRejects.cascadeFilters
    (successProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected diagnostic trace},
      elementRejects source endByte input rejected diagnostic trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TrailingDelimitedListTraceRejects opening closing allowEmpty context
      elementTrace elementRejects source endByte input rejected diagnostic trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | openingMissing => exact .nil
  | firstRejected _ _ _ child => exact rejectProtected child
  | tailRejected _ _ _ child _ tail =>
      exact (successProtected child).append (tail.cascadeFilters successProtected rejectProtected)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedTrailingTraceAgreementProperties
/-! Successful trailing lists agree under pairwise child success agreement.
The left and right child relations need not be internally functional. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {α : Type} {opening closing : Symbol} {allowEmpty : Bool}
  {leftParses rightParses : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}
  (successAgree : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
    leftParses source endByte input left afterLeft leftTrace →
    rightParses source endByte input right afterRight rightTrace →
      left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)

include successAgree in
theorem TrailingDelimitedTailTraceParses.result_agree
    {input afterLeft afterRight : Remainder} {left right : List α}
    {leftClosing rightClosing : SourceSpan} {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : TrailingDelimitedTailTraceParses closing leftParses source endByte
      input left leftClosing afterLeft leftTrace)
    (rightParsed : TrailingDelimitedTailTraceParses closing rightParses source endByte
      input right rightClosing afterRight rightTrace) :
    left = right ∧ leftClosing = rightClosing ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  induction leftParsed generalizing right rightClosing afterRight rightTrace with
  | close absent finish =>
      cases rightParsed with
      | close _ rightFinish =>
          rcases finish.result_unique rightFinish with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, rfl⟩
      | trailing span comma _ | next span comma _ _ _ _ =>
          exact False.elim (absent ⟨span, comma.1⟩)
  | trailing span comma finish =>
      cases rightParsed with
      | close absent _ => exact False.elim (absent ⟨span, comma.1⟩)
      | trailing rightSpan rightComma rightFinish =>
          rcases comma.result_unique rightComma with ⟨rfl, rfl⟩
          rcases finish.result_unique rightFinish with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, rfl⟩
      | next rightSpan rightComma absent _ _ _ =>
          rcases comma.result_unique rightComma with ⟨rfl, rfl⟩
          exact False.elim (absent ⟨_, finish.1⟩)
  | next span comma absent element progress tail ih =>
      cases rightParsed with
      | close absent _ => exact False.elim (absent ⟨span, comma.1⟩)
      | trailing rightSpan rightComma finish =>
          rcases comma.result_unique rightComma with ⟨rfl, rfl⟩
          exact False.elim (absent ⟨_, finish.1⟩)
      | next rightSpan rightComma _ rightElement _ rightTail =>
          rcases comma.result_unique rightComma with ⟨rfl, rfl⟩
          rcases successAgree element rightElement with ⟨rfl, rfl, rfl⟩
          rcases ih rightTail with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, rfl⟩

include successAgree in
theorem TrailingDelimitedListTraceParses.result_agree
    {input afterLeft afterRight : Remainder} {left right : DelimitedList α}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : TrailingDelimitedListTraceParses opening closing allowEmpty leftParses
      source endByte input left afterLeft leftTrace)
    (rightParsed : TrailingDelimitedListTraceParses opening closing allowEmpty rightParses
      source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | empty openingSpan closingSpan allowed marker finish =>
      cases rightParsed with
      | empty rightOpening rightClosing _ rightMarker rightFinish =>
          rcases marker.result_unique rightMarker with ⟨rfl, rfl⟩
          rcases finish.result_unique rightFinish with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩
      | nonempty _ _ rightMarker continues _ _ _ =>
          rcases marker.result_unique rightMarker with ⟨rfl, rfl⟩
          rw [allowed] at continues
          cases continues with
          | absent absent => exact False.elim (absent ⟨closingSpan, finish.1⟩)
  | nonempty openingSpan closingSpan marker continues first progress tail =>
      cases rightParsed with
      | empty _ rightClosing allowed rightMarker finish =>
          rcases marker.result_unique rightMarker with ⟨rfl, rfl⟩
          rw [allowed] at continues
          cases continues with
          | absent absent => exact False.elim (absent ⟨rightClosing, finish.1⟩)
      | nonempty _ _ rightMarker _ rightFirst _ rightTail =>
          rcases marker.result_unique rightMarker with ⟨rfl, rfl⟩
          rcases successAgree first rightFirst with ⟨rfl, rfl, rfl⟩
          rcases tail.result_agree successAgree rightTail with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedTrailingRejectionTraceAgreementProperties
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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedTrailingTraceMonotonicityProperties
/-! Child-relation implication lifts through trailing-enabled lists without
changing a value, source coordinate, remainder, report, or diagnostic event.
Every existing delimiter guard and progress witness is retained unchanged. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {α : Type} {opening closing : Symbol} {allowEmpty : Bool} {context : ParseContext}
  {source : SourceId} {endByte : Nat}
  {elementTrace otherTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
  {elementRejects otherRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic →
    List ParseDiagnostic → Prop}

theorem TrailingDelimitedTailTraceParses.mono
    (childMap : ∀ {input value output trace},
      elementTrace source endByte input value output trace → otherTrace source endByte input value output trace)
    {input output : Remainder} {values : List α} {closingSpan : SourceSpan} {trace : List ParseDiagnostic}
    (parsed : TrailingDelimitedTailTraceParses closing elementTrace source endByte
      input values closingSpan output trace) :
    TrailingDelimitedTailTraceParses closing otherTrace source endByte input values closingSpan output trace := by
  induction parsed with
  | close absent closing => exact .close absent closing
  | trailing span comma closing => exact .trailing span comma closing
  | next span comma absent child progress tail ih =>
      exact .next span comma absent (childMap child) progress ih

theorem TrailingDelimitedListTraceParses.mono
    (childMap : ∀ {input value output trace},
      elementTrace source endByte input value output trace → otherTrace source endByte input value output trace)
    {input output : Remainder} {values : DelimitedList α} {trace : List ParseDiagnostic}
    (parsed : TrailingDelimitedListTraceParses opening closing allowEmpty elementTrace source endByte
      input values output trace) :
    TrailingDelimitedListTraceParses opening closing allowEmpty otherTrace source endByte input values output trace := by
  cases parsed with
  | empty openingSpan closingSpan allowed opening closing =>
      exact .empty openingSpan closingSpan allowed opening closing
  | nonempty openingSpan closingSpan opening continues first progress tail =>
      exact .nonempty openingSpan closingSpan opening continues (childMap first) progress (tail.mono childMap)

theorem TrailingDelimitedTailTraceRejects.mono
    (successMap : ∀ {input value output trace},
      elementTrace source endByte input value output trace → otherTrace source endByte input value output trace)
    (rejectMap : ∀ {input rejected report trace},
      elementRejects source endByte input rejected report trace → otherRejects source endByte input rejected report trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TrailingDelimitedTailTraceRejects closing context elementTrace elementRejects source endByte
      input rejected report trace) :
    TrailingDelimitedTailTraceRejects closing context otherTrace otherRejects source endByte
      input rejected report trace := by
  induction rejection with
  | delimiterMissing commaAbsent closingAbsent reported => exact .delimiterMissing commaAbsent closingAbsent reported
  | elementRejected span comma absent child => exact .elementRejected span comma absent (rejectMap child)
  | laterRejected span comma absent child progress tail ih =>
      exact .laterRejected span comma absent (successMap child) progress ih

theorem TrailingDelimitedListTraceRejects.mono
    (successMap : ∀ {input value output trace},
      elementTrace source endByte input value output trace → otherTrace source endByte input value output trace)
    (rejectMap : ∀ {input rejected report trace},
      elementRejects source endByte input rejected report trace → otherRejects source endByte input rejected report trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace elementRejects
      source endByte input rejected report trace) :
    TrailingDelimitedListTraceRejects opening closing allowEmpty context otherTrace otherRejects
      source endByte input rejected report trace := by
  cases rejection with
  | openingMissing absent reported => exact .openingMissing absent reported
  | firstRejected span opening continues child => exact .firstRejected span opening continues (rejectMap child)
  | tailRejected span opening continues child progress tail =>
      exact .tailRejected span opening continues (successMap child) progress (tail.mono successMap rejectMap)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedTrailingTraceProperties
/-! Erasure and structural laws. Only whole-list erasure needs the separate
child carrier/end-index law demanded by the older ordinary list grammar. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {α : Type} {opening closing : Symbol} {allowEmpty : Bool}
  {elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
  {elementParses : Remainder → α → Remainder → Prop} {source : SourceId} {endByte : Nat}

theorem TrailingDelimitedTailTraceParses.ordinary
    (elementOrdinary : ∀ {input value output trace},
      elementTrace source endByte input value output trace → elementParses input value output)
    {input output : Remainder} {values : List α} {closingSpan : SourceSpan}
    {trace : List ParseDiagnostic}
    (parsed : TrailingDelimitedTailTraceParses closing elementTrace source endByte
      input values closingSpan output trace) :
    TrailingDelimitedTailParses closing elementParses input values closingSpan output := by
  induction parsed with
  | close absent token => rw [token.2]; exact .close absent token.1
  | trailing span comma token =>
      rcases comma with ⟨comma, rfl⟩
      rw [token.2]
      exact .trailing comma token.1
  | next span comma absent element progress tail ih =>
      rcases comma with ⟨token, rfl⟩
      exact .next token absent (elementOrdinary element) progress ih

theorem TrailingDelimitedTailTraceParses.output_window
    (elementWindow : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {values : List α} {closingSpan : SourceSpan}
    {trace : List ParseDiagnostic}
    (parsed : TrailingDelimitedTailTraceParses closing elementTrace source endByte
      input values closingSpan output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  induction parsed with
  | close absent token => rw [token.2]; exact ⟨rfl, rfl⟩
  | trailing span comma token => rw [token.2, comma.2]; exact ⟨rfl, rfl⟩
  | next span comma absent element progress tail ih =>
      rcases comma with ⟨token, rfl⟩
      have frame := elementWindow element
      exact ⟨ih.1.trans frame.1, ih.2.trans frame.2⟩

theorem TrailingDelimitedTailTraceParses.progress
    {input output : Remainder} {values : List α} {closingSpan : SourceSpan}
    {trace : List ParseDiagnostic}
    (parsed : TrailingDelimitedTailTraceParses closing elementTrace source endByte
      input values closingSpan output trace) : input.cursor < output.cursor := by
  induction parsed with
  | close absent token => rw [token.2]; exact Nat.lt_succ_self _
  | trailing span comma token => rw [token.2, comma.2]; simp only; omega
  | next span comma absent element progress tail ih =>
      rcases comma with ⟨token, rfl⟩
      exact Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self _) progress) ih

theorem TrailingDelimitedListTraceParses.output_window
    (elementWindow : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {values : DelimitedList α} {trace : List ParseDiagnostic}
    (parsed : TrailingDelimitedListTraceParses opening closing allowEmpty elementTrace source endByte
      input values output trace) : output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | empty _ _ _ marker finish => rw [finish.2, marker.2]; exact ⟨rfl, rfl⟩
  | nonempty _ _ marker _ first _ tail =>
      have tailFrame := tail.output_window elementWindow
      have firstFrame := elementWindow first
      rcases marker with ⟨_, rfl⟩
      exact ⟨tailFrame.1.trans firstFrame.1, tailFrame.2.trans firstFrame.2⟩

theorem TrailingDelimitedListTraceParses.progress
    {input output : Remainder} {values : DelimitedList α} {trace : List ParseDiagnostic}
    (parsed : TrailingDelimitedListTraceParses opening closing allowEmpty elementTrace source endByte
      input values output trace) : input.cursor < output.cursor := by
  cases parsed with
  | empty _ _ _ marker finish => rw [finish.2, marker.2]; simp only; omega
  | nonempty _ _ marker _ first progress tail =>
      have tailProgress := tail.progress
      rcases marker with ⟨_, rfl⟩
      exact Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self _) progress) tailProgress

theorem TrailingDelimitedListTraceParses.ordinary
    (elementOrdinary : ∀ {input value output trace},
      elementTrace source endByte input value output trace → elementParses input value output)
    (elementWindow : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {values : DelimitedList α} {trace : List ParseDiagnostic}
    (parsed : TrailingDelimitedListTraceParses opening closing allowEmpty elementTrace source endByte
      input values output trace) :
    if allowEmpty then TrailingDelimitedListParses opening closing elementParses input values output
    else NonemptyTrailingDelimitedListParses opening closing elementParses input values output := by
  have frame := parsed.output_window elementWindow
  cases parsed with
  | empty openingSpan closingSpan allowed marker finish =>
      rw [allowed]
      rcases marker with ⟨marker, rfl⟩
      rcases finish with ⟨finish, rfl⟩
      simpa only [Bool.true_eq, ↓reduceIte, Nat.add_assoc] using
        TrailingDelimitedListParses.empty (elementParses := elementParses)
          openingSpan closingSpan marker finish
  | nonempty openingSpan closingSpan marker continues first progress tail =>
      rcases marker with ⟨marker, rfl⟩
      have ordinary : NonemptyTrailingDelimitedListParses opening closing elementParses
          input { span := SourceSpan.cover openingSpan closingSpan, elements := _ } output :=
        ⟨openingSpan, _, _, _, closingSpan, frame.1, frame.2, marker,
          elementOrdinary first, progress, tail.ordinary elementOrdinary, rfl, rfl⟩
      cases continues with
      | disabled => exact ordinary
      | absent absent => exact .nonempty absent ordinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedTrailingTraceExactnessProperties
/-! Exact success functionality includes every element, both covering endpoints,
the complete remainder, and every ordered diagnostic occurrence. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {α : Type} {opening closing : Symbol} {allowEmpty : Bool}
  {elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem TrailingDelimitedTailTraceParses.result_unique
    (elementUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      elementTrace source endByte input left afterLeft leftTrace →
      elementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : List α}
    {leftClosing rightClosing : SourceSpan} {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : TrailingDelimitedTailTraceParses closing elementTrace source endByte
      input left leftClosing afterLeft leftTrace)
    (rightParsed : TrailingDelimitedTailTraceParses closing elementTrace source endByte
      input right rightClosing afterRight rightTrace) :
    left = right ∧ leftClosing = rightClosing ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  induction leftParsed generalizing right rightClosing afterRight rightTrace with
  | close absent finish =>
      cases rightParsed with
      | close _ rightFinish =>
          rcases finish.result_unique rightFinish with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, rfl⟩
      | trailing span comma _ => exact False.elim (absent ⟨span, comma.1⟩)
      | next span comma _ _ _ _ => exact False.elim (absent ⟨span, comma.1⟩)
  | trailing span comma finish =>
      cases rightParsed with
      | close absent _ => exact False.elim (absent ⟨span, comma.1⟩)
      | trailing rightSpan rightComma rightFinish =>
          rcases comma.result_unique rightComma with ⟨rfl, rfl⟩
          rcases finish.result_unique rightFinish with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, rfl⟩
      | next rightSpan rightComma absent _ _ _ =>
          rcases comma.result_unique rightComma with ⟨rfl, rfl⟩
          exact False.elim (absent ⟨_, finish.1⟩)
  | next span comma absent element progress tail ih =>
      cases rightParsed with
      | close absent _ => exact False.elim (absent ⟨span, comma.1⟩)
      | trailing rightSpan rightComma finish =>
          rcases comma.result_unique rightComma with ⟨rfl, rfl⟩
          exact False.elim (absent ⟨_, finish.1⟩)
      | next rightSpan rightComma _ rightElement _ rightTail =>
          rcases comma.result_unique rightComma with ⟨rfl, rfl⟩
          rcases elementUnique element rightElement with ⟨rfl, rfl, rfl⟩
          rcases ih rightTail with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, rfl⟩

theorem TrailingDelimitedListTraceParses.result_unique
    (elementUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      elementTrace source endByte input left afterLeft leftTrace →
      elementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : DelimitedList α}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : TrailingDelimitedListTraceParses opening closing allowEmpty elementTrace
      source endByte input left afterLeft leftTrace)
    (rightParsed : TrailingDelimitedListTraceParses opening closing allowEmpty elementTrace
      source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | empty openingSpan closingSpan allowed marker finish =>
      cases rightParsed with
      | empty rightOpening rightClosing _ rightMarker rightFinish =>
          rcases marker.result_unique rightMarker with ⟨rfl, rfl⟩
          rcases finish.result_unique rightFinish with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩
      | nonempty _ _ rightMarker continues _ _ _ =>
          rcases marker.result_unique rightMarker with ⟨rfl, rfl⟩
          rw [allowed] at continues
          cases continues with
          | absent absent => exact False.elim (absent ⟨closingSpan, finish.1⟩)
  | nonempty openingSpan closingSpan marker continues first progress tail =>
      cases rightParsed with
      | empty _ rightClosing allowed rightMarker finish =>
          rcases marker.result_unique rightMarker with ⟨rfl, rfl⟩
          rw [allowed] at continues
          cases continues with
          | absent absent => exact False.elim (absent ⟨rightClosing, finish.1⟩)
      | nonempty _ _ rightMarker _ rightFirst _ rightTail =>
          rcases marker.result_unique rightMarker with ⟨rfl, rfl⟩
          rcases elementUnique first rightFirst with ⟨rfl, rfl, rfl⟩
          rcases tail.result_unique elementUnique rightTail with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedTrailingTraceOutcomeProperties
/-! Joint exactness for trailing-enabled list traces under independent child
laws. It fixes complete outcomes without asserting existence or child execution. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem trailingDelimitedListTraceExactOutcomeSpec {α : Type}
    {elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
    {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat}
    (opening closing : Symbol) (allowEmpty : Bool) (context : ParseContext)
    (elements : TraceExactOutcomeSpec elementTrace elementRejects source endByte) :
    TraceExactOutcomeSpec
      (TrailingDelimitedListTraceParses opening closing allowEmpty elementTrace)
      (TrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace elementRejects)
      source endByte where
  successResultUnique := TrailingDelimitedListTraceParses.result_unique elements.successResultUnique
  rejectResultUnique := TrailingDelimitedListTraceRejects.result_unique elements.successResultUnique
    elements.rejectResultUnique elements.successRejectDisjoint
  successRejectDisjoint := TrailingDelimitedListTraceRejects.disjoint_success elements.successResultUnique
    elements.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeDelimitedTrailingTraceProtectionProperties
/-! Trailing-enabled lists add no delimiter events. Protected child events retain
their complete order and multiplicity through either silent closing branch. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {α : Type} {opening closing : Symbol} {allowEmpty : Bool}
  {elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat} {text : String} {lexical : List SourceSpan}

theorem TrailingDelimitedTailTraceParses.cascadeFilters
    (elementProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {values : List α} {closingSpan : SourceSpan}
    {trace : List ParseDiagnostic}
    (parsed : TrailingDelimitedTailTraceParses closing elementTrace source endByte
      input values closingSpan output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  induction parsed with
  | close | trailing => exact .nil
  | next _ _ _ element _ _ ih => exact (elementProtected element).append ih

theorem TrailingDelimitedListTraceParses.cascadeFilters
    (elementProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {values : DelimitedList α} {trace : List ParseDiagnostic}
    (parsed : TrailingDelimitedListTraceParses opening closing allowEmpty elementTrace source endByte
      input values output trace) : ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | empty => exact .nil
  | nonempty _ _ _ _ first _ tail =>
      exact (elementProtected first).append (tail.cascadeFilters elementProtected)

end Solcore.Syntax.DeclarativeGrammar
end
