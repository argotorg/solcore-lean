import Solcore.Syntax.Grammar.Basics
import Solcore.Syntax.Parser.Diagnostic
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties
import Solcore.Syntax.Internal.TraceBasics
import Solcore.Syntax.Grammar.Types
import Solcore.Syntax.DeclarativeRejectionDiagnosticProperties
import Solcore.Syntax.Internal.DelimitedTrace
import Solcore.Syntax.Internal.NameTrace
import Solcore.Syntax.DeclarativeCoreTypeNameOutcomeProperties
import Solcore.Syntax.DeclarativeTypeDispatchSelectionProperties

/-!
Exact diagnostic traces of type expressions.

Trace grammars for each type form, their unique outcomes and rejection
protection, and the recursive trace of `TypeExpr` with dispatch monotonicity.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeComptimeTypeRejectionTraceGrammar
/-! Raw comptime-type rejection records the first failing stage. Marker and
punctuation are silent; the separate terminal report is never an emitted event. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ComptimeTypeTraceRejects
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | markerMissing {input : Remainder} {report : ParseDiagnostic}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.identifier ContextualKeyword.comptime.spelling))
      (reported : RejectAtReports source endByte { head := .contextual .comptime, tail := [] }
        .typeExpr input report) :
      ComptimeTypeTraceRejects elementTrace elementRejects source endByte input input report []
  | openingMissing {input afterMarker : Remainder} {report : ParseDiagnostic}
      (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker)
      (absent : TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex afterMarker.cursor (.symbol .less))
      (reported : RejectAtReports source endByte { head := .symbol .less, tail := [] }
        .typeExpr afterMarker report) :
      ComptimeTypeTraceRejects elementTrace elementRejects source endByte input afterMarker report []
  | innerRejected {input afterMarker afterOpening rejected : Remainder}
      {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (markerSpan openingSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker)
      (opening : ExactTokenParses (.symbol .less) afterMarker openingSpan afterOpening)
      (typed : elementRejects source endByte afterOpening rejected report trace) :
      ComptimeTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace
  | closingMissing {input afterMarker afterOpening afterInner : Remainder} {inner : Syntax.TypeExpr}
      {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (markerSpan openingSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker)
      (opening : ExactTokenParses (.symbol .less) afterMarker openingSpan afterOpening)
      (typed : elementTrace source endByte afterOpening inner afterInner trace)
      (absent : TokenKindAbsentAt afterInner.tokens afterInner.endIndex afterInner.cursor (.symbol .greater))
      (reported : RejectAtReports source endByte { head := .symbol .greater, tail := [] } .typeExpr afterInner report) :
      ComptimeTypeTraceRejects elementTrace elementRejects source endByte input afterInner report trace

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeComptimeTypeTraceGrammar
/-! Raw comptime-type traces retain every source-shaped AST component. The
contextual marker is its actual identifier token; only the child emits events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def comptimeTypeTraceValue (markerSpan openingSpan closingSpan : SourceSpan)
    (inner : Syntax.TypeExpr) : Syntax.TypeExpr := {
  span := SourceSpan.cover markerSpan closingSpan
  value := .comptime markerSpan (SourceSpan.cover openingSpan closingSpan) inner
}

inductive ComptimeTypeTraceParses
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
      Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterMarker afterOpening afterInner output : Remainder} {inner : Syntax.TypeExpr}
      {trace : List ParseDiagnostic} (markerSpan openingSpan closingSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker)
      (opening : ExactTokenParses (.symbol .less) afterMarker openingSpan afterOpening)
      (typed : elementTrace source endByte afterOpening inner afterInner trace)
      (closing : ExactTokenParses (.symbol .greater) afterInner closingSpan output) :
      ComptimeTypeTraceParses elementTrace source endByte input
        (comptimeTypeTraceValue markerSpan openingSpan closingSpan inner) output trace

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeComptimeTypeTraceProperties
/-! Independent raw structure, erasure, exactness, and protected events.
Carrier preservation and progress are separate child laws, not grammar guards. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
    Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem ComptimeTypeTraceParses.ordinary_components
    {ordinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    (erases : ∀ {input value output trace},
      elementTrace source endByte input value output trace → ordinary input value output)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ComptimeTypeTraceParses elementTrace source endByte input value output trace) :
    ∃ markerSpan openingSpan closingSpan afterMarker afterOpening afterInner inner,
      ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker ∧
      ExactTokenParses (.symbol .less) afterMarker openingSpan afterOpening ∧
      ordinary afterOpening inner afterInner ∧
      ExactTokenParses (.symbol .greater) afterInner closingSpan output ∧
      value = comptimeTypeTraceValue markerSpan openingSpan closingSpan inner := by
  cases parsed with
  | parsed m o c marker opening typed closing => exact ⟨m, o, c, _, _, _, _, marker, opening, erases typed, closing, rfl⟩

theorem ComptimeTypeTraceParses.ordinary
    (erases : ∀ {input value output trace},
      elementTrace source endByte input value output trace → TypeExprParses input value output)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ComptimeTypeTraceParses elementTrace source endByte input value output trace) :
    TypeExprParses input value output := by
  cases parsed with
  | parsed m o c marker opening typed closing => exact .comptime m o c marker opening closing rfl (erases typed)

theorem ComptimeTypeTraceParses.output_window
    (childWindow : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ComptimeTypeTraceParses elementTrace source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed m o c marker opening typed closing =>
      simpa only [closing.2, opening.2, marker.2] using childWindow typed

theorem ComptimeTypeTraceParses.cursor_lt
    (childProgress : ∀ {input value output trace},
      elementTrace source endByte input value output trace → input.cursor ≤ output.cursor)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ComptimeTypeTraceParses elementTrace source endByte input value output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed m o c marker opening typed closing =>
      have progress := childProgress typed
      rw [opening.2, marker.2] at progress
      change input.cursor + 1 + 1 ≤ _ at progress
      rw [closing.2]
      change input.cursor < _ + 1
      omega

theorem ComptimeTypeTraceParses.result_unique
    (unique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      elementTrace source endByte input left afterLeft leftTrace →
      elementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Syntax.TypeExpr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ComptimeTypeTraceParses elementTrace source endByte input left afterLeft leftTrace)
    (rightParsed : ComptimeTypeTraceParses elementTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed m o c marker opening typed closing =>
      cases rightParsed with
      | parsed m' o' c' marker' opening' typed' closing' =>
          rcases marker.result_unique marker' with ⟨rfl, rfl⟩
          rcases opening.result_unique opening' with ⟨rfl, rfl⟩
          rcases unique typed typed' with ⟨rfl, rfl, rfl⟩
          rcases closing.result_unique closing' with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem ComptimeTypeTraceParses.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (childProtected : ∀ {input value output trace},
      elementTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ComptimeTypeTraceParses elementTrace source endByte input value output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed _ _ _ _ _ typed _ => exact childProtected typed

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeComptimeTypeRejectionTraceProperties
/-! Raw comptime failures include marker/opening failures. Erasure separates
them explicitly from the older positively selected comptime relation. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {ordinaryRejects : Remainder → Remainder → Prop} {source : SourceId} {endByte : Nat}

theorem ComptimeTypeTraceRejects.ordinary_cases
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ordinaryRejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ComptimeTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    (TokenKindAbsentAt input.tokens input.endIndex input.cursor (.identifier ContextualKeyword.comptime.spelling) ∧
      rejected = input) ∨
    (∃ markerSpan afterMarker, ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker ∧
      TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex afterMarker.cursor (.symbol .less) ∧
      rejected = afterMarker) ∨
    ComptimeTypeRejects ordinaryRejects input rejected := by
  cases rejection with
  | markerMissing absent => exact .inl ⟨absent, rfl⟩
  | openingMissing span marker absent => exact .inr (.inl ⟨span, _, marker, absent, rfl⟩)
  | innerRejected m o marker opening typed => exact .inr (.inr (.innerRejected m o marker opening (rejectErases typed)))
  | closingMissing m o marker opening typed absent =>
      exact .inr (.inr (.closingMissing m o marker opening (successErases typed) absent))

theorem ComptimeTypeTraceRejects.ordinary_of_prefix
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ordinaryRejects input rejected)
    {input afterMarker afterOpening rejected : Remainder} {markerSpan openingSpan : SourceSpan}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (marker : ExactTokenParses (.identifier ContextualKeyword.comptime.spelling) input markerSpan afterMarker)
    (opening : ExactTokenParses (.symbol .less) afterMarker openingSpan afterOpening)
    (rejection : ComptimeTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ComptimeTypeRejects ordinaryRejects input rejected := by
  rcases rejection.ordinary_cases successErases rejectErases with missing | missing | ordinary
  · exact False.elim (missing.1 ⟨markerSpan, marker.1⟩)
  · rcases missing with ⟨span, afterOther, other, absent, _⟩
    cases marker.output_unique other
    exact False.elim (absent ⟨openingSpan, opening.1⟩)
  · exact ordinary

private theorem comptime_absent_conflicts_token {kind : TokenKind} {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (token : ExactTokenParses kind input span output) : False := absent ⟨span, token.1⟩

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
theorem ComptimeTypeTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : ComptimeTypeTraceRejects elementTrace elementRejects source endByte input afterLeft leftReport leftTrace)
    (right : ComptimeTypeTraceRejects elementTrace elementRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left <;> cases right <;>
    grind (ematch := 12) only [ExactTokenParses.result_unique, comptime_absent_conflicts_token,
      RejectAtReports.diagnostic_unique]

include successUnique disjoint in
theorem ComptimeTypeTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ComptimeTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, ComptimeTypeTraceParses elementTrace source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases parsed
  cases rejection <;>
    grind (ematch := 12) only [ExactTokenParses.result_unique, comptime_absent_conflicts_token]

theorem ComptimeTypeTraceRejects.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (successProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ComptimeTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | markerMissing | openingMissing => exact .nil
  | innerRejected _ _ _ _ typed => exact rejectProtected typed
  | closingMissing _ _ _ _ typed => exact successProtected typed

theorem comptimeTypeTraceExactOutcomeSpec
    (types : TraceExactOutcomeSpec elementTrace elementRejects source endByte) :
    TraceExactOutcomeSpec (ComptimeTypeTraceParses elementTrace)
      (ComptimeTypeTraceRejects elementTrace elementRejects) source endByte where
  successResultUnique := ComptimeTypeTraceParses.result_unique types.successResultUnique
  rejectResultUnique := ComptimeTypeTraceRejects.result_unique
    types.successResultUnique types.rejectResultUnique types.successRejectDisjoint
  successRejectDisjoint := ComptimeTypeTraceRejects.disjoint_success
    types.successResultUnique types.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFunctionReturnsRejectionTraceGrammar
/-! Rejection requires an exact present returns marker. Absence is an optional
success, not a raw marker failure; the list's terminal report stays separate. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive FunctionReturnsTraceRejects
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | present {input afterMarker rejected : Remainder} {report : ParseDiagnostic}
      {trace : List ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.returns.spelling) input markerSpan afterMarker)
      (valuesRejected : TrailingDelimitedListTraceRejects .leftParen .rightParen true .typeExpr
        elementTrace elementRejects source endByte afterMarker rejected report trace) :
      FunctionReturnsTraceRejects elementTrace elementRejects source endByte input rejected report trace

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFunctionReturnsTraceGrammar
/-! Optional function-type returns preserve the complete parenthesized list.
An absent contextual identifier succeeds without consumption or events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive FunctionReturnsTraceParses
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Option (DelimitedList Syntax.TypeExpr) → Remainder → List ParseDiagnostic → Prop where
  | absent {input : Remainder}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.identifier ContextualKeyword.returns.spelling)) :
      FunctionReturnsTraceParses elementTrace source endByte input none input []
  | present {input afterMarker output : Remainder} {values : DelimitedList Syntax.TypeExpr}
      {trace : List ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.returns.spelling) input markerSpan afterMarker)
      (valuesParsed : TrailingDelimitedListTraceParses .leftParen .rightParen true elementTrace
        source endByte afterMarker values output trace) :
      FunctionReturnsTraceParses elementTrace source endByte input (some values) output trace

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFunctionReturnsTraceAgreementProperties
/-! Distinct child relations agree through optional returns. Exact contextual
marker presence separates the silent absent success from every rejection. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {leftParses rightParses : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {leftRejects rightRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem functionReturnsTraceOutcomeAgreement
    (children : TraceOutcomeAgreement leftParses leftRejects rightParses rightRejects source endByte) :
    TraceOutcomeAgreement (FunctionReturnsTraceParses leftParses)
      (FunctionReturnsTraceRejects leftParses leftRejects)
      (FunctionReturnsTraceParses rightParses)
      (FunctionReturnsTraceRejects rightParses rightRejects) source endByte where
  successResultAgree left right := by
    cases left with
    | absent absent =>
        cases right with
        | absent => exact ⟨rfl, rfl, rfl⟩
        | present span marker _ => exact False.elim (absent ⟨span, marker.1⟩)
    | present span marker values =>
        cases right with
        | absent absent => exact False.elim (absent ⟨span, marker.1⟩)
        | present _ otherMarker otherValues =>
            rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
            rcases values.result_agree children.successResultAgree otherValues with ⟨rfl, rfl, rfl⟩
            exact ⟨rfl, rfl, rfl⟩
  rejectResultAgree left right := by
    cases left with
    | present _ marker values =>
        cases right with
        | present _ otherMarker otherValues =>
            rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
            exact values.result_agree children otherValues
  successRejectDisjoint parsed rejected := by
    cases rejected with
    | present span marker values =>
        cases parsed with
        | absent absent => exact absent ⟨span, marker.1⟩
        | present _ otherMarker otherValues =>
            rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
            exact otherValues.disjoint_rejection_of_agreement children values
  rejectSuccessDisjoint rejected parsed := by
    cases rejected with
    | present span marker values =>
        cases parsed with
        | absent absent => exact absent ⟨span, marker.1⟩
        | present _ otherMarker otherValues =>
            rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
            exact values.disjoint_success_of_agreement children otherValues

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFunctionReturnsTraceProperties
/-! Independent optional-return structure, ordinary erasure, and exactness.
Only ordinary list erasure and carrier preservation require a child carrier law. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem FunctionReturnsTraceParses.present_token
    {input output : Remainder} {values : DelimitedList Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : FunctionReturnsTraceParses elementTrace source endByte input (some values) output trace) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor
      { span, value := .identifier ContextualKeyword.returns.spelling } := by
  cases parsed with
  | present span marker _ => exact ⟨span, marker.1⟩

theorem FunctionReturnsTraceParses.output_window
    (childWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {values : Option (DelimitedList Syntax.TypeExpr)} {trace : List ParseDiagnostic}
    (parsed : FunctionReturnsTraceParses elementTrace source endByte input values output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | absent => exact ⟨rfl, rfl⟩
  | present span marker values => simpa only [marker.2] using values.output_window childWindow

theorem FunctionReturnsTraceParses.some_progress
    {input output : Remainder} {values : DelimitedList Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : FunctionReturnsTraceParses elementTrace source endByte input (some values) output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | present span marker values =>
      have progress := values.progress
      rw [marker.2] at progress
      exact Nat.lt_trans (Nat.lt_succ_self _) progress

theorem FunctionReturnsTraceParses.cursor_le
    {input output : Remainder} {values : Option (DelimitedList Syntax.TypeExpr)} {trace : List ParseDiagnostic}
    (parsed : FunctionReturnsTraceParses elementTrace source endByte input values output trace) :
    input.cursor ≤ output.cursor := by
  cases values with
  | none => cases parsed; exact Nat.le_refl _
  | some => exact Nat.le_of_lt parsed.some_progress

private theorem returnsTypeTail_of_generic {input output : Remainder}
    {values : List Syntax.TypeExpr} {closingSpan : SourceSpan}
    (parsed : TrailingDelimitedTailParses .rightParen TypeExprParses input values closingSpan output) :
    TypeExprTrailingDelimitedTailParses .rightParen input values closingSpan output := by
  induction parsed with
  | close absent token => exact .close absent token
  | trailing comma closing => exact .trailing comma closing
  | next comma absent child progress tail ih => exact .next comma absent progress rfl child ih

theorem FunctionReturnsTraceParses.ordinary
    (childOrdinary : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (childWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {values : Option (DelimitedList Syntax.TypeExpr)} {trace : List ParseDiagnostic}
    (parsed : FunctionReturnsTraceParses elementTrace source endByte input values output trace) :
    OptionalFunctionTypeReturnsParses input values output := by
  cases parsed with
  | absent absent => exact .absent absent
  | present span marker values =>
      apply OptionalFunctionTypeReturnsParses.present span marker
      have frame := values.output_window childWindow
      cases values with
      | empty openingSpan closingSpan allowed opening closing =>
          rcases opening with ⟨opening, rfl⟩
          rcases closing with ⟨closing, rfl⟩
          exact .empty openingSpan closingSpan rfl rfl opening closing
      | nonempty openingSpan closingSpan opening continues first progress tail =>
          rcases opening with ⟨opening, rfl⟩
          cases continues with
          | absent absent =>
              exact .nonempty openingSpan closingSpan absent opening progress frame.1 frame.2 rfl rfl
                (childOrdinary first) (returnsTypeTail_of_generic (tail.ordinary childOrdinary))

theorem FunctionReturnsTraceParses.result_unique
    (childUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      elementTrace source endByte input left afterLeft leftTrace →
      elementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Option (DelimitedList Syntax.TypeExpr)}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : FunctionReturnsTraceParses elementTrace source endByte input left afterLeft leftTrace)
    (rightParsed : FunctionReturnsTraceParses elementTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | absent absent =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl, rfl⟩
      | present span marker _ => exact False.elim (absent ⟨span, marker.1⟩)
  | present span marker values =>
      cases rightParsed with
      | absent absent => exact False.elim (absent ⟨span, marker.1⟩)
      | present otherSpan otherMarker other =>
          cases marker.output_unique otherMarker
          rcases values.result_unique childUnique other with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem FunctionReturnsTraceParses.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (childProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {values : Option (DelimitedList Syntax.TypeExpr)} {trace : List ParseDiagnostic}
    (parsed : FunctionReturnsTraceParses elementTrace source endByte input values output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | absent => exact .nil
  | present _ _ values => exact values.cascadeFilters childProtected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFunctionReturnsRejectionTraceProperties
/-! Optional return rejection requires its marker and delegates to the exact
list outcome. Absence remains disjoint success; independent child laws prove
ordinary erasure, uniqueness, disjointness, and event protection. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {ordinaryRejects : Remainder → Remainder → Prop} {source : SourceId} {endByte : Nat}

theorem FunctionReturnsTraceRejects.marker_present
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : FunctionReturnsTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .identifier ContextualKeyword.returns.spelling } := by
  cases rejection with
  | present span marker _ => exact ⟨span, marker.1⟩

theorem FunctionReturnsTraceRejects.ordinary
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ordinaryRejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : FunctionReturnsTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    FunctionTypeReturnsRejects ordinaryRejects input rejected := by
  cases rejection with
  | present span marker values =>
      exact .valuesRejected span marker (values.ordinary successErases rejectErases)

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
theorem FunctionReturnsTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : FunctionReturnsTraceRejects elementTrace elementRejects source endByte input afterLeft leftReport leftTrace)
    (right : FunctionReturnsTraceRejects elementTrace elementRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | present _ marker left =>
      cases right with
      | present _ otherMarker right =>
          cases marker.output_unique otherMarker
          exact left.result_unique successUnique rejectUnique disjoint right

include successUnique disjoint in
theorem FunctionReturnsTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : FunctionReturnsTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ¬ ∃ arguments output events, FunctionReturnsTraceParses elementTrace source endByte input arguments output events := by
  rintro ⟨arguments, output, events, parsed⟩
  cases rejection with
  | present span marker rejection =>
      cases parsed with
      | absent absent => exact absent ⟨span, marker.1⟩
      | present _ otherMarker parsed =>
          cases marker.output_unique otherMarker
          exact rejection.disjoint_success successUnique disjoint ⟨_, _, _, parsed⟩

theorem FunctionReturnsTraceRejects.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (successProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : FunctionReturnsTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | present _ _ values => exact values.cascadeFilters successProtected rejectProtected

theorem functionReturnsTraceExactOutcomeSpec
    (types : TraceExactOutcomeSpec elementTrace elementRejects source endByte) :
    TraceExactOutcomeSpec (FunctionReturnsTraceParses elementTrace)
      (FunctionReturnsTraceRejects elementTrace elementRejects) source endByte where
  successResultUnique := FunctionReturnsTraceParses.result_unique types.successResultUnique
  rejectResultUnique := FunctionReturnsTraceRejects.result_unique
    types.successResultUnique types.rejectResultUnique types.successRejectDisjoint
  successRejectDisjoint := FunctionReturnsTraceRejects.disjoint_success
    types.successResultUnique types.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFunctionTypeTraceGrammar
/-! Raw function types retain both trailing-enabled lists and their exact
event order. The keyword is silent; optional returns determine the final span. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def functionTypeTraceValue (keywordSpan : SourceSpan)
    (parameters : DelimitedList Syntax.TypeExpr)
    (returns : Option (DelimitedList Syntax.TypeExpr)) : Syntax.TypeExpr := {
  span := SourceSpan.cover keywordSpan (match returns with
    | some values => values.span
    | none => parameters.span)
  value := .function keywordSpan parameters returns
}

inductive FunctionTypeTraceParses
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterKeyword afterParameters output : Remainder}
      {parameters : DelimitedList Syntax.TypeExpr} {returns : Option (DelimitedList Syntax.TypeExpr)}
      {parameterTrace returnTrace : List ParseDiagnostic} (keywordSpan : SourceSpan)
      (keywordToken : ExactTokenParses (.keyword .functionKw) input keywordSpan afterKeyword)
      (parametersParsed : TrailingDelimitedListTraceParses .leftParen .rightParen true
        elementTrace source endByte afterKeyword parameters afterParameters parameterTrace)
      (returnsParsed : FunctionReturnsTraceParses elementTrace source endByte
        afterParameters returns output returnTrace) :
      FunctionTypeTraceParses elementTrace source endByte input
        (functionTypeTraceValue keywordSpan parameters returns) output (parameterTrace ++ returnTrace)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFunctionTypeRejectionTraceGrammar
/-! Raw function rejection stops at the first failing stage. Missing keyword
is a raw failure, not a selected function-type failure. Reports stay separate. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive FunctionTypeTraceRejects
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | markerMissing {input : Remainder} {report : ParseDiagnostic}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.keyword .functionKw))
      (reported : RejectAtReports source endByte { head := .keyword .functionKw, tail := [] }
        .typeExpr input report) :
      FunctionTypeTraceRejects elementTrace elementRejects source endByte input input report []
  | parametersRejected {input afterKeyword rejected : Remainder}
      {report : ParseDiagnostic} {trace : List ParseDiagnostic} (keywordSpan : SourceSpan)
      (keywordToken : ExactTokenParses (.keyword .functionKw) input keywordSpan afterKeyword)
      (parametersRejected : TrailingDelimitedListTraceRejects .leftParen .rightParen true .typeExpr
        elementTrace elementRejects source endByte afterKeyword rejected report trace) :
      FunctionTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace
  | returnsRejected {input afterKeyword afterParameters rejected : Remainder}
      {parameters : DelimitedList Syntax.TypeExpr} {report : ParseDiagnostic}
      {parameterTrace returnTrace : List ParseDiagnostic} (keywordSpan : SourceSpan)
      (keywordToken : ExactTokenParses (.keyword .functionKw) input keywordSpan afterKeyword)
      (parametersParsed : TrailingDelimitedListTraceParses .leftParen .rightParen true
        elementTrace source endByte afterKeyword parameters afterParameters parameterTrace)
      (returnsRejected : FunctionReturnsTraceRejects elementTrace elementRejects source endByte
        afterParameters rejected report returnTrace) :
      FunctionTypeTraceRejects elementTrace elementRejects source endByte input rejected report
        (parameterTrace ++ returnTrace)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFunctionTypeTraceAgreementProperties
/-! Heterogeneous child agreement lifts through raw function parameters and
optional returns. Raw missing-keyword failures remain first failures, and
parameter events precede return events on both sides of every comparison. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {leftParses rightParses : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {leftRejects rightRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem functionTypeTraceOutcomeAgreement
    (children : TraceOutcomeAgreement leftParses leftRejects rightParses rightRejects source endByte) :
    TraceOutcomeAgreement (FunctionTypeTraceParses leftParses) (FunctionTypeTraceRejects leftParses leftRejects)
      (FunctionTypeTraceParses rightParses) (FunctionTypeTraceRejects rightParses rightRejects) source endByte where
  successResultAgree left right := by
    cases left with
    | parsed _ marker parameters returns =>
        cases right with
        | parsed _ otherMarker otherParameters otherReturns =>
            rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
            rcases parameters.result_agree children.successResultAgree otherParameters with ⟨rfl, rfl, rfl⟩
            rcases (functionReturnsTraceOutcomeAgreement children).successResultAgree returns otherReturns with
              ⟨rfl, rfl, rfl⟩
            exact ⟨rfl, rfl, rfl⟩
  rejectResultAgree left right := by
    cases left with
    | markerMissing absent reported =>
        cases right with
        | markerMissing _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
        | parametersRejected span marker _ | returnsRejected span marker _ _ =>
            exact False.elim (absent ⟨span, marker.1⟩)
    | parametersRejected span marker parameters =>
        cases right with
        | markerMissing absent _ => exact False.elim (absent ⟨span, marker.1⟩)
        | parametersRejected _ otherMarker otherParameters =>
            rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
            exact parameters.result_agree children otherParameters
        | returnsRejected _ otherMarker otherParameters _ =>
            rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
            exact False.elim (parameters.disjoint_success_of_agreement children otherParameters)
    | returnsRejected span marker parameters returns =>
        cases right with
        | markerMissing absent _ => exact False.elim (absent ⟨span, marker.1⟩)
        | parametersRejected _ otherMarker otherParameters =>
            rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
            exact False.elim (parameters.disjoint_rejection_of_agreement children otherParameters)
        | returnsRejected _ otherMarker otherParameters otherReturns =>
            rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
            rcases parameters.result_agree children.successResultAgree otherParameters with ⟨rfl, rfl, rfl⟩
            rcases (functionReturnsTraceOutcomeAgreement children).rejectResultAgree returns otherReturns with
              ⟨rfl, rfl, rfl⟩
            exact ⟨rfl, rfl, rfl⟩
  successRejectDisjoint parsed rejected := by
    cases parsed with
    | parsed span marker parameters returns =>
        cases rejected with
        | markerMissing absent _ => exact absent ⟨span, marker.1⟩
        | parametersRejected _ otherMarker otherParameters =>
            rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
            exact parameters.disjoint_rejection_of_agreement children otherParameters
        | returnsRejected _ otherMarker otherParameters otherReturns =>
            rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
            rcases parameters.result_agree children.successResultAgree otherParameters with ⟨rfl, rfl, rfl⟩
            exact (functionReturnsTraceOutcomeAgreement children).successRejectDisjoint returns otherReturns
  rejectSuccessDisjoint rejected parsed := by
    cases parsed with
    | parsed span marker parameters returns =>
        cases rejected with
        | markerMissing absent _ => exact absent ⟨span, marker.1⟩
        | parametersRejected _ otherMarker otherParameters =>
            rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
            exact otherParameters.disjoint_success_of_agreement children parameters
        | returnsRejected _ otherMarker otherParameters otherReturns =>
            rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
            rcases otherParameters.result_agree children.successResultAgree parameters with ⟨rfl, rfl, rfl⟩
            exact (functionReturnsTraceOutcomeAgreement children).rejectSuccessDisjoint otherReturns returns

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFunctionTypeTraceProperties
/-! Function-type structure and exactness are independent of parser execution.
Only ordinary erasure and output-carrier preservation need a child carrier law. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

private theorem functionTypeTail_of_generic {input output : Remainder}
    {values : List Syntax.TypeExpr} {closingSpan : SourceSpan}
    (parsed : TrailingDelimitedTailParses .rightParen TypeExprParses input values closingSpan output) :
    TypeExprTrailingDelimitedTailParses .rightParen input values closingSpan output := by
  induction parsed with
  | close absent token => exact .close absent token
  | trailing comma closing => exact .trailing comma closing
  | next comma absent child progress tail ih => exact .next comma absent progress rfl child ih

theorem FunctionTypeTraceParses.ordinary
    (childOrdinary : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (childWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : FunctionTypeTraceParses elementTrace source endByte input value output trace) :
    TypeExprParses input value output := by
  cases parsed with
  | parsed span marker parameters returns =>
      refine TypeExprParses.function span marker rfl ?_ (returns.ordinary childOrdinary childWindow)
      have frame := parameters.output_window childWindow
      cases parameters with
      | empty openingSpan closingSpan allowed opening closing =>
          rcases opening with ⟨opening, rfl⟩
          rcases closing with ⟨closing, rfl⟩
          exact .empty openingSpan closingSpan rfl rfl opening closing
      | nonempty openingSpan closingSpan opening continues first progress tail =>
          rcases opening with ⟨opening, rfl⟩
          cases continues with
          | absent absent =>
              exact .nonempty openingSpan closingSpan absent opening progress frame.1 frame.2 rfl rfl
                (childOrdinary first) (functionTypeTail_of_generic (tail.ordinary childOrdinary))

theorem FunctionTypeTraceParses.output_window
    (childWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : FunctionTypeTraceParses elementTrace source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed span marker parameters returns =>
      have first := parameters.output_window childWindow
      have last := returns.output_window childWindow
      simpa only [marker.2] using And.intro (last.1.trans first.1) (last.2.trans first.2)

theorem FunctionTypeTraceParses.progress
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : FunctionTypeTraceParses elementTrace source endByte input value output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed span marker parameters returns =>
      have first := parameters.progress
      rw [marker.2] at first
      exact Nat.lt_of_lt_of_le (Nat.lt_trans (Nat.lt_succ_self _) first) returns.cursor_le

theorem FunctionTypeTraceParses.result_unique
    (childUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      elementTrace source endByte input left afterLeft leftTrace →
      elementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Syntax.TypeExpr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : FunctionTypeTraceParses elementTrace source endByte input left afterLeft leftTrace)
    (rightParsed : FunctionTypeTraceParses elementTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed span marker parameters returns =>
      cases rightParsed with
      | parsed otherSpan otherMarker otherParameters otherReturns =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          rcases parameters.result_unique childUnique otherParameters with ⟨rfl, rfl, rfl⟩
          rcases returns.result_unique childUnique otherReturns with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem FunctionTypeTraceParses.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (childProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : FunctionTypeTraceParses elementTrace source endByte input value output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed _ _ parameters returns =>
      exact (parameters.cascadeFilters childProtected).append (returns.cascadeFilters childProtected)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeFunctionTypeRejectionTraceProperties
/-! The raw keyword failure is separated from selected function rejection.
Successful parameter-carrier preservation is required only for ordinary erasure. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {ordinaryRejects : Remainder → Remainder → Prop} {source : SourceId} {endByte : Nat}

theorem FunctionTypeTraceRejects.ordinary_cases
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ordinaryRejects input rejected)
    (childWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : FunctionTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    (TokenKindAbsentAt input.tokens input.endIndex input.cursor (.keyword .functionKw) ∧ rejected = input) ∨
      FunctionTypeRejects ordinaryRejects input rejected := by
  cases rejection with
  | markerMissing absent => exact .inl ⟨absent, rfl⟩
  | parametersRejected span marker parameters =>
      exact .inr (.parametersRejected span marker (parameters.ordinary successErases rejectErases))
  | returnsRejected span marker parameters returns =>
      exact .inr (.returnsRejected span marker (parameters.ordinary successErases childWindow)
        (returns.ordinary successErases rejectErases))

theorem FunctionTypeTraceRejects.ordinary_of_marker_present
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ordinaryRejects input rejected)
    (childWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input afterKeyword rejected : Remainder} {keywordSpan : SourceSpan}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (marker : ExactTokenParses (.keyword .functionKw) input keywordSpan afterKeyword)
    (rejection : FunctionTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    FunctionTypeRejects ordinaryRejects input rejected := by
  rcases rejection.ordinary_cases successErases rejectErases childWindow with missing | ordinary
  · exact False.elim (missing.1 ⟨keywordSpan, marker.1⟩)
  · exact ordinary

private theorem function_absent_conflicts_token {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.keyword .functionKw))
    (token : ExactTokenParses (.keyword .functionKw) input span output) : False := absent ⟨span, token.1⟩

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
theorem FunctionTypeTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : FunctionTypeTraceRejects elementTrace elementRejects source endByte input afterLeft leftReport leftTrace)
    (right : FunctionTypeTraceRejects elementTrace elementRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  have listUnique := @TrailingDelimitedListTraceParses.result_unique Syntax.TypeExpr
    .leftParen .rightParen true elementTrace source endByte successUnique
  have listRejectUnique := @TrailingDelimitedListTraceRejects.result_unique Syntax.TypeExpr
    elementTrace elementRejects source endByte .leftParen .rightParen true .typeExpr
    successUnique rejectUnique disjoint
  have listDisjoint := @TrailingDelimitedListTraceRejects.disjoint_success Syntax.TypeExpr
    elementTrace elementRejects source endByte .leftParen .rightParen true .typeExpr successUnique disjoint
  have returnUnique := @FunctionReturnsTraceRejects.result_unique elementTrace elementRejects
    source endByte successUnique rejectUnique disjoint
  cases left <;> cases right <;>
    grind (ematch := 12) only [ExactTokenParses.result_unique, function_absent_conflicts_token,
      RejectAtReports.diagnostic_unique]

include successUnique disjoint in
theorem FunctionTypeTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : FunctionTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, FunctionTypeTraceParses elementTrace source endByte input value output events := by
  have listUnique := @TrailingDelimitedListTraceParses.result_unique Syntax.TypeExpr
    .leftParen .rightParen true elementTrace source endByte successUnique
  have listDisjoint := @TrailingDelimitedListTraceRejects.disjoint_success Syntax.TypeExpr
    elementTrace elementRejects source endByte .leftParen .rightParen true .typeExpr successUnique disjoint
  have returnDisjoint := @FunctionReturnsTraceRejects.disjoint_success elementTrace elementRejects
    source endByte successUnique disjoint
  rintro ⟨value, output, events, parsed⟩
  cases parsed
  cases rejection <;>
    grind (ematch := 12) only [ExactTokenParses.result_unique, function_absent_conflicts_token]

theorem FunctionTypeTraceRejects.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (successProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : FunctionTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | markerMissing => exact .nil
  | parametersRejected _ _ parameters => exact parameters.cascadeFilters successProtected rejectProtected
  | returnsRejected _ _ parameters returns =>
      exact (parameters.cascadeFilters successProtected).append
        (returns.cascadeFilters successProtected rejectProtected)

theorem functionTypeTraceExactOutcomeSpec
    (types : TraceExactOutcomeSpec elementTrace elementRejects source endByte) :
    TraceExactOutcomeSpec (FunctionTypeTraceParses elementTrace)
      (FunctionTypeTraceRejects elementTrace elementRejects) source endByte where
  successResultUnique := FunctionTypeTraceParses.result_unique types.successResultUnique
  rejectResultUnique := FunctionTypeTraceRejects.result_unique
    types.successResultUnique types.rejectResultUnique types.successRejectDisjoint
  successRejectDisjoint := FunctionTypeTraceRejects.disjoint_success
    types.successResultUnique types.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeMappingTypeRejectionTraceGrammar
/-! Raw mapping rejection records the first failing stage, including missing
marker/opening cases that a selected dispatcher branch cannot reach. Marker
and punctuation are silent; only completed or rejected children add events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive MappingTypeTraceRejects
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | markerMissing {input : Remainder} {report : ParseDiagnostic}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.identifier ContextualKeyword.mapping.spelling))
      (reported : RejectAtReports source endByte { head := .contextual .mapping, tail := [] }
        .typeExpr input report) :
      MappingTypeTraceRejects elementTrace elementRejects source endByte input input report []
  | openingMissing {input afterMarker : Remainder} {report : ParseDiagnostic}
      (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.mapping.spelling) input markerSpan afterMarker)
      (absent : TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex afterMarker.cursor (.symbol .leftParen))
      (reported : RejectAtReports source endByte { head := .symbol .leftParen, tail := [] }
        .typeExpr afterMarker report) :
      MappingTypeTraceRejects elementTrace elementRejects source endByte input afterMarker report []
  | keyRejected {input afterMarker afterOpening rejected : Remainder}
      {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (markerSpan openingSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.mapping.spelling) input markerSpan afterMarker)
      (opening : ExactTokenParses (.symbol .leftParen) afterMarker openingSpan afterOpening)
      (key : elementRejects source endByte afterOpening rejected report trace) :
      MappingTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace
  | arrowMissing {input afterMarker afterOpening afterKey : Remainder} {key : Syntax.TypeExpr}
      {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (markerSpan openingSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.mapping.spelling) input markerSpan afterMarker)
      (opening : ExactTokenParses (.symbol .leftParen) afterMarker openingSpan afterOpening)
      (keyParsed : elementTrace source endByte afterOpening key afterKey trace)
      (absent : TokenKindAbsentAt afterKey.tokens afterKey.endIndex afterKey.cursor (.symbol .fatArrow))
      (reported : RejectAtReports source endByte { head := .symbol .fatArrow, tail := [] } .typeExpr afterKey report) :
      MappingTypeTraceRejects elementTrace elementRejects source endByte input afterKey report trace
  | valueRejected {input afterMarker afterOpening afterKey afterArrow rejected : Remainder} {key : Syntax.TypeExpr}
      {report : ParseDiagnostic} {keyEvents valueEvents : List ParseDiagnostic}
      (markerSpan openingSpan arrowSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.mapping.spelling) input markerSpan afterMarker)
      (opening : ExactTokenParses (.symbol .leftParen) afterMarker openingSpan afterOpening)
      (keyParsed : elementTrace source endByte afterOpening key afterKey keyEvents)
      (arrow : ExactTokenParses (.symbol .fatArrow) afterKey arrowSpan afterArrow)
      (value : elementRejects source endByte afterArrow rejected report valueEvents) :
      MappingTypeTraceRejects elementTrace elementRejects source endByte input rejected report (keyEvents ++ valueEvents)
  | closingMissing {input afterMarker afterOpening afterKey afterArrow afterValue : Remainder}
      {key value : Syntax.TypeExpr} {report : ParseDiagnostic} {keyEvents valueEvents : List ParseDiagnostic}
      (markerSpan openingSpan arrowSpan : SourceSpan)
      (marker : ExactTokenParses (.identifier ContextualKeyword.mapping.spelling) input markerSpan afterMarker)
      (opening : ExactTokenParses (.symbol .leftParen) afterMarker openingSpan afterOpening)
      (keyParsed : elementTrace source endByte afterOpening key afterKey keyEvents)
      (arrow : ExactTokenParses (.symbol .fatArrow) afterKey arrowSpan afterArrow)
      (valueParsed : elementTrace source endByte afterArrow value afterValue valueEvents)
      (absent : TokenKindAbsentAt afterValue.tokens afterValue.endIndex afterValue.cursor (.symbol .rightParen))
      (reported : RejectAtReports source endByte { head := .symbol .rightParen, tail := [] } .typeExpr afterValue report) :
      MappingTypeTraceRejects elementTrace elementRejects source endByte input afterValue report (keyEvents ++ valueEvents)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeMappingTypeRejectionTraceProtectionProperties
/-! Mapping rejection protects only the existing key/value event suffix, in
its original order and multiplicity; its separate report remains uncommitted. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem MappingTypeTraceRejects.cascadeFilters
    {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
    {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat} {text : String} {lexical : List SourceSpan}
    (successProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : MappingTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | markerMissing | openingMissing => exact .nil
  | keyRejected _ _ _ _ key => exact rejectProtected key
  | arrowMissing _ _ _ _ key => exact successProtected key
  | valueRejected _ _ _ _ _ key _ value => exact (successProtected key).append (rejectProtected value)
  | closingMissing _ _ _ _ _ key _ value => exact (successProtected key).append (successProtected value)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeMappingTypeTraceGrammar
/-! Raw mapping types use a contextual identifier marker and two recursive
children. Delimiters are silent; key events precede value events exactly. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def mappingTypeTraceValue (markerSpan openingSpan closingSpan : SourceSpan)
    (key value : Syntax.TypeExpr) : Syntax.TypeExpr := {
  span := SourceSpan.cover markerSpan closingSpan
  value := .mapping markerSpan (SourceSpan.cover openingSpan closingSpan) key value
}

inductive MappingTypeTraceParses
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterMarker afterOpening afterKey afterArrow afterValue output : Remainder}
      {key value : Syntax.TypeExpr} {keyEvents valueEvents : List ParseDiagnostic}
      (markerSpan openingSpan arrowSpan closingSpan : SourceSpan)
      (markerToken : ExactTokenParses (.identifier ContextualKeyword.mapping.spelling) input markerSpan afterMarker)
      (openingToken : ExactTokenParses (.symbol .leftParen) afterMarker openingSpan afterOpening)
      (keyParsed : elementTrace source endByte afterOpening key afterKey keyEvents)
      (arrowToken : ExactTokenParses (.symbol .fatArrow) afterKey arrowSpan afterArrow)
      (valueParsed : elementTrace source endByte afterArrow value afterValue valueEvents)
      (closingToken : ExactTokenParses (.symbol .rightParen) afterValue closingSpan output) :
      MappingTypeTraceParses elementTrace source endByte input
        (mappingTypeTraceValue markerSpan openingSpan closingSpan key value) output (keyEvents ++ valueEvents)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeMappingTypeRejectionTraceProperties
/-! Raw mapping failures include marker/opening failures. Erasure separates
them explicitly from the older positively selected mapping relation. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {ordinaryRejects : Remainder → Remainder → Prop} {source : SourceId} {endByte : Nat}

theorem MappingTypeTraceRejects.ordinary_cases
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ordinaryRejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : MappingTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    (TokenKindAbsentAt input.tokens input.endIndex input.cursor (.identifier ContextualKeyword.mapping.spelling) ∧
      rejected = input) ∨
    (∃ markerSpan afterMarker, ExactTokenParses (.identifier ContextualKeyword.mapping.spelling) input markerSpan afterMarker ∧
      TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex afterMarker.cursor (.symbol .leftParen) ∧
      rejected = afterMarker) ∨
    MappingTypeRejects ordinaryRejects input rejected := by
  cases rejection with
  | markerMissing absent => exact .inl ⟨absent, rfl⟩
  | openingMissing span marker absent => exact .inr (.inl ⟨span, _, marker, absent, rfl⟩)
  | keyRejected m o marker opening key => exact .inr (.inr (.keyRejected m o marker opening (rejectErases key)))
  | arrowMissing m o marker opening key absent =>
      exact .inr (.inr (.arrowMissing m o marker opening (successErases key) absent))
  | valueRejected m o a marker opening key arrow value =>
      exact .inr (.inr (.valueRejected m o a marker opening (successErases key) arrow (rejectErases value)))
  | closingMissing m o a marker opening key arrow value absent =>
      exact .inr (.inr (.closingMissing m o a marker opening (successErases key) arrow (successErases value) absent))

theorem MappingTypeTraceRejects.ordinary_of_prefix
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ordinaryRejects input rejected)
    {input afterMarker afterOpening rejected : Remainder} {markerSpan openingSpan : SourceSpan}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (marker : ExactTokenParses (.identifier ContextualKeyword.mapping.spelling) input markerSpan afterMarker)
    (opening : ExactTokenParses (.symbol .leftParen) afterMarker openingSpan afterOpening)
    (rejection : MappingTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    MappingTypeRejects ordinaryRejects input rejected := by
  rcases rejection.ordinary_cases successErases rejectErases with missing | missing | ordinary
  · exact False.elim (missing.1 ⟨markerSpan, marker.1⟩)
  · rcases missing with ⟨span, afterOther, other, absent, _⟩
    cases marker.output_unique other
    exact False.elim (absent ⟨openingSpan, opening.1⟩)
  · exact ordinary

private theorem mapping_absent_conflicts_token {kind : TokenKind} {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (token : ExactTokenParses kind input span output) : False := absent ⟨span, token.1⟩

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
theorem MappingTypeTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : MappingTypeTraceRejects elementTrace elementRejects source endByte input afterLeft leftReport leftTrace)
    (right : MappingTypeTraceRejects elementTrace elementRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left <;> cases right <;>
    grind (ematch := 12) only [ExactTokenParses.result_unique, mapping_absent_conflicts_token,
      RejectAtReports.diagnostic_unique]

include successUnique disjoint in
theorem MappingTypeTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : MappingTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, MappingTypeTraceParses elementTrace source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases parsed
  cases rejection <;>
    grind (ematch := 12) only [ExactTokenParses.result_unique, mapping_absent_conflicts_token]

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeMappingTypeTraceAgreementProperties
/-! Raw mapping outcomes agree across distinct child relations. Both child
positions use heterogeneous agreement, keeping key events before value events
and the exact first failed stage. No recursive uniqueness is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {leftParses rightParses : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {leftRejects rightRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

private theorem mappingTrace_absent_conflicts_token {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (token : ExactTokenParses kind input span output) : False := absent ⟨span, token.1⟩

theorem mappingTypeTraceOutcomeAgreement
    (children : TraceOutcomeAgreement leftParses leftRejects rightParses rightRejects source endByte) :
    TraceOutcomeAgreement
      (MappingTypeTraceParses leftParses) (MappingTypeTraceRejects leftParses leftRejects)
      (MappingTypeTraceParses rightParses) (MappingTypeTraceRejects rightParses rightRejects) source endByte := by
  rcases children with ⟨successAgree, rejectAgree, successRejectDisjoint, rejectSuccessDisjoint⟩
  constructor
  · intro input left right afterLeft afterRight leftTrace rightTrace leftParsed rightParsed
    cases leftParsed <;> cases rightParsed <;>
      grind (ematch := 12) only [ExactTokenParses.result_unique]
  · intro input afterLeft afterRight leftReport rightReport leftTrace rightTrace leftRejected rightRejected
    cases leftRejected <;> cases rightRejected <;>
      grind (ematch := 12) only [ExactTokenParses.result_unique, mappingTrace_absent_conflicts_token,
        RejectAtReports.diagnostic_unique]
  · intro input value output events rejected report trace parsed rejection
    cases parsed <;> cases rejection <;>
      grind (ematch := 12) only [ExactTokenParses.result_unique, mappingTrace_absent_conflicts_token]
  · intro input rejected report trace value output events rejection parsed
    cases rejection <;> cases parsed <;>
      grind (ematch := 12) only [ExactTokenParses.result_unique, mappingTrace_absent_conflicts_token]

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeMappingTypeTraceProperties
/-! Exact raw mapping structure and event order without child progress or
implicit carrier assumptions. Type-dispatch lookahead is outside this seam. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem MappingTypeTraceParses.ordinary_components
    {elementParses : Remainder → Syntax.TypeExpr → Remainder → Prop}
    (elementOrdinary : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      elementParses input value output)
    {input output : Remainder} {result : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : MappingTypeTraceParses elementTrace source endByte input result output trace) :
    ∃ markerSpan openingSpan arrowSpan closingSpan afterMarker afterOpening afterKey afterArrow afterValue key value,
      ExactTokenParses (.identifier ContextualKeyword.mapping.spelling) input markerSpan afterMarker ∧
      ExactTokenParses (.symbol .leftParen) afterMarker openingSpan afterOpening ∧
      elementParses afterOpening key afterKey ∧
      ExactTokenParses (.symbol .fatArrow) afterKey arrowSpan afterArrow ∧
      elementParses afterArrow value afterValue ∧
      ExactTokenParses (.symbol .rightParen) afterValue closingSpan output ∧
      result = mappingTypeTraceValue markerSpan openingSpan closingSpan key value := by
  cases parsed with
  | parsed markerSpan openingSpan arrowSpan closingSpan marker opening key arrow value closing =>
      exact ⟨markerSpan, openingSpan, arrowSpan, closingSpan, _, _, _, _, _, _, _,
        marker, opening, elementOrdinary key, arrow, elementOrdinary value, closing, rfl⟩

theorem MappingTypeTraceParses.output_window
    (elementWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : MappingTypeTraceParses elementTrace source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed _ _ _ _ marker opening key arrow value closing =>
      rcases marker with ⟨_, rfl⟩
      rcases opening with ⟨_, rfl⟩
      rcases arrow with ⟨_, rfl⟩
      rw [closing.2]
      have keyFrame := elementWindow key
      have valueFrame := elementWindow value
      exact ⟨valueFrame.1.trans keyFrame.1, valueFrame.2.trans keyFrame.2⟩

theorem MappingTypeTraceParses.result_unique
    (elementUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      elementTrace source endByte input left afterLeft leftTrace →
      elementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Syntax.TypeExpr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : MappingTypeTraceParses elementTrace source endByte input left afterLeft leftTrace)
    (rightParsed : MappingTypeTraceParses elementTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed _ _ _ _ marker opening key arrow value closing =>
      cases rightParsed with
      | parsed _ _ _ _ otherMarker otherOpening otherKey otherArrow otherValue otherClosing =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          rcases opening.result_unique otherOpening with ⟨rfl, rfl⟩
          rcases elementUnique key otherKey with ⟨rfl, rfl, rfl⟩
          rcases arrow.result_unique otherArrow with ⟨rfl, rfl⟩
          rcases elementUnique value otherValue with ⟨rfl, rfl, rfl⟩
          rcases closing.result_unique otherClosing with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem MappingTypeTraceParses.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (elementProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : MappingTypeTraceParses elementTrace source endByte input value output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed _ _ _ _ _ _ key _ value _ => exact (elementProtected key).append (elementProtected value)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeMappingTypeTraceOutcomeProperties
/-! Raw mapping outcomes are unique and disjoint under independent child laws.
This bundle asserts neither existence nor prioritized dispatcher selection. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem mappingTypeTraceExactOutcomeSpec
    {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
    {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat}
    (elements : TraceExactOutcomeSpec elementTrace elementRejects source endByte) :
    TraceExactOutcomeSpec (MappingTypeTraceParses elementTrace)
      (MappingTypeTraceRejects elementTrace elementRejects) source endByte where
  successResultUnique := MappingTypeTraceParses.result_unique elements.successResultUnique
  rejectResultUnique := MappingTypeTraceRejects.result_unique elements.successResultUnique
    elements.rejectResultUnique elements.successRejectDisjoint
  successRejectDisjoint := MappingTypeTraceRejects.disjoint_success elements.successResultUnique
    elements.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamedTypeArgumentsRejectionTraceGrammar
/-! Named-type argument rejection is possible only after positive angle-bracket
lookahead. An absent opening delimiter is an unchanged optional success. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive NamedTypeArgumentsTraceRejects
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | present {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (openingSpan : SourceSpan)
      (opening : TokenAt input.tokens input.endIndex input.cursor { span := openingSpan, value := .symbol .less })
      (arguments : TrailingDelimitedListTraceRejects .less .greater false .typeExpr elementTrace elementRejects
        source endByte input rejected report trace) :
      NamedTypeArgumentsTraceRejects elementTrace elementRejects source endByte input rejected report trace

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamedTypeArgumentsRejectionTraceProtectionProperties
/-! Optional argument rejection protects precisely the preceding child-event
suffix. Its final unexpected-token report remains separate and uncommitted. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem NamedTypeArgumentsTraceRejects.cascadeFilters
    {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
    {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat} {text : String} {lexical : List SourceSpan}
    (successProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedTypeArgumentsTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | present _ _ arguments => exact arguments.cascadeFilters successProtected rejectProtected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamedTypeArgumentsTraceGrammar
/-! Optional named-type argument traces retain a structurally nonempty angle
list. Absence of the opening marker is a silent identity judgment. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive NamedTypeArgumentsTraceParses
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Option (NonemptyDelimitedList Syntax.TypeExpr) → Remainder → List ParseDiagnostic → Prop where
  | absent {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .less)) :
      NamedTypeArgumentsTraceParses elementTrace source endByte input none input []
  | present {input output : Remainder} {arguments : NonemptyDelimitedList Syntax.TypeExpr}
      {trace : List ParseDiagnostic}
      (parsed : TrailingDelimitedListTraceParses .less .greater false elementTrace source endByte input
        { span := arguments.span, elements := arguments.elements.toList } output trace) :
      NamedTypeArgumentsTraceParses elementTrace source endByte input (some arguments) output trace

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamedTypeArgumentsRejectionTraceProperties
/-! Exact rejection is restricted to present arguments. Independent child laws
determine the report and every event; ordinary erasure preserves the existing
selected nonempty-angle rejection rather than admitting absent arguments. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {ordinaryRejects : Remainder → Remainder → Prop} {source : SourceId} {endByte : Nat}

theorem NamedTypeArgumentsTraceRejects.opening_present
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedTypeArgumentsTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .less } := by
  cases rejection with
  | present span opening => exact ⟨span, opening⟩

theorem NamedTypeArgumentsTraceRejects.ordinary
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ordinaryRejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedTypeArgumentsTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    NamedTypeArgumentsRejects ordinaryRejects input rejected := by
  cases rejection with
  | present span opening arguments =>
      exact .selected span ⟨opening, rfl⟩ (arguments.ordinary successErases rejectErases)

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
theorem NamedTypeArgumentsTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : NamedTypeArgumentsTraceRejects elementTrace elementRejects source endByte input afterLeft leftReport leftTrace)
    (right : NamedTypeArgumentsTraceRejects elementTrace elementRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | present _ _ left =>
      cases right with
      | present _ _ right => exact left.result_unique successUnique rejectUnique disjoint right

include successUnique disjoint in
theorem NamedTypeArgumentsTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedTypeArgumentsTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ¬ ∃ arguments output events, NamedTypeArgumentsTraceParses elementTrace source endByte input arguments output events := by
  rintro ⟨arguments, output, events, parsed⟩
  cases rejection with
  | present span opening rejection =>
      cases parsed with
      | absent absent => exact absent ⟨span, opening⟩
      | present parsed => exact rejection.disjoint_success successUnique disjoint ⟨_, _, _, parsed⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamedTypeArgumentsTraceProperties
/-! Structural nonemptiness, ordinary erasure, exactness, and event protection.
Only carrier preservation and ordinary erasure require separate child laws. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem TrailingDelimitedListTraceParses.nonempty_elements {α : Type}
    {opening closing : Symbol}
    {child : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
    {input output : Remainder} {values : DelimitedList α} {trace : List ParseDiagnostic}
    (parsed : TrailingDelimitedListTraceParses opening closing false child source endByte input values output trace) :
    values.elements ≠ [] := by
  cases parsed with
  | empty _ _ allowed => contradiction
  | nonempty => simp

private theorem namedArguments_opening_token
    {input output : Remainder} {values : DelimitedList Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TrailingDelimitedListTraceParses .less .greater false elementTrace source endByte input values output trace) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .less } := by
  cases parsed with
  | empty _ _ allowed => contradiction
  | nonempty span _ marker => exact ⟨span, marker.1⟩

theorem NamedTypeArgumentsTraceParses.present_token
    {input output : Remainder} {arguments : NonemptyDelimitedList Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : NamedTypeArgumentsTraceParses elementTrace source endByte input (some arguments) output trace) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .less } := by
  cases parsed with
  | present parsed => exact namedArguments_opening_token parsed

theorem NamedTypeArgumentsTraceParses.output_window
    (elementWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {arguments : Option (NonemptyDelimitedList Syntax.TypeExpr)}
    {trace : List ParseDiagnostic}
    (parsed : NamedTypeArgumentsTraceParses elementTrace source endByte input arguments output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | absent => exact ⟨rfl, rfl⟩
  | present parsed => exact parsed.output_window elementWindow

theorem NamedTypeArgumentsTraceParses.cursor_le
    {input output : Remainder} {arguments : Option (NonemptyDelimitedList Syntax.TypeExpr)}
    {trace : List ParseDiagnostic}
    (parsed : NamedTypeArgumentsTraceParses elementTrace source endByte input arguments output trace) :
    input.cursor ≤ output.cursor := by
  cases parsed with
  | absent => exact Nat.le_refl _
  | present parsed => exact Nat.le_of_lt parsed.progress

theorem NamedTypeArgumentsTraceParses.some_progress
    {input output : Remainder} {arguments : NonemptyDelimitedList Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : NamedTypeArgumentsTraceParses elementTrace source endByte input (some arguments) output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | present parsed => exact parsed.progress

private theorem typeTail_of_generic {input output : Remainder} {values : List Syntax.TypeExpr}
    {closingSpan : SourceSpan}
    (parsed : TrailingDelimitedTailParses .greater TypeExprParses input values closingSpan output) :
    TypeExprTrailingDelimitedTailParses .greater input values closingSpan output := by
  induction parsed with
  | close absent token => exact .close absent token
  | trailing comma closing => exact .trailing comma closing
  | next comma absent child progress tail ih => exact .next comma absent progress rfl child ih

theorem NamedTypeArgumentsTraceParses.ordinary
    (elementOrdinary : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (elementWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {arguments : Option (NonemptyDelimitedList Syntax.TypeExpr)}
    {trace : List ParseDiagnostic}
    (parsed : NamedTypeArgumentsTraceParses elementTrace source endByte input arguments output trace) :
    OptionalNamedTypeArgumentsParses input arguments output := by
  cases parsed with
  | absent absent => exact .absent absent
  | present parsed =>
      rcases parsed.ordinary elementOrdinary elementWindow with
        ⟨openingSpan, first, afterFirst, rest, closingSpan, tokensEq, endIndexEq,
          marker, firstParsed, progress, tail, elementsEq, spanEq⟩
      exact .present openingSpan closingSpan marker progress tokensEq endIndexEq elementsEq spanEq
        firstParsed (typeTail_of_generic tail)

theorem NamedTypeArgumentsTraceParses.result_unique
    (elementUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      elementTrace source endByte input left afterLeft leftTrace →
      elementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Option (NonemptyDelimitedList Syntax.TypeExpr)}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : NamedTypeArgumentsTraceParses elementTrace source endByte input left afterLeft leftTrace)
    (rightParsed : NamedTypeArgumentsTraceParses elementTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | absent absent =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl, rfl⟩
      | present parsed => exact False.elim (absent (NamedTypeArgumentsTraceParses.present parsed).present_token)
  | present parsed =>
      cases rightParsed with
      | absent absent => exact False.elim (absent (NamedTypeArgumentsTraceParses.present parsed).present_token)
      | present other =>
          rename_i left right
          rcases parsed.result_unique elementUnique other with ⟨same, rfl, rfl⟩
          have valuesEq : left = right := by
            cases left with
            | mk leftSpan leftValues =>
                cases right with
                | mk rightSpan rightValues =>
                    cases leftValues
                    cases rightValues
                    simp only [NonemptyList.toList, DelimitedList.mk.injEq, List.cons.injEq] at same
                    rcases same with ⟨rfl, rfl, rfl⟩
                    rfl
          exact ⟨congrArg some valuesEq, rfl, rfl⟩

theorem NamedTypeArgumentsTraceParses.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (elementProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {arguments : Option (NonemptyDelimitedList Syntax.TypeExpr)}
    {trace : List ParseDiagnostic}
    (parsed : NamedTypeArgumentsTraceParses elementTrace source endByte input arguments output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | absent => exact .nil
  | present parsed => exact parsed.cascadeFilters elementProtected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamedTypeArgumentsTraceOutcomeProperties
/-! Independent optional-argument exactness fixes complete outcomes without
asserting their existence or assuming recursive type execution. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem namedTypeArgumentsTraceExactOutcomeSpec
    {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
    {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat}
    (elements : TraceExactOutcomeSpec elementTrace elementRejects source endByte) :
    TraceExactOutcomeSpec (NamedTypeArgumentsTraceParses elementTrace)
      (NamedTypeArgumentsTraceRejects elementTrace elementRejects) source endByte where
  successResultUnique := NamedTypeArgumentsTraceParses.result_unique elements.successResultUnique
  rejectResultUnique := NamedTypeArgumentsTraceRejects.result_unique elements.successResultUnique
    elements.rejectResultUnique elements.successRejectDisjoint
  successRejectDisjoint := NamedTypeArgumentsTraceRejects.disjoint_success elements.successResultUnique
    elements.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamedTypeFinishingTraceGrammar
/-! Finishing a named type has a spelling-dependent diagnostic even without
hyphens. The declaration is independent of parser state, evaluation, and fuel. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def namedTypeTraceValue (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList Syntax.TypeExpr)) : Syntax.TypeExpr := {
  span := match arguments with
    | none => name.span
    | some values => SourceSpan.cover name.span values.span
  value := .named name arguments
}

def UnqualifiedMappingSpelling (name : QualifiedName) : Prop :=
  name.value.components.tail = [] ∧ name.value.components.head.value = "mapping"

inductive NamedTypeFinishingTrace (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList Syntax.TypeExpr)) : List ParseDiagnostic → Prop where
  | canonicalRequired (spelling : UnqualifiedMappingSpelling name) :
      NamedTypeFinishingTrace name arguments [{
        span := (namedTypeTraceValue name arguments).span
        kind := .constraintViolation .mappingRequiresCanonicalForm
      }]
  | ordinary (spelling : ¬ UnqualifiedMappingSpelling name) :
      NamedTypeFinishingTrace name arguments []

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamedTypeFinishingTraceProperties
/-! Independent existence, unique complete events, and protected normalization
for named-type construction. No assumption about canonical source is needed. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem namedTypeFinishingTrace_exists (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList Syntax.TypeExpr)) :
    ∃ trace, NamedTypeFinishingTrace name arguments trace := by
  by_cases spelling : UnqualifiedMappingSpelling name
  · exact ⟨_, .canonicalRequired spelling⟩
  · exact ⟨_, .ordinary spelling⟩

theorem NamedTypeFinishingTrace.trace_unique {name : QualifiedName}
    {arguments : Option (NonemptyDelimitedList Syntax.TypeExpr)} {left right : List ParseDiagnostic}
    (leftTrace : NamedTypeFinishingTrace name arguments left)
    (rightTrace : NamedTypeFinishingTrace name arguments right) : left = right := by
  cases leftTrace <;> cases rightTrace <;> first | rfl | contradiction

theorem NamedTypeFinishingTrace.cascadeFilters {name : QualifiedName}
    {arguments : Option (NonemptyDelimitedList Syntax.TypeExpr)} {trace : List ParseDiagnostic}
    (parsed : NamedTypeFinishingTrace name arguments trace) (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | ordinary => exact .nil
  | canonicalRequired => exact parseDiagnosticCascadeFilters_protected_cons (by simp [LexicalCascadeCandidate]) .nil

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeProxyTypeRejectionTraceGrammar
/-! Raw proxy-type rejection includes an absent marker and a nested failure.
The terminal report is not appended to the child's ordered event trace. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ProxyTypeTraceRejects
    (typeRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | markerMissing {input : Remainder} {report : ParseDiagnostic}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .at))
      (reported : RejectAtReports source endByte { head := .symbol .at, tail := [] } .typeExpr input report) :
      ProxyTypeTraceRejects typeRejects source endByte input input report []
  | innerRejected {input afterMarker rejected : Remainder}
      {report : ParseDiagnostic} {trace : List ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.symbol .at) input markerSpan afterMarker)
      (typed : typeRejects source endByte afterMarker rejected report trace) :
      ProxyTypeTraceRejects typeRejects source endByte input rejected report trace

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeProxyTypeTraceGrammar
/-! Raw proxy-type success keeps the exact marker, complete nested type, and
covering span. The nested relation alone contributes ordered diagnostic events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ProxyTypeTraceParses
    (typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
      Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterMarker output : Remainder} {inner : Syntax.TypeExpr}
      {trace : List ParseDiagnostic} (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.symbol .at) input markerSpan afterMarker)
      (typed : typeTrace source endByte afterMarker inner output trace) :
      ProxyTypeTraceParses typeTrace source endByte input {
        span := SourceSpan.cover markerSpan inner.span
        value := .proxy markerSpan inner
      } output trace

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeProxyTypeTraceProperties
/-! Independent raw structure, ordinary erasure, uniqueness, and protection.
Carrier preservation and progress each require their explicit child law;
neither is hidden in the trace relation or its execution contracts. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
    Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem ProxyTypeTraceParses.marker_present
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ProxyTypeTraceParses typeTrace source endByte input value output trace) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .at } := by
  cases parsed with
  | parsed span marker _ => exact ⟨span, marker.1⟩

theorem ProxyTypeTraceParses.ordinary_components
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    (erases : ∀ {input value output trace},
      typeTrace source endByte input value output trace → typeOrdinary input value output)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ProxyTypeTraceParses typeTrace source endByte input value output trace) :
    ∃ markerSpan afterMarker inner,
      ExactTokenParses (.symbol .at) input markerSpan afterMarker ∧
      typeOrdinary afterMarker inner output ∧
      value = { span := SourceSpan.cover markerSpan inner.span, value := .proxy markerSpan inner } := by
  cases parsed with
  | parsed span marker typed => exact ⟨span, _, _, marker, erases typed, rfl⟩

theorem ProxyTypeTraceParses.ordinary
    (erases : ∀ {input value output trace},
      typeTrace source endByte input value output trace → TypeExprParses input value output)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ProxyTypeTraceParses typeTrace source endByte input value output trace) :
    TypeExprParses input value output := by
  cases parsed with
  | parsed span marker typed => exact .proxy span marker rfl (erases typed)

theorem ProxyTypeTraceParses.output_window
    (childWindow : ∀ {input value output trace},
      typeTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ProxyTypeTraceParses typeTrace source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed span marker typed => simpa only [marker.2] using childWindow typed

theorem ProxyTypeTraceParses.cursor_lt
    (childProgress : ∀ {input value output trace},
      typeTrace source endByte input value output trace → input.cursor ≤ output.cursor)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ProxyTypeTraceParses typeTrace source endByte input value output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed span marker typed =>
      have progress := childProgress typed
      rw [marker.2] at progress
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) progress

theorem ProxyTypeTraceParses.result_unique
    (unique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      typeTrace source endByte input left afterLeft leftTrace →
      typeTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Syntax.TypeExpr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : ProxyTypeTraceParses typeTrace source endByte input left afterLeft leftTrace)
    (rightParsed : ProxyTypeTraceParses typeTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed span marker typed =>
      cases rightParsed with
      | parsed otherSpan otherMarker otherTyped =>
          rcases marker.result_unique otherMarker with ⟨rfl, rfl⟩
          rcases unique typed otherTyped with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem ProxyTypeTraceParses.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (childProtected : ∀ {input value output trace},
      typeTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ProxyTypeTraceParses typeTrace source endByte input value output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed _ _ typed => exact childProtected typed

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeProxyTypeRejectionTraceProperties
/-! Independent raw rejection erasure, exactness, and event protection. The
older selected relation needs a marker guard; the outcome bundle proves only
uniqueness and disjointness, never nested-parser totality or silent diagnostics. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
    Remainder → List ParseDiagnostic → Prop}
  {typeRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem ProxyTypeTraceRejects.ordinary_cases
    {ordinaryRejects : Remainder → Remainder → Prop}
    (erases : ∀ {input rejected report trace},
      typeRejects source endByte input rejected report trace → ordinaryRejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ProxyTypeTraceRejects typeRejects source endByte input rejected report trace) :
    (TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .at) ∧ rejected = input) ∨
      ProxyTypeRejects ordinaryRejects input rejected := by
  cases rejection with
  | markerMissing absent _ => exact .inl ⟨absent, rfl⟩
  | innerRejected span marker typed => exact .inr (.innerRejected span marker (erases typed))

theorem ProxyTypeTraceRejects.ordinary_of_marker_present
    {ordinaryRejects : Remainder → Remainder → Prop}
    (erases : ∀ {input rejected report trace},
      typeRejects source endByte input rejected report trace → ordinaryRejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (selected : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .at })
    (rejection : ProxyTypeTraceRejects typeRejects source endByte input rejected report trace) :
    ProxyTypeRejects ordinaryRejects input rejected := by
  rcases rejection.ordinary_cases erases with missing | ordinary
  · exact False.elim (missing.1 selected)
  · exact ordinary

theorem ProxyTypeTraceRejects.result_unique
    (unique : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
      typeRejects source endByte input afterLeft leftReport leftTrace →
      typeRejects source endByte input afterRight rightReport rightTrace →
        afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : ProxyTypeTraceRejects typeRejects source endByte input afterLeft leftReport leftTrace)
    (right : ProxyTypeTraceRejects typeRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | markerMissing absent reported =>
      cases right with
      | markerMissing _ other => exact ⟨rfl, reported.diagnostic_unique other, rfl⟩
      | innerRejected span marker _ => exact False.elim (absent ⟨span, marker.1⟩)
  | innerRejected span marker typed =>
      cases right with
      | markerMissing absent _ => exact False.elim (absent ⟨span, marker.1⟩)
      | innerRejected _ otherMarker other =>
          cases marker.output_unique otherMarker
          exact unique typed other

theorem ProxyTypeTraceRejects.disjoint_success
    (disjoint : ∀ {input rejected report trace},
      typeRejects source endByte input rejected report trace →
        ¬ ∃ value output events, typeTrace source endByte input value output events)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ProxyTypeTraceRejects typeRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, ProxyTypeTraceParses typeTrace source endByte input value output events := by
  rintro ⟨_, _, _, success⟩
  cases success with
  | parsed span marker typed =>
      cases rejection with
      | markerMissing absent _ => exact absent ⟨span, marker.1⟩
      | innerRejected _ otherMarker rejectedType =>
          cases marker.output_unique otherMarker
          exact disjoint rejectedType ⟨_, _, _, typed⟩

theorem ProxyTypeTraceRejects.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (childProtected : ∀ {input rejected report trace},
      typeRejects source endByte input rejected report trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ProxyTypeTraceRejects typeRejects source endByte input rejected report trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | markerMissing => exact .nil
  | innerRejected _ _ typed => exact childProtected typed

theorem proxyTypeTraceExactOutcomeSpec
    (types : TraceExactOutcomeSpec typeTrace typeRejects source endByte) :
    TraceExactOutcomeSpec (ProxyTypeTraceParses typeTrace)
      (ProxyTypeTraceRejects typeRejects) source endByte where
  successResultUnique := ProxyTypeTraceParses.result_unique types.successResultUnique
  rejectResultUnique := ProxyTypeTraceRejects.result_unique types.rejectResultUnique
  successRejectDisjoint := ProxyTypeTraceRejects.disjoint_success types.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeQualifiedNameTraceGrammar
/-! Independent maximal dotted-name success with checked spelling events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Forward components following an already consumed first identifier. Dots
are silent; the first position without a dot ends the complete suffix. -/
inductive DottedIdentifierTailTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → List Syntax.Identifier → Remainder → List ParseDiagnostic → Prop where
  | done {input : Remainder}
      (stopped : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .dot)) :
      DottedIdentifierTailTraceParses source endByte input [] input []
  | next {input afterDot afterComponent output : Remainder}
      {component : Syntax.Identifier} {components : List Syntax.Identifier}
      {headTrace tailTrace : List ParseDiagnostic}
      (dotSpan : SourceSpan)
      (dot : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (name : IdentifierTraceParses afterDot component afterComponent headTrace)
      (tail : DottedIdentifierTailTraceParses source endByte afterComponent components output tailTrace) :
      DottedIdentifierTailTraceParses source endByte input (component :: components)
        output (headTrace ++ tailTrace)

/-- Finish an existing forward prefix with a newly recognized suffix. The
separate previous last component also permits arbitrary prefix accumulator use. -/
def qualifiedNameFromSuffix (first last : Syntax.Identifier)
    (previous suffix : List Syntax.Identifier) : Syntax.QualifiedName :=
  { span := SourceSpan.cover first.span (finalIdentifier last suffix).span
    value := { components := { head := first, tail := previous ++ suffix } } }

/-- Assemble a nonempty forward component list and its complete covering span. -/
def tracedQualifiedName (first : Syntax.Identifier) (components : List Syntax.Identifier) : Syntax.QualifiedName :=
  qualifiedNameFromSuffix first first [] components

/-- One checked first identifier followed by every available dotted component. -/
inductive QualifiedNameTraceParses (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.QualifiedName → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterFirst output : Remainder} {first : Syntax.Identifier}
      {components : List Syntax.Identifier} {firstTrace tailTrace : List ParseDiagnostic}
      (head : IdentifierTraceParses input first afterFirst firstTrace)
      (tail : DottedIdentifierTailTraceParses source endByte afterFirst components output tailTrace) :
      QualifiedNameTraceParses source endByte input (tracedQualifiedName first components)
        output (firstTrace ++ tailTrace)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamedTypeTraceGrammar
/-! Raw named-type success independently composes the checked qualified name,
optional nonempty arguments, and final spelling diagnostics, in that order.
Type-dispatch priority guards are deliberately not part of this raw judgment. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive NamedTypeTraceParses
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterName output : Remainder} {name : QualifiedName}
      {arguments : Option (NonemptyDelimitedList Syntax.TypeExpr)}
      {nameEvents argumentEvents finishingEvents : List ParseDiagnostic}
      (nameParsed : QualifiedNameTraceParses source endByte input name afterName nameEvents)
      (argumentsParsed : NamedTypeArgumentsTraceParses elementTrace source endByte
        afterName arguments output argumentEvents)
      (finished : NamedTypeFinishingTrace name arguments finishingEvents) :
      NamedTypeTraceParses elementTrace source endByte input (namedTypeTraceValue name arguments)
        output (nameEvents ++ argumentEvents ++ finishingEvents)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeQualifiedNameRejectionTraceGrammar
/-! Independent dotted-name rejection reports and earlier checked-name events.
An absent dot ends a successful tail; only a selected dot can expose failure. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive DottedIdentifierTailTraceRejects (context : ParseContext)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | componentRejected {input afterDot : Remainder} {report : ParseDiagnostic}
      (dotSpan : SourceSpan)
      (dot : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (absent : IdentifierAbsentAt afterDot)
      (reported : RejectAtReports source endByte { head := .identifier, tail := [] }
        context afterDot report) :
      DottedIdentifierTailTraceRejects context source endByte input afterDot report []
  | laterRejected {input afterDot afterComponent rejected : Remainder}
      {component : Syntax.Identifier} {report : ParseDiagnostic}
      {headTrace tailTrace : List ParseDiagnostic}
      (dotSpan : SourceSpan)
      (dot : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (name : IdentifierTraceParses afterDot component afterComponent headTrace)
      (tail : DottedIdentifierTailTraceRejects context source endByte
        afterComponent rejected report tailTrace) :
      DottedIdentifierTailTraceRejects context source endByte input rejected report
        (headTrace ++ tailTrace)

inductive QualifiedNameTraceRejects (context : ParseContext)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | firstRejected {input : Remainder} {report : ParseDiagnostic}
      (absent : IdentifierAbsentAt input)
      (reported : RejectAtReports source endByte { head := .identifier, tail := [] }
        context input report) :
      QualifiedNameTraceRejects context source endByte input input report []
  | tailRejected {input afterFirst rejected : Remainder}
      {first : Syntax.Identifier} {report : ParseDiagnostic}
      {firstTrace tailTrace : List ParseDiagnostic}
      (head : IdentifierTraceParses input first afterFirst firstTrace)
      (tail : DottedIdentifierTailTraceRejects context source endByte
        afterFirst rejected report tailTrace) :
      QualifiedNameTraceRejects context source endByte input rejected report
        (firstTrace ++ tailTrace)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamedTypeRejectionTraceGrammar
/-! Raw named-type rejection stops at the qualified name or its optional
arguments. The finishing spelling event occurs only after both succeed. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive NamedTypeTraceRejects
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | nameRejected {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (name : QualifiedNameTraceRejects .typeExpr source endByte input rejected report trace) :
      NamedTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace
  | argumentsRejected {input afterName rejected : Remainder} {name : QualifiedName}
      {report : ParseDiagnostic} {nameEvents argumentEvents : List ParseDiagnostic}
      (nameParsed : QualifiedNameTraceParses source endByte input name afterName nameEvents)
      (arguments : NamedTypeArgumentsTraceRejects elementTrace elementRejects
        source endByte afterName rejected report argumentEvents) :
      NamedTypeTraceRejects elementTrace elementRejects source endByte input rejected report
        (nameEvents ++ argumentEvents)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeQualifiedNameTraceProperties
/-! Carrier, ordinary erasure, exactness, and protected dotted-name events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem DottedIdentifierTailTraceParses.ordinary
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {components : List Syntax.Identifier} {trace : List ParseDiagnostic}
    (parsed : DottedIdentifierTailTraceParses source endByte input components output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex ∧
      DottedIdentifierTailParses input.tokens input.endIndex input.cursor components output.cursor := by
  induction parsed with
  | done stopped => exact ⟨rfl, rfl, .done _ stopped⟩
  | next dotSpan dot name tail ih =>
      rcases dot with ⟨dotToken, rfl⟩
      rcases identifierTraceParses_iff.mp name with ⟨ordinary, _⟩
      refine ⟨ih.1.trans ordinary.2.1, ih.2.1.trans ordinary.2.2.1,
        .next dotSpan dotToken ordinary.1 ?_⟩
      simpa only [ordinary.2.1, ordinary.2.2.1, ordinary.2.2.2, Nat.add_assoc] using ih.2.2

theorem DottedIdentifierTailTraceParses.output_window
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {components : List Syntax.Identifier} {trace : List ParseDiagnostic}
    (parsed : DottedIdentifierTailTraceParses source endByte input components output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex :=
  ⟨parsed.ordinary.1, parsed.ordinary.2.1⟩

theorem DottedIdentifierTailTraceParses.cursor_eq
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {components : List Syntax.Identifier} {trace : List ParseDiagnostic}
    (parsed : DottedIdentifierTailTraceParses source endByte input components output trace) :
    output.cursor = input.cursor + 2 * components.length := by
  induction parsed with
  | done => simp
  | next dotSpan dot name tail ih =>
      have nameCursor := (identifierTraceParses_iff.mp name).1.2.2.2
      rcases dot with ⟨_, rfl⟩
      simp only [List.length_cons] at ⊢
      simp only at nameCursor
      omega

theorem QualifiedNameTraceParses.ordinary
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {name : Syntax.QualifiedName} {trace : List ParseDiagnostic}
    (parsed : QualifiedNameTraceParses source endByte input name output trace) :
    QualifiedNameParses input name output := by
  cases parsed with
  | parsed head tail =>
      have first := (identifierTraceParses_iff.mp head).1
      have rest := tail.ordinary
      refine ⟨rest.1.trans first.2.1, rest.2.1.trans first.2.2.1, first.1, ?_, rfl⟩
      simpa only [first.2.1, first.2.2.1, first.2.2.2, tracedQualifiedName,
        qualifiedNameFromSuffix, List.nil_append] using rest.2.2

theorem QualifiedNameTraceParses.output_window
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {name : Syntax.QualifiedName} {trace : List ParseDiagnostic}
    (parsed : QualifiedNameTraceParses source endByte input name output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex :=
  ⟨parsed.ordinary.1, parsed.ordinary.2.1⟩

theorem QualifiedNameTraceParses.cursor_lt
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {name : Syntax.QualifiedName} {trace : List ParseDiagnostic}
    (parsed : QualifiedNameTraceParses source endByte input name output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed head tail =>
      have first := (identifierTraceParses_iff.mp head).1.2.2.2
      have rest := tail.cursor_eq
      omega

theorem DottedIdentifierTailTraceParses.result_unique
    {source : SourceId} {endByte : Nat} {input afterLeft afterRight : Remainder}
    {left right : List Syntax.Identifier} {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : DottedIdentifierTailTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : DottedIdentifierTailTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  induction leftParsed generalizing right afterRight rightTrace with
  | done stopped =>
      cases rightParsed with
      | done => exact ⟨rfl, rfl, rfl⟩
      | next dotSpan dot => exact False.elim (stopped ⟨dotSpan, dot.1⟩)
  | next dotSpan dot name tail ih =>
      cases rightParsed with
      | done stopped => exact False.elim (stopped ⟨dotSpan, dot.1⟩)
      | next otherSpan otherDot otherName otherTail =>
          have afterDotEq := dot.2.trans otherDot.2.symm
          cases afterDotEq
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          rcases ih otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem QualifiedNameTraceParses.result_unique
    {source : SourceId} {endByte : Nat} {input afterLeft afterRight : Remainder}
    {left right : Syntax.QualifiedName} {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : QualifiedNameTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : QualifiedNameTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed head tail =>
      cases rightParsed with
      | parsed otherHead otherTail =>
          rcases head.result_unique otherHead with ⟨rfl, rfl, rfl⟩
          rcases tail.result_unique otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem DottedIdentifierTailTraceParses.cascadeFilters
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {components : List Syntax.Identifier} {trace : List ParseDiagnostic}
    (parsed : DottedIdentifierTailTraceParses source endByte input components output trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  induction parsed with
  | done => exact .nil
  | next _ _ name _ ih => exact (name.cascadeFilters text lexical).append ih

theorem QualifiedNameTraceParses.cascadeFilters
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {name : Syntax.QualifiedName} {trace : List ParseDiagnostic}
    (parsed : QualifiedNameTraceParses source endByte input name output trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed head tail => exact (head.cascadeFilters text lexical).append (tail.cascadeFilters text lexical)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamedTypeTraceProperties
/-! Raw named types preserve exact structure and every event occurrence.
Ordinary erasure is componentwise: selecting the prioritized type-expression
branch requires separate dispatch guards and is outside this raw boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem NamedTypeTraceParses.ordinary_components
    (elementOrdinary : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (elementWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : NamedTypeTraceParses elementTrace source endByte input value output trace) :
    ∃ name afterName arguments, QualifiedNameParses input name afterName ∧
      OptionalNamedTypeArgumentsParses afterName arguments output ∧ value = namedTypeTraceValue name arguments := by
  cases parsed with
  | parsed name arguments finished =>
      exact ⟨_, _, _, name.ordinary, arguments.ordinary elementOrdinary elementWindow, rfl⟩

theorem NamedTypeTraceParses.output_window
    (elementWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : NamedTypeTraceParses elementTrace source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed name arguments finished =>
      have frame := arguments.output_window elementWindow
      exact ⟨frame.1.trans name.output_window.1, frame.2.trans name.output_window.2⟩

theorem NamedTypeTraceParses.progress
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : NamedTypeTraceParses elementTrace source endByte input value output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed name arguments finished => exact Nat.lt_of_lt_of_le name.cursor_lt arguments.cursor_le

theorem NamedTypeTraceParses.result_unique
    (elementUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      elementTrace source endByte input left afterLeft leftTrace →
      elementTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Syntax.TypeExpr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : NamedTypeTraceParses elementTrace source endByte input left afterLeft leftTrace)
    (rightParsed : NamedTypeTraceParses elementTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed name arguments finished =>
      cases rightParsed with
      | parsed otherName otherArguments otherFinished =>
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          rcases arguments.result_unique elementUnique otherArguments with ⟨rfl, rfl, rfl⟩
          cases finished.trace_unique otherFinished
          exact ⟨rfl, rfl, rfl⟩

theorem NamedTypeTraceParses.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (elementProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : NamedTypeTraceParses elementTrace source endByte input value output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed name arguments finished =>
      exact ((name.cascadeFilters text lexical).append (arguments.cascadeFilters elementProtected)).append
        (finished.cascadeFilters text lexical)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeQualifiedNameRejectionTraceProperties
/-! Exact rejected dotted names preserve only the preceding spelling events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem DottedIdentifierTailTraceRejects.ordinary
    {context : ParseContext} {source : SourceId} {endByte : Nat}
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DottedIdentifierTailTraceRejects context source endByte input rejected report trace) :
    TypeQualifiedNameTailRejects input rejected := by
  induction rejection with
  | componentRejected span dot absent => exact .componentRejected span dot (.absent absent)
  | laterRejected span dot name tail ih =>
      exact .laterRejected span dot (identifierTraceParses_iff.mp name).1 ih

theorem QualifiedNameTraceRejects.ordinary
    {context : ParseContext} {source : SourceId} {endByte : Nat}
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : QualifiedNameTraceRejects context source endByte input rejected report trace) :
    TypeQualifiedNameRejects input rejected := by
  cases rejection with
  | firstRejected absent => exact .firstRejected (.absent absent)
  | tailRejected head tail => exact .tailRejected (identifierTraceParses_iff.mp head).1 tail.ordinary

theorem DottedIdentifierTailTraceRejects.output_window
    {context : ParseContext} {source : SourceId} {endByte : Nat}
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DottedIdentifierTailTraceRejects context source endByte input rejected report trace) :
    rejected.tokens = input.tokens ∧ rejected.endIndex = input.endIndex := by
  induction rejection with
  | componentRejected span dot => rcases dot with ⟨_, rfl⟩; exact ⟨rfl, rfl⟩
  | laterRejected span dot name tail ih =>
      rcases dot with ⟨_, rfl⟩
      have ordinary := (identifierTraceParses_iff.mp name).1
      exact ⟨ih.1.trans ordinary.2.1, ih.2.trans ordinary.2.2.1⟩

theorem QualifiedNameTraceRejects.output_window
    {context : ParseContext} {source : SourceId} {endByte : Nat}
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : QualifiedNameTraceRejects context source endByte input rejected report trace) :
    rejected.tokens = input.tokens ∧ rejected.endIndex = input.endIndex := by
  cases rejection with
  | firstRejected => exact ⟨rfl, rfl⟩
  | tailRejected head tail =>
      have ordinary := (identifierTraceParses_iff.mp head).1
      exact ⟨tail.output_window.1.trans ordinary.2.1, tail.output_window.2.trans ordinary.2.2.1⟩

theorem DottedIdentifierTailTraceRejects.result_unique
    {context : ParseContext} {source : SourceId} {endByte : Nat}
    {input afterLeft afterRight : Remainder} {left right : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : DottedIdentifierTailTraceRejects context source endByte input afterLeft left leftTrace)
    (rightRejected : DottedIdentifierTailTraceRejects context source endByte input afterRight right rightTrace) :
    afterLeft = afterRight ∧ left = right ∧ leftTrace = rightTrace := by
  induction leftRejected generalizing afterRight right rightTrace with
  | componentRejected span dot absent reported =>
      cases rightRejected with
      | componentRejected otherSpan otherDot otherAbsent otherReport =>
          have same := dot.2.trans otherDot.2.symm
          cases same
          exact ⟨rfl, reported.diagnostic_unique otherReport, rfl⟩
      | laterRejected otherSpan otherDot name tail =>
          have same := dot.2.trans otherDot.2.symm
          cases same
          exact False.elim (absent ⟨_, _, (identifierTraceParses_iff.mp name).1.1⟩)
  | laterRejected span dot name tail ih =>
      cases rightRejected with
      | componentRejected otherSpan otherDot absent reported =>
          have same := dot.2.trans otherDot.2.symm
          cases same
          exact False.elim (absent ⟨_, _, (identifierTraceParses_iff.mp name).1.1⟩)
      | laterRejected otherSpan otherDot otherName otherTail =>
          have same := dot.2.trans otherDot.2.symm
          cases same
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          rcases ih otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem QualifiedNameTraceRejects.result_unique
    {context : ParseContext} {source : SourceId} {endByte : Nat}
    {input afterLeft afterRight : Remainder} {left right : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : QualifiedNameTraceRejects context source endByte input afterLeft left leftTrace)
    (rightRejected : QualifiedNameTraceRejects context source endByte input afterRight right rightTrace) :
    afterLeft = afterRight ∧ left = right ∧ leftTrace = rightTrace := by
  cases leftRejected with
  | firstRejected absent reported =>
      cases rightRejected with
      | firstRejected otherAbsent otherReport => exact ⟨rfl, reported.diagnostic_unique otherReport, rfl⟩
      | tailRejected head tail =>
          exact False.elim (absent ⟨_, _, (identifierTraceParses_iff.mp head).1.1⟩)
  | tailRejected head tail =>
      cases rightRejected with
      | firstRejected absent reported =>
          exact False.elim (absent ⟨_, _, (identifierTraceParses_iff.mp head).1.1⟩)
      | tailRejected otherHead otherTail =>
          rcases head.result_unique otherHead with ⟨rfl, rfl, rfl⟩
          rcases tail.result_unique otherTail with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem DottedIdentifierTailTraceRejects.disjoint_success
    {context : ParseContext} {source : SourceId} {endByte : Nat}
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DottedIdentifierTailTraceRejects context source endByte input rejected report trace) :
    ¬ ∃ components output successTrace,
      DottedIdentifierTailTraceParses source endByte input components output successTrace := by
  rintro ⟨components, output, successTrace, parsed⟩
  exact rejection.ordinary.disjointDotted ⟨components, output.cursor, parsed.ordinary.2.2⟩

theorem QualifiedNameTraceRejects.disjoint_success
    {context : ParseContext} {source : SourceId} {endByte : Nat}
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : QualifiedNameTraceRejects context source endByte input rejected report trace) :
    ¬ ∃ name output successTrace,
      QualifiedNameTraceParses source endByte input name output successTrace := by
  rintro ⟨name, output, successTrace, parsed⟩
  exact rejection.ordinary.disjointQualified ⟨name, output, parsed.ordinary⟩

theorem DottedIdentifierTailTraceRejects.cascadeFilters
    {context : ParseContext} {source : SourceId} {endByte : Nat}
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DottedIdentifierTailTraceRejects context source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  induction rejection with
  | componentRejected => exact .nil
  | laterRejected _ _ name _ ih => exact (name.cascadeFilters text lexical).append ih

theorem QualifiedNameTraceRejects.cascadeFilters
    {context : ParseContext} {source : SourceId} {endByte : Nat}
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : QualifiedNameTraceRejects context source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | firstRejected => exact .nil
  | tailRejected head tail => exact (head.cascadeFilters text lexical).append (tail.cascadeFilters text lexical)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamedTypeRejectionTraceProperties
/-! Raw named-type rejection erases to the existing raw branch rejection.
It does not claim the type dispatcher's extra branch-selection conditions. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {ordinaryRejects : Remainder → Remainder → Prop} {source : SourceId} {endByte : Nat}

theorem NamedTypeTraceRejects.ordinary
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ordinaryRejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    NamedTypeRejects ordinaryRejects input rejected := by
  cases rejection with
  | nameRejected name => exact .nameRejected name.ordinary
  | argumentsRejected name arguments =>
      exact .argumentsRejected name.ordinary (arguments.ordinary successErases rejectErases)

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
theorem NamedTypeTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : NamedTypeTraceRejects elementTrace elementRejects source endByte input afterLeft leftReport leftTrace)
    (right : NamedTypeTraceRejects elementTrace elementRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | nameRejected name =>
      cases right with
      | nameRejected other => exact name.result_unique other
      | argumentsRejected other arguments => exact False.elim (name.disjoint_success ⟨_, _, _, other⟩)
  | argumentsRejected name arguments =>
      cases right with
      | nameRejected other => exact False.elim (other.disjoint_success ⟨_, _, _, name⟩)
      | argumentsRejected otherName otherArguments =>
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          rcases arguments.result_unique successUnique rejectUnique disjoint otherArguments with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

include successUnique disjoint in
theorem NamedTypeTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, NamedTypeTraceParses elementTrace source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases parsed with
  | parsed name arguments finishing =>
      cases rejection with
      | nameRejected rejected => exact rejected.disjoint_success ⟨_, _, _, name⟩
      | argumentsRejected otherName rejected =>
          rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
          exact rejected.disjoint_success successUnique disjoint ⟨_, _, _, arguments⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamedTypeRejectionTraceProtectionProperties
/-! Earlier checked names and protected argument-child events remain in full
order on rejection. The final unexpected report is never committed here. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem NamedTypeTraceRejects.cascadeFilters
    {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
    {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat} {text : String} {lexical : List SourceSpan}
    (successProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | nameRejected name => exact name.cascadeFilters text lexical
  | argumentsRejected name arguments =>
      exact (name.cascadeFilters text lexical).append (arguments.cascadeFilters successProtected rejectProtected)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamedTypeTraceOutcomeProperties
/-! Raw named-type joint exactness under independent recursive child laws.
Neither existence nor the prioritized type dispatch is asserted here. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem namedTypeTraceExactOutcomeSpec
    {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
    {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat}
    (elements : TraceExactOutcomeSpec elementTrace elementRejects source endByte) :
    TraceExactOutcomeSpec (NamedTypeTraceParses elementTrace)
      (NamedTypeTraceRejects elementTrace elementRejects) source endByte where
  successResultUnique := NamedTypeTraceParses.result_unique elements.successResultUnique
  rejectResultUnique := NamedTypeTraceRejects.result_unique elements.successResultUnique
    elements.rejectResultUnique elements.successRejectDisjoint
  successRejectDisjoint := NamedTypeTraceRejects.disjoint_success elements.successResultUnique
    elements.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeNamedTypeTraceAgreementProperties
/-! Distinct child relations agree through optional arguments and raw named
types. Name checks and finishing events stay in their original order. No
functionality of either child relation by itself is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {leftParses rightParses : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {leftRejects rightRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem namedTypeArgumentsTraceOutcomeAgreement
    (children : TraceOutcomeAgreement leftParses leftRejects rightParses rightRejects source endByte) :
    TraceOutcomeAgreement (NamedTypeArgumentsTraceParses leftParses)
      (NamedTypeArgumentsTraceRejects leftParses leftRejects)
      (NamedTypeArgumentsTraceParses rightParses)
      (NamedTypeArgumentsTraceRejects rightParses rightRejects) source endByte where
  successResultAgree left right := by
    cases left with
    | absent absent =>
        cases right with
        | absent => exact ⟨rfl, rfl, rfl⟩
        | present parsed => exact False.elim (absent (NamedTypeArgumentsTraceParses.present parsed).present_token)
    | present parsed =>
        cases right with
        | absent absent => exact False.elim (absent (NamedTypeArgumentsTraceParses.present parsed).present_token)
        | present other =>
            rename_i left right
            rcases parsed.result_agree children.successResultAgree other with ⟨same, rfl, rfl⟩
            have valuesEq : left = right := by
              cases left with
              | mk leftSpan leftValues =>
                  cases right with
                  | mk rightSpan rightValues =>
                      cases leftValues
                      cases rightValues
                      simp only [NonemptyList.toList, DelimitedList.mk.injEq, List.cons.injEq] at same
                      rcases same with ⟨rfl, rfl, rfl⟩
                      rfl
            exact ⟨congrArg some valuesEq, rfl, rfl⟩
  rejectResultAgree left right := by
    cases left with
    | present _ _ left =>
        cases right with
        | present _ _ right => exact left.result_agree children right
  successRejectDisjoint parsed rejection := by
    cases rejection with
    | present span opening rejection =>
        cases parsed with
        | absent absent => exact absent ⟨span, opening⟩
        | present parsed => exact parsed.disjoint_rejection_of_agreement children rejection
  rejectSuccessDisjoint rejection parsed := by
    cases rejection with
    | present span opening rejection =>
        cases parsed with
        | absent absent => exact absent ⟨span, opening⟩
        | present parsed => exact rejection.disjoint_success_of_agreement children parsed

theorem namedTypeTraceOutcomeAgreement
    (children : TraceOutcomeAgreement leftParses leftRejects rightParses rightRejects source endByte) :
    TraceOutcomeAgreement (NamedTypeTraceParses leftParses)
      (NamedTypeTraceRejects leftParses leftRejects)
      (NamedTypeTraceParses rightParses)
      (NamedTypeTraceRejects rightParses rightRejects) source endByte where
  successResultAgree left right := by
    cases left with
    | parsed name arguments finished =>
        cases right with
        | parsed otherName otherArguments otherFinished =>
            rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
            rcases (namedTypeArgumentsTraceOutcomeAgreement children).successResultAgree
              arguments otherArguments with ⟨rfl, rfl, rfl⟩
            cases finished.trace_unique otherFinished
            exact ⟨rfl, rfl, rfl⟩
  rejectResultAgree left right := by
    cases left with
    | nameRejected name =>
        cases right with
        | nameRejected other => exact name.result_unique other
        | argumentsRejected other _ => exact False.elim (name.disjoint_success ⟨_, _, _, other⟩)
    | argumentsRejected name arguments =>
        cases right with
        | nameRejected other => exact False.elim (other.disjoint_success ⟨_, _, _, name⟩)
        | argumentsRejected otherName otherArguments =>
            rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
            rcases (namedTypeArgumentsTraceOutcomeAgreement children).rejectResultAgree
              arguments otherArguments with ⟨rfl, rfl, rfl⟩
            exact ⟨rfl, rfl, rfl⟩
  successRejectDisjoint parsed rejection := by
    cases parsed with
    | parsed name arguments _ =>
        cases rejection with
        | nameRejected rejected => exact rejected.disjoint_success ⟨_, _, _, name⟩
        | argumentsRejected otherName rejected =>
            rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
            exact (namedTypeArgumentsTraceOutcomeAgreement children).successRejectDisjoint arguments rejected
  rejectSuccessDisjoint rejection parsed := by
    cases parsed with
    | parsed name arguments _ =>
        cases rejection with
        | nameRejected rejected => exact rejected.disjoint_success ⟨_, _, _, name⟩
        | argumentsRejected otherName rejected =>
            rcases name.result_unique otherName with ⟨rfl, rfl, rfl⟩
            exact (namedTypeArgumentsTraceOutcomeAgreement children).rejectSuccessDisjoint rejected arguments

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeQualifiedNameTraceOutcomeProperties
/-! Unconditional joint exactness for maximal checked qualified names and
their dotted tails. These bundles assert uniqueness/disjointness, not existence. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem dottedIdentifierTailTraceExactOutcomeSpec (context : ParseContext)
    (source : SourceId) (endByte : Nat) :
    TraceExactOutcomeSpec DottedIdentifierTailTraceParses
      (DottedIdentifierTailTraceRejects context) source endByte where
  successResultUnique := DottedIdentifierTailTraceParses.result_unique
  rejectResultUnique := DottedIdentifierTailTraceRejects.result_unique
  successRejectDisjoint := DottedIdentifierTailTraceRejects.disjoint_success

theorem qualifiedNameTraceExactOutcomeSpec (context : ParseContext)
    (source : SourceId) (endByte : Nat) :
    TraceExactOutcomeSpec QualifiedNameTraceParses
      (QualifiedNameTraceRejects context) source endByte where
  successResultUnique := QualifiedNameTraceParses.result_unique
  rejectResultUnique := QualifiedNameTraceRejects.result_unique
  successRejectDisjoint := QualifiedNameTraceRejects.disjoint_success

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeSimpleTypeTraceAgreementProperties
/-! Heterogeneous child agreement lifts through raw proxy and comptime types.
All comparisons are directly between the two child relations. No same-relation
type uniqueness, recursive existence, progress, or carrier law is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {leftParses rightParses : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {leftRejects rightRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

private theorem simpleTrace_absent_conflicts_token {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (token : ExactTokenParses kind input span output) : False := absent ⟨span, token.1⟩

theorem proxyTypeTraceOutcomeAgreement
    (children : TraceOutcomeAgreement leftParses leftRejects rightParses rightRejects source endByte) :
    TraceOutcomeAgreement (ProxyTypeTraceParses leftParses) (ProxyTypeTraceRejects leftRejects)
      (ProxyTypeTraceParses rightParses) (ProxyTypeTraceRejects rightRejects) source endByte := by
  rcases children with ⟨successAgree, rejectAgree, successRejectDisjoint, rejectSuccessDisjoint⟩
  constructor
  · intro input left right afterLeft afterRight leftTrace rightTrace leftParsed rightParsed
    cases leftParsed <;> cases rightParsed <;>
      grind only [ExactTokenParses.result_unique]
  · intro input afterLeft afterRight leftReport rightReport leftTrace rightTrace leftRejected rightRejected
    cases leftRejected <;> cases rightRejected <;>
      grind only [ExactTokenParses.result_unique, simpleTrace_absent_conflicts_token,
        RejectAtReports.diagnostic_unique]
  · intro input value output events rejected report trace parsed rejection
    cases parsed <;> cases rejection <;>
      grind only [ExactTokenParses.result_unique, simpleTrace_absent_conflicts_token]
  · intro input rejected report trace value output events rejection parsed
    cases rejection <;> cases parsed <;>
      grind only [ExactTokenParses.result_unique, simpleTrace_absent_conflicts_token]

/-- Marker, opening, child, and closing failures retain their first-failure
order on both sides. The child trace is the only emitted event sequence. -/
theorem comptimeTypeTraceOutcomeAgreement
    (children : TraceOutcomeAgreement leftParses leftRejects rightParses rightRejects source endByte) :
    TraceOutcomeAgreement
      (ComptimeTypeTraceParses leftParses) (ComptimeTypeTraceRejects leftParses leftRejects)
      (ComptimeTypeTraceParses rightParses) (ComptimeTypeTraceRejects rightParses rightRejects) source endByte := by
  rcases children with ⟨successAgree, rejectAgree, successRejectDisjoint, rejectSuccessDisjoint⟩
  constructor
  · intro input left right afterLeft afterRight leftTrace rightTrace leftParsed rightParsed
    cases leftParsed <;> cases rightParsed <;>
      grind (ematch := 12) only [ExactTokenParses.result_unique]
  · intro input afterLeft afterRight leftReport rightReport leftTrace rightTrace leftRejected rightRejected
    cases leftRejected <;> cases rightRejected <;>
      grind (ematch := 12) only [ExactTokenParses.result_unique, simpleTrace_absent_conflicts_token,
        RejectAtReports.diagnostic_unique]
  · intro input value output events rejected report trace parsed rejection
    cases parsed <;> cases rejection <;>
      grind (ematch := 12) only [ExactTokenParses.result_unique, simpleTrace_absent_conflicts_token]
  · intro input rejected report trace value output events rejection parsed
    cases rejection <;> cases parsed <;>
      grind (ematch := 12) only [ExactTokenParses.result_unique, simpleTrace_absent_conflicts_token]

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTupleTypeRejectionTraceGrammar
/-! Raw tuple rejection is precisely the trailing-enabled parenthesized-list
rejection, including an absent opening marker. The final report is uncommitted. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

abbrev TupleTypeTraceRejects
    (typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
      Remainder → List ParseDiagnostic → Prop)
    (typeRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :=
  TrailingDelimitedListTraceRejects .leftParen .rightParen true .typeExpr
    typeTrace typeRejects source endByte

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTupleTypeTraceGrammar
/-! Raw tuple-type success maps the complete trailing-enabled list to a type,
including empty and singleton lists. It never introduces expression grouping. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

def tupleTypeTraceValue (values : DelimitedList Syntax.TypeExpr) : Syntax.TypeExpr :=
  { span := values.span, value := .tuple values.elements }

inductive TupleTypeTraceParses
    (typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
      Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop where
  | parsed {input output : Remainder} {values : DelimitedList Syntax.TypeExpr}
      {trace : List ParseDiagnostic}
      (elements : TrailingDelimitedListTraceParses .leftParen .rightParen true
        typeTrace source endByte input values output trace) :
      TupleTypeTraceParses typeTrace source endByte input (tupleTypeTraceValue values) output trace

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTupleTypeTraceAgreementProperties
/-! Pairwise child outcome agreement lifts through the raw tuple list. Neither
child relation needs its own functionality, existence, or carrier law. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {leftParses rightParses : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {leftRejects rightRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem tupleTypeTraceOutcomeAgreement
    (children : TraceOutcomeAgreement leftParses leftRejects rightParses rightRejects source endByte) :
    TraceOutcomeAgreement (TupleTypeTraceParses leftParses) (TupleTypeTraceRejects leftParses leftRejects)
      (TupleTypeTraceParses rightParses) (TupleTypeTraceRejects rightParses rightRejects) source endByte where
  successResultAgree left right := by
    cases left with
    | parsed elements =>
        cases right with
        | parsed other =>
            rcases elements.result_agree children.successResultAgree other with ⟨rfl, rfl, rfl⟩
            exact ⟨rfl, rfl, rfl⟩
  rejectResultAgree left right := left.result_agree children right
  successRejectDisjoint parsed rejected := by
    cases parsed with
    | parsed elements => exact elements.disjoint_rejection_of_agreement children rejected
  rejectSuccessDisjoint rejected parsed := by
    cases parsed with
    | parsed elements => exact rejected.disjoint_success_of_agreement children elements

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTupleTypeTraceProperties
/-! Tuple types retain every list element, including empty and singleton lists.
Ordinary erasure and carrier preservation require their separate child laws;
the independent trace relation itself does not assume those laws. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
    Remainder → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

private theorem tupleTypeTail_of_generic {input output : Remainder}
    {values : List Syntax.TypeExpr} {closingSpan : SourceSpan}
    (parsed : TrailingDelimitedTailParses .rightParen TypeExprParses input values closingSpan output) :
    TypeExprTrailingDelimitedTailParses .rightParen input values closingSpan output := by
  induction parsed with
  | close absent token => exact .close absent token
  | trailing comma closing => exact .trailing comma closing
  | next comma absent child progress tail ih => exact .next comma absent progress rfl child ih

theorem TupleTypeTraceParses.ordinary
    (childOrdinary : ∀ {input value output trace},
      typeTrace source endByte input value output trace → TypeExprParses input value output)
    (childWindow : ∀ {input value output trace},
      typeTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TupleTypeTraceParses typeTrace source endByte input value output trace) :
    TypeExprParses input value output := by
  cases parsed with
  | parsed elements =>
      apply TypeExprParses.tuple rfl
      have frame := elements.output_window childWindow
      cases elements with
      | empty openingSpan closingSpan allowed marker closing =>
          rcases marker with ⟨marker, rfl⟩
          rcases closing with ⟨closing, rfl⟩
          exact .empty openingSpan closingSpan rfl rfl marker closing
      | nonempty openingSpan closingSpan marker continues first progress tail =>
          rcases marker with ⟨marker, rfl⟩
          cases continues with
          | absent absent =>
              exact .nonempty openingSpan closingSpan absent marker progress frame.1 frame.2 rfl rfl
                (childOrdinary first) (tupleTypeTail_of_generic (tail.ordinary childOrdinary))

theorem TupleTypeTraceParses.output_window
    (childWindow : ∀ {input value output trace},
      typeTrace source endByte input value output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TupleTypeTraceParses typeTrace source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed elements => exact elements.output_window childWindow

theorem TupleTypeTraceParses.progress
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TupleTypeTraceParses typeTrace source endByte input value output trace) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed elements => exact elements.progress

theorem TupleTypeTraceParses.result_unique
    (childUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      typeTrace source endByte input left afterLeft leftTrace →
      typeTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    {input afterLeft afterRight : Remainder} {left right : Syntax.TypeExpr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : TupleTypeTraceParses typeTrace source endByte input left afterLeft leftTrace)
    (rightParsed : TupleTypeTraceParses typeTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | parsed left =>
      cases rightParsed with
      | parsed right =>
          rcases left.result_unique childUnique right with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩

theorem TupleTypeTraceParses.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (childProtected : ∀ {input value output trace},
      typeTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TupleTypeTraceParses typeTrace source endByte input value output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | parsed elements => exact elements.cascadeFilters childProtected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTupleTypeRejectionTraceProperties
/-! Raw tuple rejection includes an absent opening marker. Its erasure keeps
that case separate from the selected ordinary tuple branch. Exactness concerns
uniqueness/disjointness, and protection excludes the uncommitted final report. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {typeTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
    Remainder → List ParseDiagnostic → Prop}
  {typeRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem TupleTypeTraceRejects.ordinary_cases
    {ordinaryRejects : Remainder → Remainder → Prop}
    (successErases : ∀ {input value output trace},
      typeTrace source endByte input value output trace → TypeExprParses input value output)
    (rejectErases : ∀ {input rejected report trace},
      typeRejects source endByte input rejected report trace → ordinaryRejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TupleTypeTraceRejects typeTrace typeRejects source endByte input rejected report trace) :
    (TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftParen) ∧ rejected = input) ∨
      TupleTypeRejects ordinaryRejects input rejected := by
  have ordinary := TrailingDelimitedListTraceRejects.ordinary successErases rejectErases rejection
  cases rejection with
  | openingMissing absent reported => exact .inl ⟨absent, rfl⟩
  | firstRejected span opening continues child => exact .inr (.selected span opening ordinary)
  | tailRejected span opening continues child progress tail => exact .inr (.selected span opening ordinary)

theorem TupleTypeTraceRejects.ordinary_of_opening_present
    {ordinaryRejects : Remainder → Remainder → Prop}
    (successErases : ∀ {input value output trace},
      typeTrace source endByte input value output trace → TypeExprParses input value output)
    (rejectErases : ∀ {input rejected report trace},
      typeRejects source endByte input rejected report trace → ordinaryRejects input rejected)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (opening : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .leftParen })
    (rejection : TupleTypeTraceRejects typeTrace typeRejects source endByte input rejected report trace) :
    TupleTypeRejects ordinaryRejects input rejected := by
  rcases TupleTypeTraceRejects.ordinary_cases successErases rejectErases rejection with missing | ordinary
  · exact False.elim (missing.1 opening)
  · exact ordinary

theorem TupleTypeTraceRejects.result_unique
    (successUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      typeTrace source endByte input left afterLeft leftTrace →
      typeTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    (rejectUnique : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
      typeRejects source endByte input afterLeft leftReport leftTrace →
      typeRejects source endByte input afterRight rightReport rightTrace →
        afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace)
    (disjoint : ∀ {input rejected report trace},
      typeRejects source endByte input rejected report trace →
        ¬ ∃ value output events, typeTrace source endByte input value output events)
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : TupleTypeTraceRejects typeTrace typeRejects source endByte input afterLeft leftReport leftTrace)
    (right : TupleTypeTraceRejects typeTrace typeRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace :=
  TrailingDelimitedListTraceRejects.result_unique successUnique rejectUnique disjoint left right

theorem TupleTypeTraceRejects.disjoint_success
    (successUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
      typeTrace source endByte input left afterLeft leftTrace →
      typeTrace source endByte input right afterRight rightTrace →
        left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace)
    (disjoint : ∀ {input rejected report trace},
      typeRejects source endByte input rejected report trace →
        ¬ ∃ value output events, typeTrace source endByte input value output events)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TupleTypeTraceRejects typeTrace typeRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, TupleTypeTraceParses typeTrace source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases parsed with
  | parsed elements =>
      exact TrailingDelimitedListTraceRejects.disjoint_success successUnique disjoint rejection ⟨_, _, _, elements⟩

theorem TupleTypeTraceRejects.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (successProtected : ∀ {input value output trace},
      typeTrace source endByte input value output trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected report trace},
      typeRejects source endByte input rejected report trace →
        ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TupleTypeTraceRejects typeTrace typeRejects source endByte input rejected report trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace :=
  TrailingDelimitedListTraceRejects.cascadeFilters successProtected rejectProtected rejection

theorem tupleTypeTraceExactOutcomeSpec
    (types : TraceExactOutcomeSpec typeTrace typeRejects source endByte) :
    TraceExactOutcomeSpec (TupleTypeTraceParses typeTrace)
      (TupleTypeTraceRejects typeTrace typeRejects) source endByte where
  successResultUnique := TupleTypeTraceParses.result_unique types.successResultUnique
  rejectResultUnique := TupleTypeTraceRejects.result_unique types.successResultUnique
    types.rejectResultUnique types.successRejectDisjoint
  successRejectDisjoint := TupleTypeTraceRejects.disjoint_success types.successResultUnique
    types.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTypeDispatchTraceGrammar
/-! One independent prioritized type layer over arbitrary nested trace
relations. Raw forms remain separate from selection; final rejection emits no
event and reports only the type-expression expectation. No existence is claimed. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive TypeDispatchFinalTraceRejects (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | rejected {input : Remainder} {report : ParseDiagnostic}
      (reported : RejectAtReports source endByte { head := .typeExpr, tail := [] } .typeExpr input report) :
      TypeDispatchFinalTraceRejects source endByte input input report []

def TypeDispatchRawTraceParses
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (branch : TypeDispatchBranch) :
    SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop :=
  match branch with
  | .function => FunctionTypeTraceParses elementTrace
  | .comptime => ComptimeTypeTraceParses elementTrace
  | .mapping => MappingTypeTraceParses elementTrace
  | .proxy => ProxyTypeTraceParses elementTrace
  | .tuple => TupleTypeTraceParses elementTrace
  | .named => NamedTypeTraceParses elementTrace
  | .final => fun _ _ _ _ _ _ => False

def TypeDispatchRawTraceRejects
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (branch : TypeDispatchBranch) :
    SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop :=
  match branch with
  | .function => FunctionTypeTraceRejects elementTrace elementRejects
  | .comptime => ComptimeTypeTraceRejects elementTrace elementRejects
  | .mapping => MappingTypeTraceRejects elementTrace elementRejects
  | .proxy => ProxyTypeTraceRejects elementRejects
  | .tuple => TupleTypeTraceRejects elementTrace elementRejects
  | .named => NamedTypeTraceRejects elementTrace elementRejects
  | .final => TypeDispatchFinalTraceRejects

inductive TypeDispatchTraceParses
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop where
  | selected {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
      (branch : TypeDispatchBranch)
      (selection : TypeDispatchSelects input branch)
      (parsed : TypeDispatchRawTraceParses elementTrace branch source endByte input value output trace) :
      TypeDispatchTraceParses elementTrace source endByte input value output trace

inductive TypeDispatchTraceRejects
    (elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop)
    (elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | selected {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
      (branch : TypeDispatchBranch)
      (selection : TypeDispatchSelects input branch)
      (rejection : TypeDispatchRawTraceRejects elementTrace elementRejects branch source endByte
        input rejected report trace) :
      TypeDispatchTraceRejects elementTrace elementRejects source endByte input rejected report trace

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTypeDispatchTraceOutcomeProperties
/-! Selection uniqueness lifts exact raw outcomes to the prioritized layer.
These laws establish uniqueness and disjointness only, not outcome existence. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem TypeDispatchFinalTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : TypeDispatchFinalTraceRejects source endByte input afterLeft leftReport leftTrace)
    (right : TypeDispatchFinalTraceRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | rejected report =>
      cases right with
      | rejected other => exact ⟨rfl, report.diagnostic_unique other, rfl⟩

theorem TypeDispatchTraceParses.raw_of_selected
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    {branch : TypeDispatchBranch} (selection : TypeDispatchSelects input branch)
    (parsed : TypeDispatchTraceParses elementTrace source endByte input value output trace) :
    TypeDispatchRawTraceParses elementTrace branch source endByte input value output trace := by
  cases parsed with
  | selected actual actualSelection raw =>
      cases selection.branch_unique actualSelection
      exact raw

theorem TypeDispatchTraceRejects.raw_of_selected
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    {branch : TypeDispatchBranch} (selection : TypeDispatchSelects input branch)
    (rejection : TypeDispatchTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    TypeDispatchRawTraceRejects elementTrace elementRejects branch source endByte input rejected report trace := by
  cases rejection with
  | selected actual actualSelection raw =>
      cases selection.branch_unique actualSelection
      exact raw

theorem TypeDispatchTraceParses.not_final
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (selection : TypeDispatchSelects input .final)
    (parsed : TypeDispatchTraceParses elementTrace source endByte input value output trace) : False :=
  parsed.raw_of_selected selection

theorem TypeDispatchTraceRejects.final_iff
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (selection : TypeDispatchSelects input .final) :
    TypeDispatchTraceRejects elementTrace elementRejects source endByte input rejected report trace ↔
      rejected = input ∧
      RejectAtReports source endByte { head := .typeExpr, tail := [] } .typeExpr input report ∧ trace = [] := by
  constructor
  · intro rejection
    have raw := rejection.raw_of_selected selection
    cases raw with
    | rejected reported => exact ⟨rfl, reported, rfl⟩
  · rintro ⟨rfl, reported, rfl⟩
    exact .selected .final selection (.rejected reported)

variable (rawExact : ∀ branch,
  TraceExactOutcomeSpec (TypeDispatchRawTraceParses elementTrace branch)
    (TypeDispatchRawTraceRejects elementTrace elementRejects branch) source endByte)

include rawExact

theorem TypeDispatchTraceParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.TypeExpr}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : TypeDispatchTraceParses elementTrace source endByte input left afterLeft leftTrace)
    (rightParsed : TypeDispatchTraceParses elementTrace source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace := by
  cases leftParsed with
  | selected branch selection raw =>
      exact (rawExact branch).successResultUnique raw (rightParsed.raw_of_selected selection)

theorem TypeDispatchTraceRejects.result_unique
    {input afterLeft afterRight : Remainder} {leftReport rightReport : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : TypeDispatchTraceRejects elementTrace elementRejects source endByte input afterLeft leftReport leftTrace)
    (right : TypeDispatchTraceRejects elementTrace elementRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace := by
  cases left with
  | selected branch selection raw =>
      exact (rawExact branch).rejectResultUnique raw (right.raw_of_selected selection)

theorem TypeDispatchTraceRejects.disjoint_success
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TypeDispatchTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, TypeDispatchTraceParses elementTrace source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  cases rejection with
  | selected branch selection raw =>
      exact (rawExact branch).successRejectDisjoint raw ⟨value, output, events, parsed.raw_of_selected selection⟩

theorem typeDispatchTraceExactOutcomeSpec_of_raw :
    TraceExactOutcomeSpec (TypeDispatchTraceParses elementTrace)
      (TypeDispatchTraceRejects elementTrace elementRejects) source endByte where
  successResultUnique := TypeDispatchTraceParses.result_unique rawExact
  rejectResultUnique := TypeDispatchTraceRejects.result_unique rawExact
  successRejectDisjoint := TypeDispatchTraceRejects.disjoint_success rawExact

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTypeDispatchTraceAgreementProperties
/-! Heterogeneous raw agreement lifts through the exact ordered selector.
The two child relations may differ and need not be internally functional.
Final rejection stays a silent, non-consuming independent terminal report. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {leftParses rightParses : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {leftRejects rightRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem typeDispatchTraceOutcomeAgreement_of_raw
    (raw : ∀ branch,
      TraceOutcomeAgreement (TypeDispatchRawTraceParses leftParses branch)
        (TypeDispatchRawTraceRejects leftParses leftRejects branch)
        (TypeDispatchRawTraceParses rightParses branch)
        (TypeDispatchRawTraceRejects rightParses rightRejects branch) source endByte) :
    TraceOutcomeAgreement (TypeDispatchTraceParses leftParses) (TypeDispatchTraceRejects leftParses leftRejects)
      (TypeDispatchTraceParses rightParses) (TypeDispatchTraceRejects rightParses rightRejects) source endByte where
  successResultAgree left right := by
    cases left with
    | selected branch selection parsed =>
        exact (raw branch).successResultAgree parsed (right.raw_of_selected selection)
  rejectResultAgree left right := by
    cases left with
    | selected branch selection rejection =>
        exact (raw branch).rejectResultAgree rejection (right.raw_of_selected selection)
  successRejectDisjoint left right := by
    cases left with
    | selected branch selection parsed =>
        exact (raw branch).successRejectDisjoint parsed (right.raw_of_selected selection)
  rejectSuccessDisjoint left right := by
    cases left with
    | selected branch selection rejection =>
        exact (raw branch).rejectSuccessDisjoint rejection (right.raw_of_selected selection)

theorem typeDispatchRawTraceOutcomeAgreement
    (children : TraceOutcomeAgreement leftParses leftRejects rightParses rightRejects source endByte)
    (branch : TypeDispatchBranch) :
    TraceOutcomeAgreement (TypeDispatchRawTraceParses leftParses branch)
      (TypeDispatchRawTraceRejects leftParses leftRejects branch)
      (TypeDispatchRawTraceParses rightParses branch)
      (TypeDispatchRawTraceRejects rightParses rightRejects branch) source endByte := by
  cases branch with
  | function => exact functionTypeTraceOutcomeAgreement children
  | comptime => exact comptimeTypeTraceOutcomeAgreement children
  | mapping => exact mappingTypeTraceOutcomeAgreement children
  | proxy => exact proxyTypeTraceOutcomeAgreement children
  | tuple => exact tupleTypeTraceOutcomeAgreement children
  | named => exact namedTypeTraceOutcomeAgreement children
  | final =>
      exact {
        successResultAgree := by intro _ _ _ _ _ _ _ impossible; exact False.elim impossible
        rejectResultAgree := TypeDispatchFinalTraceRejects.result_unique
        successRejectDisjoint := by intro _ _ _ _ _ _ _ impossible; exact False.elim impossible
        rejectSuccessDisjoint := by intro _ _ _ _ _ _ _ _ impossible; exact False.elim impossible
      }

theorem typeDispatchTraceOutcomeAgreement
    (children : TraceOutcomeAgreement leftParses leftRejects rightParses rightRejects source endByte) :
    TraceOutcomeAgreement (TypeDispatchTraceParses leftParses) (TypeDispatchTraceRejects leftParses leftRejects)
      (TypeDispatchTraceParses rightParses) (TypeDispatchTraceRejects rightParses rightRejects) source endByte :=
  typeDispatchTraceOutcomeAgreement_of_raw (typeDispatchRawTraceOutcomeAgreement children)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTypeDispatchTraceProperties
/-! Concrete raw-form exactness and protected-event laws lift to the selected
type layer. Child carrier preservation is separate from all exactness claims. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem typeDispatchRawTraceExactOutcomeSpec
    (children : TraceExactOutcomeSpec elementTrace elementRejects source endByte)
    (branch : TypeDispatchBranch) :
    TraceExactOutcomeSpec (TypeDispatchRawTraceParses elementTrace branch)
      (TypeDispatchRawTraceRejects elementTrace elementRejects branch) source endByte := by
  cases branch with
  | function => exact functionTypeTraceExactOutcomeSpec children
  | comptime => exact comptimeTypeTraceExactOutcomeSpec children
  | mapping => exact mappingTypeTraceExactOutcomeSpec children
  | proxy => exact proxyTypeTraceExactOutcomeSpec children
  | tuple => exact tupleTypeTraceExactOutcomeSpec children
  | named => exact namedTypeTraceExactOutcomeSpec children
  | final =>
      refine ⟨?_, TypeDispatchFinalTraceRejects.result_unique, ?_⟩
      · intro _ _ _ _ _ _ _ impossible; exact False.elim impossible
      · intro _ _ _ _ _ ⟨_, _, _, impossible⟩; exact impossible

theorem typeDispatchTraceExactOutcomeSpec
    (children : TraceExactOutcomeSpec elementTrace elementRejects source endByte) :
    TraceExactOutcomeSpec (TypeDispatchTraceParses elementTrace)
      (TypeDispatchTraceRejects elementTrace elementRejects) source endByte :=
  typeDispatchTraceExactOutcomeSpec_of_raw (typeDispatchRawTraceExactOutcomeSpec children)

theorem TypeDispatchTraceParses.output_window
    (childWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TypeDispatchTraceParses elementTrace source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | selected branch selection raw =>
      cases branch <;> simp only [TypeDispatchRawTraceParses] at raw
      case function => exact raw.output_window childWindow
      case comptime => exact raw.output_window childWindow
      case mapping => exact raw.output_window childWindow
      case proxy => exact raw.output_window childWindow
      case tuple => exact raw.output_window childWindow
      case named => exact raw.output_window childWindow

theorem TypeDispatchTraceParses.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (childProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TypeDispatchTraceParses elementTrace source endByte input value output trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases parsed with
  | selected branch selection raw =>
      cases branch <;> simp only [TypeDispatchRawTraceParses] at raw
      case function => exact raw.cascadeFilters childProtected
      case comptime => exact raw.cascadeFilters childProtected
      case mapping => exact raw.cascadeFilters childProtected
      case proxy => exact raw.cascadeFilters childProtected
      case tuple => exact raw.cascadeFilters childProtected
      case named => exact raw.cascadeFilters childProtected

theorem TypeDispatchTraceRejects.cascadeFilters
    {text : String} {lexical : List SourceSpan}
    (successProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TypeDispatchTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | selected branch selection raw =>
      cases branch <;> simp only [TypeDispatchRawTraceRejects] at raw
      case function => exact raw.cascadeFilters successProtected rejectProtected
      case comptime => exact raw.cascadeFilters successProtected rejectProtected
      case mapping => exact raw.cascadeFilters successProtected rejectProtected
      case proxy => exact raw.cascadeFilters rejectProtected
      case tuple => exact TupleTypeTraceRejects.cascadeFilters successProtected rejectProtected raw
      case named => exact raw.cascadeFilters successProtected rejectProtected
      case final => cases raw; exact .nil

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTypeDispatchTraceOrdinaryProperties
/-! Selected trace erasure recovers the older ordinary type layer. Positive
selection eliminates raw missing-prefix failures; named erasure receives the
comptime/mapping exclusions that are absent from the raw named grammar. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem TypeDispatchTraceParses.ordinary
    (childOrdinary : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (childWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TypeDispatchTraceParses elementTrace source endByte input value output trace) :
    TypeExprParses input value output := by
  cases parsed with
  | selected branch selection raw =>
      cases branch <;> simp only [TypeDispatchRawTraceParses] at raw
      case function => exact raw.ordinary childOrdinary childWindow
      case comptime => exact raw.ordinary childOrdinary
      case mapping =>
        rcases raw.ordinary_components childOrdinary with
          ⟨markerSpan, openingSpan, arrowSpan, closingSpan, afterMarker, afterOpening, afterKey,
            afterArrow, afterValue, key, value, marker, opening, keyParsed, arrow, valueParsed, closing, rfl⟩
        exact .mapping markerSpan openingSpan arrowSpan closingSpan marker opening arrow closing rfl keyParsed valueParsed
      case proxy => exact raw.ordinary childOrdinary
      case tuple => exact raw.ordinary childOrdinary childWindow
      case named =>
        cases selection with
        | named _ comptimeAbsent mappingAbsent _ _ _ =>
            rcases raw.ordinary_components childOrdinary childWindow with
              ⟨name, afterName, arguments, nameParsed, argumentsParsed, rfl⟩
            exact .named comptimeAbsent mappingAbsent nameParsed (by cases arguments <;> rfl) argumentsParsed

theorem TypeDispatchTraceRejects.ordinary
    {ordinaryRejects : Remainder → Remainder → Prop}
    (successErases : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      TypeExprParses input value output)
    (rejectErases : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ordinaryRejects input rejected)
    (childWindow : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TypeDispatchTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    TypeExprCoreRejects ordinaryRejects input rejected := by
  cases rejection with
  | selected branch selection raw =>
      cases selection with
      | function present =>
          rcases present with ⟨span, marker⟩
          exact .function (FunctionTypeTraceRejects.ordinary_of_marker_present
            successErases rejectErases childWindow (afterKeyword := { input with cursor := input.cursor + 1 })
            ⟨marker, rfl⟩ raw)
      | comptime functionAbsent present =>
          rcases present.exact_prefix with ⟨_, _, _, _, marker, opening⟩
          exact .comptime functionAbsent
            (ComptimeTypeTraceRejects.ordinary_of_prefix successErases rejectErases marker opening raw)
      | mapping functionAbsent comptimeAbsent present =>
          rcases present.exact_prefix with ⟨_, _, _, _, marker, opening⟩
          exact .mapping functionAbsent comptimeAbsent
            (MappingTypeTraceRejects.ordinary_of_prefix successErases rejectErases marker opening raw)
      | proxy functionAbsent comptimeAbsent mappingAbsent present =>
          exact .proxy functionAbsent comptimeAbsent mappingAbsent
            (ProxyTypeTraceRejects.ordinary_of_marker_present rejectErases present raw)
      | tuple functionAbsent comptimeAbsent mappingAbsent atAbsent present =>
          exact .tuple functionAbsent comptimeAbsent mappingAbsent atAbsent
            (TupleTypeTraceRejects.ordinary_of_opening_present successErases rejectErases present raw)
      | named functionAbsent comptimeAbsent mappingAbsent atAbsent leftParenAbsent present =>
          exact .named functionAbsent comptimeAbsent mappingAbsent atAbsent leftParenAbsent present
            (NamedTypeTraceRejects.ordinary successErases rejectErases raw)
      | final functionAbsent comptimeAbsent mappingAbsent atAbsent leftParenAbsent identifierAbsent =>
          cases raw
          exact .final functionAbsent comptimeAbsent mappingAbsent atAbsent leftParenAbsent identifierAbsent

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTypeExprTraceGrammar
/-! Fuel-free recursive type traces are the least simultaneous fixed point of
the independent selected layer. Success and rejection share one query domain;
the definition quantifies over closed relations, not executable parsers. It
asserts neither existence of an outcome nor an execution resource bound. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive TypeTraceQuery where
  | success (source : SourceId) (endByte : Nat) (input : Remainder)
      (value : Syntax.TypeExpr) (output : Remainder) (trace : List ParseDiagnostic)
  | rejection (source : SourceId) (endByte : Nat) (input rejected : Remainder)
      (report : ParseDiagnostic) (trace : List ParseDiagnostic)

def TypeTraceLayer (candidate : TypeTraceQuery → Prop) : TypeTraceQuery → Prop
  | .success source endByte input value output trace =>
      TypeDispatchTraceParses (fun source endByte input value output trace =>
        candidate (.success source endByte input value output trace))
        source endByte input value output trace
  | .rejection source endByte input rejected report trace =>
      TypeDispatchTraceRejects (fun source endByte input value output trace =>
        candidate (.success source endByte input value output trace))
        (fun source endByte input rejected report trace =>
          candidate (.rejection source endByte input rejected report trace))
        source endByte input rejected report trace

def TypeTraceLeast (query : TypeTraceQuery) : Prop :=
  ∀ candidate : TypeTraceQuery → Prop,
    (∀ query, TypeTraceLayer candidate query → candidate query) → candidate query

def TypeExprTraceParses (source : SourceId) (endByte : Nat) (input : Remainder)
    (value : Syntax.TypeExpr) (output : Remainder) (trace : List ParseDiagnostic) : Prop :=
  TypeTraceLeast (.success source endByte input value output trace)

def TypeExprTraceRejects (source : SourceId) (endByte : Nat) (input rejected : Remainder)
    (report : ParseDiagnostic) (trace : List ParseDiagnostic) : Prop :=
  TypeTraceLeast (.rejection source endByte input rejected report trace)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTypeFormTraceMonotonicityProperties
/-! Raw type forms preserve all source-shaped data and events when their child
success relation is enlarged at the same source and end byte. Qualified names,
finishing events, optional guards, and delimiter policies are unchanged. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace otherTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
    Remainder → List ParseDiagnostic → Prop} {source : SourceId} {endByte : Nat}
  (childMap : ∀ {input value output trace},
    elementTrace source endByte input value output trace → otherTrace source endByte input value output trace)

include childMap

theorem NamedTypeArgumentsTraceParses.mono
    {input output : Remainder} {values : Option (NonemptyDelimitedList Syntax.TypeExpr)}
    {trace : List ParseDiagnostic}
    (parsed : NamedTypeArgumentsTraceParses elementTrace source endByte input values output trace) :
    NamedTypeArgumentsTraceParses otherTrace source endByte input values output trace := by
  cases parsed with
  | absent absent => exact .absent absent
  | present values => exact .present (values.mono childMap)

theorem NamedTypeTraceParses.mono
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : NamedTypeTraceParses elementTrace source endByte input value output trace) :
    NamedTypeTraceParses otherTrace source endByte input value output trace := by
  cases parsed with
  | parsed name arguments finished => exact .parsed name (arguments.mono childMap) finished

theorem MappingTypeTraceParses.mono
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : MappingTypeTraceParses elementTrace source endByte input value output trace) :
    MappingTypeTraceParses otherTrace source endByte input value output trace := by
  cases parsed with
  | parsed markerSpan openingSpan arrowSpan closingSpan marker opening key arrow value closing =>
      exact .parsed markerSpan openingSpan arrowSpan closingSpan marker opening
        (childMap key) arrow (childMap value) closing

theorem ProxyTypeTraceParses.mono
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ProxyTypeTraceParses elementTrace source endByte input value output trace) :
    ProxyTypeTraceParses otherTrace source endByte input value output trace := by
  cases parsed with
  | parsed span marker inner => exact .parsed span marker (childMap inner)

theorem TupleTypeTraceParses.mono
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TupleTypeTraceParses elementTrace source endByte input value output trace) :
    TupleTypeTraceParses otherTrace source endByte input value output trace := by
  cases parsed with
  | parsed values => exact .parsed (values.mono childMap)

theorem ComptimeTypeTraceParses.mono
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ComptimeTypeTraceParses elementTrace source endByte input value output trace) :
    ComptimeTypeTraceParses otherTrace source endByte input value output trace := by
  cases parsed with
  | parsed markerSpan openingSpan closingSpan marker opening inner closing =>
      exact .parsed markerSpan openingSpan closingSpan marker opening (childMap inner) closing

theorem FunctionReturnsTraceParses.mono
    {input output : Remainder} {values : Option (DelimitedList Syntax.TypeExpr)}
    {trace : List ParseDiagnostic}
    (parsed : FunctionReturnsTraceParses elementTrace source endByte input values output trace) :
    FunctionReturnsTraceParses otherTrace source endByte input values output trace := by
  cases parsed with
  | absent absent => exact .absent absent
  | present span marker values => exact .present span marker (values.mono childMap)

theorem FunctionTypeTraceParses.mono
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : FunctionTypeTraceParses elementTrace source endByte input value output trace) :
    FunctionTypeTraceParses otherTrace source endByte input value output trace := by
  cases parsed with
  | parsed span marker parameters returns =>
      exact .parsed span marker (parameters.mono childMap) (returns.mono childMap)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTypeFormRejectionTraceMonotonicityProperties
/-! Enlarging child relations preserves raw type rejection at the same source
and end byte. The full report, remainder, and ordered successful/rejected child
events are identical; no terminal report is inserted into those events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace otherTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
    Remainder → List ParseDiagnostic → Prop}
  {elementRejects otherRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop} {source : SourceId} {endByte : Nat}
  (successMap : ∀ {input value output trace},
    elementTrace source endByte input value output trace → otherTrace source endByte input value output trace)
  (rejectMap : ∀ {input rejected report trace},
    elementRejects source endByte input rejected report trace → otherRejects source endByte input rejected report trace)

include successMap rejectMap in
theorem NamedTypeArgumentsTraceRejects.mono
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedTypeArgumentsTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    NamedTypeArgumentsTraceRejects otherTrace otherRejects source endByte input rejected report trace := by
  cases rejection with
  | present span opening values => exact .present span opening (values.mono successMap rejectMap)

include successMap rejectMap in
theorem NamedTypeTraceRejects.mono
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    NamedTypeTraceRejects otherTrace otherRejects source endByte input rejected report trace := by
  cases rejection with
  | nameRejected name => exact .nameRejected name
  | argumentsRejected name arguments => exact .argumentsRejected name (arguments.mono successMap rejectMap)

include successMap rejectMap in
theorem MappingTypeTraceRejects.mono
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : MappingTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    MappingTypeTraceRejects otherTrace otherRejects source endByte input rejected report trace := by
  cases rejection with
  | markerMissing absent reported => exact .markerMissing absent reported
  | openingMissing span marker absent reported => exact .openingMissing span marker absent reported
  | keyRejected markerSpan openingSpan marker opening key =>
      exact .keyRejected markerSpan openingSpan marker opening (rejectMap key)
  | arrowMissing markerSpan openingSpan marker opening key absent reported =>
      exact .arrowMissing markerSpan openingSpan marker opening (successMap key) absent reported
  | valueRejected markerSpan openingSpan arrowSpan marker opening key arrow value =>
      exact .valueRejected markerSpan openingSpan arrowSpan marker opening (successMap key) arrow (rejectMap value)
  | closingMissing markerSpan openingSpan arrowSpan marker opening key arrow value absent reported =>
      exact .closingMissing markerSpan openingSpan arrowSpan marker opening (successMap key) arrow
        (successMap value) absent reported

include rejectMap in
theorem ProxyTypeTraceRejects.mono
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ProxyTypeTraceRejects elementRejects source endByte input rejected report trace) :
    ProxyTypeTraceRejects otherRejects source endByte input rejected report trace := by
  cases rejection with
  | markerMissing absent reported => exact .markerMissing absent reported
  | innerRejected span marker inner => exact .innerRejected span marker (rejectMap inner)

include successMap rejectMap in
theorem TupleTypeTraceRejects.mono
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TupleTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    TupleTypeTraceRejects otherTrace otherRejects source endByte input rejected report trace :=
  TrailingDelimitedListTraceRejects.mono successMap rejectMap rejection

include successMap rejectMap in
theorem ComptimeTypeTraceRejects.mono
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ComptimeTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ComptimeTypeTraceRejects otherTrace otherRejects source endByte input rejected report trace := by
  cases rejection with
  | markerMissing absent reported => exact .markerMissing absent reported
  | openingMissing span marker absent reported => exact .openingMissing span marker absent reported
  | innerRejected markerSpan openingSpan marker opening inner =>
      exact .innerRejected markerSpan openingSpan marker opening (rejectMap inner)
  | closingMissing markerSpan openingSpan marker opening inner absent reported =>
      exact .closingMissing markerSpan openingSpan marker opening (successMap inner) absent reported

include successMap rejectMap in
theorem FunctionReturnsTraceRejects.mono
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : FunctionReturnsTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    FunctionReturnsTraceRejects otherTrace otherRejects source endByte input rejected report trace := by
  cases rejection with
  | present span marker values => exact .present span marker (values.mono successMap rejectMap)

include successMap rejectMap in
theorem FunctionTypeTraceRejects.mono
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : FunctionTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    FunctionTypeTraceRejects otherTrace otherRejects source endByte input rejected report trace := by
  cases rejection with
  | markerMissing absent reported => exact .markerMissing absent reported
  | parametersRejected span marker values => exact .parametersRejected span marker (values.mono successMap rejectMap)
  | returnsRejected span marker parameters returns =>
      exact .returnsRejected span marker (parameters.mono successMap) (returns.mono successMap rejectMap)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTypeDispatchTraceMonotonicityProperties
/-! One selected type layer is monotone in its nested relations at fixed source
coordinates. The selected branch and every negative/positive guard stay fixed;
the final rejection has no child relation to replace. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace otherTrace : SourceId → Nat → Remainder → Syntax.TypeExpr →
    Remainder → List ParseDiagnostic → Prop}
  {elementRejects otherRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop} {source : SourceId} {endByte : Nat}

theorem TypeDispatchRawTraceParses.mono
    (childMap : ∀ {input value output trace},
      elementTrace source endByte input value output trace → otherTrace source endByte input value output trace)
    {branch : TypeDispatchBranch} {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TypeDispatchRawTraceParses elementTrace branch source endByte input value output trace) :
    TypeDispatchRawTraceParses otherTrace branch source endByte input value output trace := by
  cases branch with
  | function => exact FunctionTypeTraceParses.mono childMap parsed
  | comptime => exact ComptimeTypeTraceParses.mono childMap parsed
  | mapping => exact MappingTypeTraceParses.mono childMap parsed
  | proxy => exact ProxyTypeTraceParses.mono childMap parsed
  | tuple => exact TupleTypeTraceParses.mono childMap parsed
  | named => exact NamedTypeTraceParses.mono childMap parsed
  | final => exact parsed

theorem TypeDispatchTraceParses.mono
    (childMap : ∀ {input value output trace},
      elementTrace source endByte input value output trace → otherTrace source endByte input value output trace)
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TypeDispatchTraceParses elementTrace source endByte input value output trace) :
    TypeDispatchTraceParses otherTrace source endByte input value output trace := by
  cases parsed with
  | selected branch selection raw => exact .selected branch selection (TypeDispatchRawTraceParses.mono childMap raw)

theorem TypeDispatchRawTraceRejects.mono
    (successMap : ∀ {input value output trace},
      elementTrace source endByte input value output trace → otherTrace source endByte input value output trace)
    (rejectMap : ∀ {input rejected report trace},
      elementRejects source endByte input rejected report trace → otherRejects source endByte input rejected report trace)
    {branch : TypeDispatchBranch} {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TypeDispatchRawTraceRejects elementTrace elementRejects branch source endByte input rejected report trace) :
    TypeDispatchRawTraceRejects otherTrace otherRejects branch source endByte input rejected report trace := by
  cases branch with
  | function => exact FunctionTypeTraceRejects.mono successMap rejectMap rejection
  | comptime => exact ComptimeTypeTraceRejects.mono successMap rejectMap rejection
  | mapping => exact MappingTypeTraceRejects.mono successMap rejectMap rejection
  | proxy => exact ProxyTypeTraceRejects.mono rejectMap rejection
  | tuple => exact TupleTypeTraceRejects.mono successMap rejectMap rejection
  | named => exact NamedTypeTraceRejects.mono successMap rejectMap rejection
  | final => exact rejection

theorem TypeDispatchTraceRejects.mono
    (successMap : ∀ {input value output trace},
      elementTrace source endByte input value output trace → otherTrace source endByte input value output trace)
    (rejectMap : ∀ {input rejected report trace},
      elementRejects source endByte input rejected report trace → otherRejects source endByte input rejected report trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TypeDispatchTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    TypeDispatchTraceRejects otherTrace otherRejects source endByte input rejected report trace := by
  cases rejection with
  | selected branch selection raw =>
      exact .selected branch selection (TypeDispatchRawTraceRejects.mono successMap rejectMap raw)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTypeExprTraceInductionProperties
/-! The fixed type layer is monotone and its least relation supports exact
rolling/unrolling and simultaneous induction. Strong induction retains each
child's original derivation alongside the chosen induction property. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem TypeTraceLayer.mono {left right : TypeTraceQuery → Prop}
    (childMap : ∀ query, left query → right query) (query : TypeTraceQuery)
    (step : TypeTraceLayer left query) : TypeTraceLayer right query := by
  cases query with
  | success source endByte input value output trace =>
      exact TypeDispatchTraceParses.mono
        (fun {input value output trace} parsed =>
          childMap (.success source endByte input value output trace) parsed) step
  | rejection source endByte input rejected report trace =>
      exact TypeDispatchTraceRejects.mono
        (fun {input value output trace} parsed =>
          childMap (.success source endByte input value output trace) parsed)
        (fun {input rejected report trace} rejectedChild =>
          childMap (.rejection source endByte input rejected report trace) rejectedChild) step

theorem TypeTraceLeast.induction
    {candidate : TypeTraceQuery → Prop}
    (closed : ∀ query, TypeTraceLayer candidate query → candidate query)
    {query : TypeTraceQuery} (derivation : TypeTraceLeast query) : candidate query :=
  derivation candidate closed

theorem TypeTraceLeast.roll {query : TypeTraceQuery}
    (step : TypeTraceLayer TypeTraceLeast query) : TypeTraceLeast query := by
  intro candidate closed
  exact closed query (TypeTraceLayer.mono (fun _ derivation => derivation candidate closed) query step)

theorem TypeTraceLeast.unroll {query : TypeTraceQuery}
    (derivation : TypeTraceLeast query) : TypeTraceLayer TypeTraceLeast query := by
  apply derivation (TypeTraceLayer TypeTraceLeast)
  intro next step
  exact TypeTraceLayer.mono (fun _ nested => TypeTraceLeast.roll nested) next step

theorem TypeTraceLeast.strong_induction
    {candidate : TypeTraceQuery → Prop}
    (closed : ∀ query, TypeTraceLayer (fun query => TypeTraceLeast query ∧ candidate query) query → candidate query)
    {query : TypeTraceQuery} (derivation : TypeTraceLeast query) : candidate query := by
  have both : TypeTraceLeast query ∧ candidate query := derivation
    (fun query => TypeTraceLeast query ∧ candidate query) (by
    intro next step
    exact ⟨TypeTraceLeast.roll (TypeTraceLayer.mono (fun _ pair => pair.1) next step), closed next step⟩)
  exact both.2

theorem TypeExprTraceParses.unroll_iff {source : SourceId} {endByte : Nat}
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic} :
    TypeExprTraceParses source endByte input value output trace ↔
      TypeDispatchTraceParses TypeExprTraceParses source endByte input value output trace := by
  change TypeTraceLeast (.success source endByte input value output trace) ↔
    TypeTraceLayer TypeTraceLeast (.success source endByte input value output trace)
  exact ⟨TypeTraceLeast.unroll, TypeTraceLeast.roll⟩

theorem TypeExprTraceRejects.unroll_iff {source : SourceId} {endByte : Nat}
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    TypeExprTraceRejects source endByte input rejected report trace ↔
      TypeDispatchTraceRejects TypeExprTraceParses TypeExprTraceRejects
        source endByte input rejected report trace := by
  change TypeTraceLeast (.rejection source endByte input rejected report trace) ↔
    TypeTraceLayer TypeTraceLeast (.rejection source endByte input rejected report trace)
  exact ⟨TypeTraceLeast.unroll, TypeTraceLeast.roll⟩

theorem TypeExprTraceParses.roll {source : SourceId} {endByte : Nat}
    {input output : Remainder} {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (step : TypeDispatchTraceParses TypeExprTraceParses source endByte input value output trace) :
    TypeExprTraceParses source endByte input value output trace :=
  TypeExprTraceParses.unroll_iff.mpr step

theorem TypeExprTraceRejects.roll {source : SourceId} {endByte : Nat}
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (step : TypeDispatchTraceRejects TypeExprTraceParses TypeExprTraceRejects
      source endByte input rejected report trace) :
    TypeExprTraceRejects source endByte input rejected report trace :=
  TypeExprTraceRejects.unroll_iff.mpr step

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTypeExprTraceOutcomeProperties
/-! Recursive trace exactness follows by simultaneous strong induction on the
left derivation. Left children carry the least derivation and its induction
property; right children are arbitrary least derivations. Only the right root
is unrolled. No uniform recursive uniqueness or outcome existence is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private def agreesWithLeast : TypeTraceQuery → Prop
  | .success source endByte input value output trace =>
      (∀ {other after events}, TypeExprTraceParses source endByte input other after events →
        value = other ∧ output = after ∧ trace = events) ∧
      (∀ {rejected report events}, TypeExprTraceRejects source endByte input rejected report events → False)
  | .rejection source endByte input rejected report trace =>
      (∀ {after diagnostic events}, TypeExprTraceRejects source endByte input after diagnostic events →
        rejected = after ∧ report = diagnostic ∧ trace = events) ∧
      (∀ {value output events}, TypeExprTraceParses source endByte input value output events → False)

private def knownSuccess (source : SourceId) (endByte : Nat) (input : Remainder)
    (value : Syntax.TypeExpr) (output : Remainder) (trace : List ParseDiagnostic) : Prop :=
  TypeExprTraceParses source endByte input value output trace ∧
    agreesWithLeast (.success source endByte input value output trace)

private def knownRejection (source : SourceId) (endByte : Nat) (input rejected : Remainder)
    (report : ParseDiagnostic) (trace : List ParseDiagnostic) : Prop :=
  TypeExprTraceRejects source endByte input rejected report trace ∧
    agreesWithLeast (.rejection source endByte input rejected report trace)

private theorem knownChildren_agree (source : SourceId) (endByte : Nat) :
    TraceOutcomeAgreement knownSuccess knownRejection TypeExprTraceParses TypeExprTraceRejects source endByte where
  successResultAgree left right := left.2.1 right
  rejectResultAgree left right := left.2.1 right
  successRejectDisjoint left right := left.2.2 right
  rejectSuccessDisjoint left right := left.2.2 right

private theorem agreesWithLeast_closed (query : TypeTraceQuery)
    (step : TypeTraceLayer (fun query => TypeTraceLeast query ∧ agreesWithLeast query) query) :
    agreesWithLeast query := by
  cases query with
  | success source endByte input value output trace =>
      have agreement := typeDispatchTraceOutcomeAgreement (knownChildren_agree source endByte)
      constructor
      · intro other after events right
        exact agreement.successResultAgree step (TypeExprTraceParses.unroll_iff.mp right)
      · intro rejected report events right
        exact agreement.successRejectDisjoint step (TypeExprTraceRejects.unroll_iff.mp right)
  | rejection source endByte input rejected report trace =>
      have agreement := typeDispatchTraceOutcomeAgreement (knownChildren_agree source endByte)
      constructor
      · intro after diagnostic events right
        exact agreement.rejectResultAgree step (TypeExprTraceRejects.unroll_iff.mp right)
      · intro value output events right
        exact agreement.rejectSuccessDisjoint step (TypeExprTraceParses.unroll_iff.mp right)

theorem TypeExprTraceParses.result_unique
    {source : SourceId} {endByte : Nat} {input afterLeft afterRight : Remainder}
    {left right : Syntax.TypeExpr} {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : TypeExprTraceParses source endByte input left afterLeft leftTrace)
    (rightParsed : TypeExprTraceParses source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace :=
  (TypeTraceLeast.strong_induction agreesWithLeast_closed leftParsed).1 rightParsed

theorem TypeExprTraceRejects.result_unique
    {source : SourceId} {endByte : Nat} {input afterLeft afterRight : Remainder}
    {leftReport rightReport : ParseDiagnostic} {leftTrace rightTrace : List ParseDiagnostic}
    (leftRejected : TypeExprTraceRejects source endByte input afterLeft leftReport leftTrace)
    (rightRejected : TypeExprTraceRejects source endByte input afterRight rightReport rightTrace) :
    afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace :=
  (TypeTraceLeast.strong_induction agreesWithLeast_closed leftRejected).1 rightRejected

theorem TypeExprTraceParses.disjoint_rejection
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TypeExprTraceParses source endByte input value output trace) :
    ¬ ∃ rejected report events, TypeExprTraceRejects source endByte input rejected report events := by
  rintro ⟨rejected, report, events, rejection⟩
  exact (TypeTraceLeast.strong_induction agreesWithLeast_closed parsed).2 rejection

theorem TypeExprTraceRejects.disjoint_success
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TypeExprTraceRejects source endByte input rejected report trace) :
    ¬ ∃ value output events, TypeExprTraceParses source endByte input value output events := by
  rintro ⟨value, output, events, parsed⟩
  exact (TypeTraceLeast.strong_induction agreesWithLeast_closed rejection).2 parsed

theorem typeExprTraceExactOutcomeSpec {source : SourceId} {endByte : Nat} :
    TraceExactOutcomeSpec TypeExprTraceParses TypeExprTraceRejects source endByte where
  successResultUnique := TypeExprTraceParses.result_unique
  rejectResultUnique := TypeExprTraceRejects.result_unique
  successRejectDisjoint := TypeExprTraceRejects.disjoint_success

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeTypeExprTraceStructuralProperties
/-! Fuel-free recursive trace structure: successful ordinary erasure preserves
the complete token carrier and active end index; both outcomes retain protected
events. These laws do not assert execution, completeness, or outcome existence. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private def successStructure : TypeTraceQuery → Prop
  | .success _ _ input value output _ =>
      TypeExprParses input value output ∧
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex
  | .rejection _ _ _ _ _ _ => True

private theorem successStructure_closed (query : TypeTraceQuery)
    (step : TypeTraceLayer successStructure query) : successStructure query := by
  cases query with
  | success source endByte input value output trace =>
      exact ⟨TypeDispatchTraceParses.ordinary (fun child => child.1)
        (fun child => child.2) step,
        TypeDispatchTraceParses.output_window (fun child => child.2) step⟩
  | rejection => trivial

theorem TypeExprTraceParses.ordinary
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TypeExprTraceParses source endByte input value output trace) :
    TypeExprParses input value output :=
  (TypeTraceLeast.induction successStructure_closed parsed).1

theorem TypeExprTraceParses.output_window
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TypeExprTraceParses source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex :=
  (TypeTraceLeast.induction successStructure_closed parsed).2

private def protectedEvents (text : String) (lexical : List SourceSpan) : TypeTraceQuery → Prop
  | .success _ _ _ _ _ trace => ParseDiagnosticCascadeFilters text lexical trace trace
  | .rejection _ _ _ _ _ trace => ParseDiagnosticCascadeFilters text lexical trace trace

private theorem protectedEvents_closed (text : String) (lexical : List SourceSpan)
    (query : TypeTraceQuery) (step : TypeTraceLayer (protectedEvents text lexical) query) :
    protectedEvents text lexical query := by
  cases query with
  | success => exact TypeDispatchTraceParses.cascadeFilters (fun child => child) step
  | rejection => exact TypeDispatchTraceRejects.cascadeFilters (fun child => child) (fun child => child) step

theorem TypeExprTraceParses.cascadeFilters
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {value : Syntax.TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TypeExprTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace :=
  TypeTraceLeast.induction (protectedEvents_closed text lexical) parsed

theorem TypeExprTraceRejects.cascadeFilters
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TypeExprTraceRejects source endByte input rejected report trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace :=
  TypeTraceLeast.induction (protectedEvents_closed text lexical) rejection

end Solcore.Syntax.DeclarativeGrammar
end
