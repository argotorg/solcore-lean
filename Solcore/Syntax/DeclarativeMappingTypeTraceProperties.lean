import Solcore.Syntax.DeclarativeMappingTypeTraceGrammar
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties
import Solcore.Syntax.DeclarativeParseDiagnosticCascadeProperties

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
