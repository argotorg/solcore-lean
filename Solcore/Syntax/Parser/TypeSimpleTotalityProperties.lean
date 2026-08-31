import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.PrimitiveTotalityProperties
import Solcore.Syntax.Parser.Type

/-! Conditional totality for non-function recursive type forms. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem element_invariantFreeOnValid
    {α : Type} {element : Parser α}
    (contract : ElementTotalityContract element) :
    Parser.InvariantFreeOnValid element :=
  Parser.invariantFreeOnValid_of_ne_invariant contract.invariantFree

/-- Mapping types add no invariant beyond their recursive type parser. -/
theorem parseMappingType_invariantFreeOnValid (nested : Parser TypeExpr)
    (contract : ElementTotalityContract nested) :
    Parser.InvariantFreeOnValid (parseMappingType nested) := by
  unfold parseMappingType
  apply Parser.bind_invariantFreeOnValid
    (contextual_validFor .mapping .typeExpr)
    (contextual_ordinary .mapping .typeExpr).invariantFreeOnValid
  intro mapping
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .leftParen .typeExpr)
    (symbol_ordinary .leftParen .typeExpr).invariantFreeOnValid
  intro opening
  apply Parser.bind_invariantFreeOnValid contract.validFor
    (element_invariantFreeOnValid contract)
  intro key
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .fatArrow .typeExpr)
    (symbol_ordinary .fatArrow .typeExpr).invariantFreeOnValid
  intro arrow
  apply Parser.bind_invariantFreeOnValid contract.validFor
    (element_invariantFreeOnValid contract)
  intro value
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .rightParen .typeExpr)
    (symbol_ordinary .rightParen .typeExpr).invariantFreeOnValid
  intro closing
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover mapping.span closing.span
    value := .mapping mapping.span
      (SourceSpan.cover opening.span closing.span) key value
  } : TypeExpr)

theorem parseMappingType_ne_invariant (nested : Parser TypeExpr)
    (contract : ElementTotalityContract nested)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parseMappingType nested input ≠ .invariant error :=
  (parseMappingType_invariantFreeOnValid nested contract).ne_invariant
    input inputValid error

/-- Comptime types add no invariant beyond their recursive type parser. -/
theorem parseComptimeType_invariantFreeOnValid (nested : Parser TypeExpr)
    (contract : ElementTotalityContract nested) :
    Parser.InvariantFreeOnValid (parseComptimeType nested) := by
  unfold parseComptimeType
  apply Parser.bind_invariantFreeOnValid
    (contextual_validFor .comptime .typeExpr)
    (contextual_ordinary .comptime .typeExpr).invariantFreeOnValid
  intro comptime
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .less .typeExpr)
    (symbol_ordinary .less .typeExpr).invariantFreeOnValid
  intro opening
  apply Parser.bind_invariantFreeOnValid contract.validFor
    (element_invariantFreeOnValid contract)
  intro inner
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .greater .typeExpr)
    (symbol_ordinary .greater .typeExpr).invariantFreeOnValid
  intro closing
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover comptime.span closing.span
    value := .comptime comptime.span
      (SourceSpan.cover opening.span closing.span) inner
  } : TypeExpr)

theorem parseComptimeType_ne_invariant (nested : Parser TypeExpr)
    (contract : ElementTotalityContract nested)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parseComptimeType nested input ≠ .invariant error :=
  (parseComptimeType_invariantFreeOnValid nested contract).ne_invariant
    input inputValid error

/-- Proxy types add no invariant beyond their recursive type parser. -/
theorem parseProxyType_invariantFreeOnValid (nested : Parser TypeExpr)
    (contract : ElementTotalityContract nested) :
    Parser.InvariantFreeOnValid (parseProxyType nested) := by
  intro input inputValid
  unfold parseProxyType
  rcases (symbol_ordinary .at .typeExpr) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerValid := symbol_validFor .at .typeExpr input inputValid
    rw [markerResult] at markerValid
    rcases element_invariantFreeOnValid contract afterMarker markerValid.2.1 with
      ⟨inner, next, innerResult⟩ | ⟨failure, rejected, innerResult⟩
    · exact Or.inl ⟨{
          span := SourceSpan.cover marker.span inner.span
          value := .proxy marker.span inner
        }, next, by simp only [markerResult, innerResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [markerResult, innerResult]⟩
  · exact Or.inr ⟨failure, rejected, by simp only [markerResult]⟩

theorem parseProxyType_ne_invariant (nested : Parser TypeExpr)
    (contract : ElementTotalityContract nested)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parseProxyType nested input ≠ .invariant error :=
  (parseProxyType_invariantFreeOnValid nested contract).ne_invariant
    input inputValid error

/-- Tuple types add no invariant beyond their recursive element parser. -/
theorem parseTupleType_invariantFreeOnValid (nested : Parser TypeExpr)
    (contract : ElementTotalityContract nested) :
    Parser.InvariantFreeOnValid (parseTupleType nested) := by
  intro input inputValid
  rcases delimited_ordinary .leftParen .rightParen true nested
      .typeExpr .typeExpr contract input inputValid with
    ⟨tuple, next, tupleResult⟩ | ⟨failure, rejected, tupleResult⟩
  · exact Or.inl ⟨{
        span := tuple.span
        value := .tuple tuple.elements
      }, next, by unfold parseTupleType; simp only [tupleResult, bind, pure]⟩
  · exact Or.inr ⟨failure, rejected, by
      unfold parseTupleType
      simp only [tupleResult, bind]⟩

theorem parseTupleType_ne_invariant (nested : Parser TypeExpr)
    (contract : ElementTotalityContract nested)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parseTupleType nested input ≠ .invariant error :=
  (parseTupleType_invariantFreeOnValid nested contract).ne_invariant
    input inputValid error

end Solcore.Syntax.Parser
