import Solcore.Syntax.DeclarativeNamedTypeArgumentsTraceProperties
import Solcore.Syntax.Parser.DelimitedTrailingTraceContextProperties
import Solcore.Syntax.Parser.Type

/-! The optional angle marker and nonempty-carrier conversion are silent.
Their exact state behavior does not require any recursive child contract. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem requireNonempty_success_iff_toList {α : Type} (phase : ParserPhase)
    {values : DelimitedList α} {arguments : NonemptyDelimitedList α} {input output : State} :
    requireNonempty values phase input = .ok arguments output ↔
      values = { span := arguments.span, elements := arguments.elements.toList } ∧ output = input := by
  constructor
  · intro result
    unfold requireNonempty at result
    cases elements : values.elements with
    | nil => rw [elements] at result; contradiction
    | cons head tail =>
        rw [elements] at result
        cases result
        refine ⟨?_, rfl⟩
        cases values
        simp_all only [NonemptyList.toList]
  · rintro ⟨rfl, rfl⟩
    cases arguments with
    | mk span elements => cases elements; rfl

theorem requireNonempty_eq_ok_of_toList {α : Type} (phase : ParserPhase)
    (arguments : NonemptyDelimitedList α) (input : State) :
    requireNonempty { span := arguments.span, elements := arguments.elements.toList } phase input =
      .ok arguments input :=
  (requireNonempty_success_iff_toList phase).mpr ⟨rfl, rfl⟩

/-- The independent false-empty-policy structure rules out the defensive
nonempty-conversion invariant, with no validity or diagnostic assumptions. -/
theorem requireNonempty_ne_invariant_of_trace {α : Type}
    {opening closing : Symbol}
    {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → α →
      DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat} {before after : DeclarativeGrammar.Remainder}
    {values : DelimitedList α} {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.TrailingDelimitedListTraceParses opening closing false elementTrace
      source endByte before values after trace) (phase : ParserPhase) (input : State)
    (error : ParserInvariantError) : requireNonempty values phase input ≠ .invariant error := by
  have nonempty := parsed.nonempty_elements
  unfold requireNonempty
  cases elements : values.elements with
  | nil => exact False.elim (nonempty elements)
  | cons head tail => intro failed; cases failed

theorem parseNamedTypeArguments_eq_none_of_absent (nested : Parser TypeExpr)
    {input : State}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.symbol .less)) :
    parseNamedTypeArguments nested input = .ok none input := by
  simp only [parseNamedTypeArguments, getState, bind,
    DelimitedTraceInternals.symbol_absent .less absent, Bool.false_eq_true, if_false, pure]

theorem parseNamedTypeArguments_eq_of_present (nested : Parser TypeExpr)
    {input : State} {span : SourceSpan}
    (opening : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .symbol .less }) :
    parseNamedTypeArguments nested input =
      match delimited .less .greater false nested .typeExpr .typeExpr input with
      | .ok values next =>
          match requireNonempty values .typeExpr next with
          | .ok arguments output => .ok (some arguments) output
          | .reject failure rejected => .reject failure rejected
          | .invariant error => .invariant error
      | .reject failure rejected => .reject failure rejected
      | .invariant error => .invariant error := by
  have present := DelimitedTraceInternals.symbol_present .less
    (input := input) (after := { input.declarativeRemainder with cursor := input.cursor + 1 }) ⟨opening, rfl⟩
  simp only [parseNamedTypeArguments, getState, bind, present, if_true, pure]
  cases delimited .less .greater false nested .typeExpr .typeExpr input with
  | reject => rfl
  | invariant => rfl
  | ok values next =>
      simp only
      cases requireNonempty values .typeExpr next <;> rfl

end Solcore.Syntax.Parser
