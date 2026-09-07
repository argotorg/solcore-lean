import Solcore.Syntax.DeclarativeCoreLambdaGrammar
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.Parameter

/-! Shared exact lookahead for non-recovering function and lambda parameters.
The contextual marker is selected only when the next identifier is visible in
the active window. These proof-side projections do not execute either branch
and do not alter the parser, state, or diagnostic history. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

namespace ParameterDispatchTraceInternals

def comptimeGuard (input : State) : Bool :=
  isContextual input .comptime &&
    match input.peekOffsetKind? 1 with
    | some (.identifier _) => true
    | _ => false

theorem comptimeGuard_true_iff {input : State} :
    comptimeGuard input = true ↔ ComptimeLambdaParameterStartsAt input.declarativeRemainder := by
  constructor
  · intro guard
    rcases Bool.and_eq_true_iff.mp guard with ⟨markerPresent, namePresent⟩
    rcases contextual_eq_ok_of_isContextual_eq_true .comptime .parameter markerPresent with
      ⟨marker, markerResult⟩
    have advanced : isIdentifier { input with cursor := input.cursor + 1 } = true := namePresent
    rcases identifierPresentAt_of_isIdentifier_eq_true advanced with ⟨nameSpan, spelling, nameToken⟩
    exact ⟨marker.span, nameSpan, spelling,
      (contextual_success_exactTokenParses .comptime .parameter markerResult).1, nameToken⟩
  · rintro ⟨markerSpan, nameSpan, spelling, markerToken, nameToken⟩
    change TokenAt input.tokens input.window.endIndex input.cursor
      { span := markerSpan, value := .identifier ContextualKeyword.comptime.spelling } at markerToken
    change TokenAt input.tokens input.window.endIndex (input.cursor + 1)
      { span := nameSpan, value := .identifier spelling } at nameToken
    have markerPresent : isContextual input .comptime = true := by
      unfold isContextual State.peekKind? State.peek?
      simp only [markerToken.1, if_true, markerToken.2, Option.map_some, TokenKind.isContextual]
      exact beq_iff_eq.mpr rfl
    have namePresent : (match input.peekOffsetKind? 1 with
        | some (.identifier _) => true | _ => false) = true := by
      simp only [State.peekOffsetKind?, State.peekOffset?, nameToken.1, if_true,
        nameToken.2, Option.map_some]
    exact Bool.and_eq_true_iff.mpr ⟨markerPresent, namePresent⟩

theorem comptimeGuard_false_iff {input : State} :
    comptimeGuard input = false ↔ ComptimeParameterPrefixAbsentAt input.declarativeRemainder := by
  change comptimeGuard input = false ↔ ¬ ComptimeLambdaParameterStartsAt input.declarativeRemainder
  rw [← comptimeGuard_true_iff]
  exact Bool.eq_false_iff

theorem comptimeGuard_eq_of_remainder_eq {left right : State}
    (same : left.declarativeRemainder = right.declarativeRemainder) :
    comptimeGuard left = comptimeGuard right := by
  have equivalent : comptimeGuard left = true ↔ comptimeGuard right = true := by
    rw [comptimeGuard_true_iff, comptimeGuard_true_iff, same]
  cases leftValue : comptimeGuard left <;> cases rightValue : comptimeGuard right <;> simp_all

end ParameterDispatchTraceInternals

theorem FunctionParameterInternals.namedParameterCore_eq_comptime_of_prefix
    {input : State} (present : ComptimeLambdaParameterStartsAt input.declarativeRemainder) :
    FunctionParameterInternals.namedParameterCore input =
      FunctionParameterInternals.comptimeNamedParameter input := by
  change (if ParameterDispatchTraceInternals.comptimeGuard input then _ else _) = _
  rw [ParameterDispatchTraceInternals.comptimeGuard_true_iff.mpr present]
  rfl

theorem FunctionParameterInternals.namedParameterCore_eq_ordinary_of_prefix_absent
    {input : State} (absent : ComptimeParameterPrefixAbsentAt input.declarativeRemainder) :
    FunctionParameterInternals.namedParameterCore input =
      FunctionParameterInternals.ordinaryNamedParameter input := by
  change (if ParameterDispatchTraceInternals.comptimeGuard input then _ else _) = _
  rw [ParameterDispatchTraceInternals.comptimeGuard_false_iff.mpr absent]
  rfl

theorem LambdaParameterInternals.lambdaParameterCore_eq_comptime_of_prefix
    {input : State} (present : ComptimeLambdaParameterStartsAt input.declarativeRemainder) :
    LambdaParameterInternals.lambdaParameterCore input =
      LambdaParameterInternals.comptimeLambdaParameter input := by
  change (if ParameterDispatchTraceInternals.comptimeGuard input then _ else _) = _
  rw [ParameterDispatchTraceInternals.comptimeGuard_true_iff.mpr present]
  rfl

theorem LambdaParameterInternals.lambdaParameterCore_eq_ordinary_of_prefix_absent
    {input : State} (absent : ComptimeParameterPrefixAbsentAt input.declarativeRemainder) :
    LambdaParameterInternals.lambdaParameterCore input =
      LambdaParameterInternals.ordinaryLambdaParameter input := by
  change (if ParameterDispatchTraceInternals.comptimeGuard input then _ else _) = _
  rw [ParameterDispatchTraceInternals.comptimeGuard_false_iff.mpr absent]
  rfl

end Solcore.Syntax.Parser
