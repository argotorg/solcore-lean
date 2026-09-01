import Solcore.Syntax.Parser.QualifiedNameSoundnessProperties
import Solcore.Syntax.Parser.TypeDelimitedSoundnessProperties
import Solcore.Syntax.Parser.TypeNamedProperties

/-! Success soundness for named type parsing and optional type arguments. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem namedTypeBind_success_components {α β : Type}
    {first : Parser α} {nextParser : α → Parser β}
    {input final : State} {value : β}
    (result : (first >>= nextParser) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        nextParser firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => nextParser firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/-- Requiring nonempty contents preserves state, span, and element order. -/
theorem requireNonempty_success_shape {α : Type}
    {parsed : DelimitedList α} {phase : ParserPhase}
    {input next : State} {nonempty : NonemptyDelimitedList α}
    (result : requireNonempty parsed phase input = .ok nonempty next) :
    next = input ∧ nonempty.span = parsed.span ∧
      nonempty.elements.toList = parsed.elements := by
  unfold requireNonempty at result
  cases elements : parsed.elements with
  | nil => rw [elements] at result; contradiction
  | cons head tail =>
      rw [elements] at result
      cases result
      exact ⟨rfl, rfl, by simp [NonemptyList.toList]⟩

/-- Optional named arguments follow their prioritized angle-list grammar. -/
theorem parseNamedTypeArguments_success_sound
    (nested : Parser TypeExpr)
    (nestedSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State}
    {arguments : Option (NonemptyDelimitedList TypeExpr)}
    (result : parseNamedTypeArguments nested input = .ok arguments next) :
    DeclarativeGrammar.OptionalNamedTypeArgumentsParses
      input.declarativeRemainder arguments next.declarativeRemainder := by
  unfold parseNamedTypeArguments getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .less
  · simp only [present, if_true] at result
    rcases namedTypeBind_success_components result with
      ⟨parsed, afterParsed, parsedResult, rest⟩
    rcases namedTypeBind_success_components rest with
      ⟨nonempty, afterNonempty, nonemptyResult, finished⟩
    have parsedGrammar := delimited_nonempty_trailing_success_sound
      .less .greater nested DeclarativeGrammar.TypeExprParses
      .typeExpr .typeExpr nestedSound nestedShape parsedResult
    have shape := requireNonempty_success_shape nonemptyResult
    cases finished
    rw [shape.1]
    apply optionalNamedTypeArguments_present_of_nonemptyTrailing
    simpa only [shape.2.1, shape.2.2] using parsedGrammar
  · have absent : isSymbol input .less = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .less absent)

/-- Finishing a named type changes only its AST and parser diagnostics. -/
theorem finishNamedType_success_shape
    {name : QualifiedName}
    {arguments : Option (NonemptyDelimitedList TypeExpr)}
    {input next : State} {value : TypeExpr}
    (result : finishNamedType name arguments input = .ok value next) :
    value = makeNamedType name arguments ∧
      next.declarativeRemainder = input.declarativeRemainder := by
  unfold finishNamedType at result
  dsimp only at result
  split at result
  · unfold emitDiagnostic modifyState at result
    simp only [bind] at result
    cases result
    exact ⟨rfl, by simp [State.emit, State.declarativeRemainder]⟩
  · cases result
    exact ⟨rfl, rfl⟩

/-- Successful named parsing follows its exact prioritized recursive grammar. -/
theorem parseNamedType_success_sound
    (nested : Parser TypeExpr)
    (nestedSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    {input next : State} {value : TypeExpr}
    (comptimeAbsent : DeclarativeGrammar.ContextualSymbolPairAbsentAt
      input.declarativeRemainder .comptime .less)
    (mappingAbsent : DeclarativeGrammar.ContextualSymbolPairAbsentAt
      input.declarativeRemainder .mapping .leftParen)
    (result : parseNamedType nested input = .ok value next) :
    DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
      next.declarativeRemainder := by
  unfold parseNamedType at result
  rcases namedTypeBind_success_components result with
    ⟨name, afterName, nameResult, rest⟩
  rcases namedTypeBind_success_components rest with
    ⟨arguments, afterArguments, argumentsResult, finished⟩
  have nameGrammar := qualifiedName_success_sound .typeExpr .typeExpr
    nameResult
  have argumentsGrammar := parseNamedTypeArguments_success_sound nested
    nestedSound nestedShape argumentsResult
  have finishShape := finishNamedType_success_shape finished
  apply DeclarativeGrammar.TypeExprParses.named comptimeAbsent mappingAbsent
    nameGrammar
  · rw [finishShape.1]
    unfold makeNamedType
    rfl
  · rw [finishShape.2]
    exact argumentsGrammar

/-- Named grammar soundness composes with recursive source validity. -/
theorem parseNamedType_success_sound_and_validFor
    (nested : Parser TypeExpr)
    (nestedSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    (nestedValid : nested.ValidFor TypeExpr.ValidFor)
    {input next : State} {value : TypeExpr}
    (inputValid : input.ValidFor)
    (comptimeAbsent : DeclarativeGrammar.ContextualSymbolPairAbsentAt
      input.declarativeRemainder .comptime .less)
    (mappingAbsent : DeclarativeGrammar.ContextualSymbolPairAbsentAt
      input.declarativeRemainder .mapping .leftParen)
    (result : parseNamedType nested input = .ok value next) :
    DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
        next.declarativeRemainder ∧
      TypeExpr.ValidFor input.file value := by
  refine ⟨parseNamedType_success_sound nested nestedSound nestedShape
    comptimeAbsent mappingAbsent result, ?_⟩
  have valid := parseNamedType_validFor nested nestedValid
    nestedShape.preservesTokensOnSuccess input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
