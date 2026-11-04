import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.DelimitedTotality
import Solcore.Syntax.Parser.Internal.TypeBasics
import Solcore.Syntax.Parser.Internal.Basics

/-!
Totality of the parsers of named, simple and function types: on valid input they make
progress and end in an ordinary outcome.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.TypeSimpleTotalityProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.QualifiedNameTotalityProperties
/-! Fuel adequacy and totality for qualified-name parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace QualifiedNameInternals

/-- More fuel than remaining tokens makes the dotted-name tail ordinary. -/
theorem qualifiedNameTail_ordinary_of_remainingCount_lt
    (context : ParseContext) (phase : ParserPhase) (first : Identifier) :
    ∀ fuel last tailRev state, state.remainingCount < fuel →
      (∃ name next,
        qualifiedNameTail context phase first fuel last tailRev state =
          .ok name next) ∨
      (∃ failure next,
        qualifiedNameTail context phase first fuel last tailRev state =
          .reject failure next) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev state adequate
      omega
  | succ fuel inductionHypothesis =>
      intro last tailRev state adequate
      unfold qualifiedNameTail
      split
      · cases dotResult : symbol .dot context state with
        | invariant error =>
            exact False.elim
              (symbol_ne_invariant .dot context state error dotResult)
        | reject failure rejected =>
            exact Or.inr ⟨failure, rejected, rfl⟩
        | ok dot afterDot =>
            dsimp only
            cases componentResult : identifier context afterDot with
            | invariant error =>
                exact False.elim
                  (identifier_ne_invariant context afterDot error
                    componentResult)
            | reject failure rejected =>
                exact Or.inr ⟨failure, rejected, rfl⟩
            | ok component next =>
                change
                  (∃ name final,
                    qualifiedNameTail context phase first fuel component
                      (component :: tailRev) next = .ok name final) ∨
                  (∃ failure final,
                    qualifiedNameTail context phase first fuel component
                      (component :: tailRev) next = .reject failure final)
                apply inductionHypothesis component (component :: tailRev) next
                have dotShape := symbol_ok_state_shape .dot context dotResult
                rcases identifier_ok_state_shape context componentResult with
                  ⟨_, _, _, _, componentCursor⟩
                have dotWindow := symbol_preservesTokenWindow .dot context state
                rw [dotResult] at dotWindow
                have componentWindow :=
                  identifier_preservesTokenWindow context afterDot
                rw [componentResult] at componentWindow
                have nextWindow : next.window = state.window :=
                  componentWindow.2.trans dotWindow.2
                have endIndexEq :
                    next.window.endIndex = state.window.endIndex :=
                  congrArg TokenWindow.endIndex nextWindow
                have cursorBeforeEnd :=
                  State.cursor_lt_endIndex_of_peek?_eq_some dotShape.1
                have nextCursor : next.cursor = state.cursor + 2 := by
                  rw [componentCursor, dotShape.2]
                simp only [State.remainingCount] at adequate ⊢
                rw [endIndexEq, nextCursor]
                omega
      · exact Or.inl ⟨_, _, rfl⟩

/-- Adequate dotted-name fuel excludes all internal invariant results. -/
theorem qualifiedNameTail_ne_invariant_of_remainingCount_lt
    (context : ParseContext) (phase : ParserPhase) (first last : Identifier)
    (fuel : Nat) (tailRev : List Identifier) (state : State)
    (adequate : state.remainingCount < fuel)
    (error : ParserInvariantError) :
    qualifiedNameTail context phase first fuel last tailRev state ≠
      .invariant error := by
  intro failed
  rcases qualifiedNameTail_ordinary_of_remainingCount_lt context phase first
      fuel last tailRev state adequate with
    ⟨name, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- The exact production fuel for a qualified-name tail is sufficient. -/
theorem qualifiedNameTail_production_ordinary
    (context : ParseContext) (phase : ParserPhase) (first last : Identifier)
    (tailRev : List Identifier) (state : State) :
    (∃ name next,
      qualifiedNameTail context phase first (state.remainingCount + 1)
        last tailRev state = .ok name next) ∨
      (∃ failure next,
        qualifiedNameTail context phase first (state.remainingCount + 1)
          last tailRev state = .reject failure next) :=
  qualifiedNameTail_ordinary_of_remainingCount_lt context phase first
    (state.remainingCount + 1) last tailRev state (by omega)

end QualifiedNameInternals

/-- Public qualified-name parsing is ordinary on every input. -/
theorem qualifiedName_ordinary (context : ParseContext) (phase : ParserPhase) :
    Parser.Ordinary (qualifiedName context phase) := by
  intro input
  unfold qualifiedName
  cases firstResult : identifier context input with
  | invariant error =>
      exact False.elim
        (identifier_ne_invariant context input error firstResult)
  | reject failure rejected =>
      exact Or.inr ⟨failure, rejected, rfl⟩
  | ok first next =>
      dsimp only
      exact QualifiedNameInternals.qualifiedNameTail_production_ordinary
        context phase first first [] next

/-- Public qualified names cannot expose fuel or primitive invariants. -/
theorem qualifiedName_ne_invariant (context : ParseContext)
    (phase : ParserPhase) (input : State) (error : ParserInvariantError) :
    qualifiedName context phase input ≠ .invariant error :=
  (qualifiedName_ordinary context phase).ne_invariant input error

/-- Qualified names can instantiate generic delimited element parsing. -/
theorem qualifiedName_elementTotalityContract (context : ParseContext)
    (phase : ParserPhase) :
    ElementTotalityContract (qualifiedName context phase) := {
  validFor := (qualifiedName_validFor context phase).mono
    (fun _ _ _ => trivial)
  preservesTokenWindow := qualifiedName_preservesTokenWindow context phase
  cursorLtOnSuccess := qualifiedName_cursor_lt_onSuccess context phase
  invariantFree := fun input _ error =>
    qualifiedName_ne_invariant context phase input error
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeNamedTotalityProperties
/-! Valid-input totality for the named-type parser path. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A successful syntactically nonempty delimited parse satisfies `requireNonempty`. -/
theorem requireNonempty_ok_of_delimited_false_ok {α : Type}
    (opening closing : Symbol) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase)
    {input afterDelimited : State} {parsed : DelimitedList α}
    (parsedResult : delimited opening closing false element context phase input =
      .ok parsed afterDelimited) :
    ∃ nonempty,
      requireNonempty parsed phase afterDelimited = .ok nonempty afterDelimited := by
  have nonempty := delimited_false_elements_ne_nil_onSuccess opening closing
    element context phase parsedResult
  unfold requireNonempty
  cases elements : parsed.elements with
  | nil => exact False.elim (nonempty elements)
  | cons head tail => exact ⟨_, rfl⟩

/-- In particular, `requireNonempty` cannot expose its defensive invariant. -/
theorem requireNonempty_ne_invariant_of_delimited_false_ok {α : Type}
    (opening closing : Symbol) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase)
    {input afterDelimited : State} {parsed : DelimitedList α}
    (parsedResult : delimited opening closing false element context phase input =
      .ok parsed afterDelimited)
    (error : ParserInvariantError) :
    requireNonempty parsed phase afterDelimited ≠ .invariant error := by
  intro failed
  rcases requireNonempty_ok_of_delimited_false_ok opening closing element
      context phase parsedResult with ⟨nonempty, result⟩
  rw [result] at failed
  contradiction

theorem parseNamedTypeArguments_ordinary
    (nested : Parser TypeExpr) (contract : ElementTotalityContract nested)
    (input : State) (inputValid : input.ValidFor) :
    (∃ arguments next,
      parseNamedTypeArguments nested input = .ok arguments next) ∨
    (∃ failure next,
      parseNamedTypeArguments nested input = .reject failure next) := by
  by_cases present : isSymbol input .less
  · rcases delimited_ordinary .less .greater false nested .typeExpr .typeExpr
        contract input inputValid with
      ⟨parsed, afterDelimited, parsedResult⟩ |
      ⟨failure, rejected, parsedResult⟩
    · rcases requireNonempty_ok_of_delimited_false_ok .less .greater nested
        .typeExpr .typeExpr parsedResult with ⟨nonempty, nonemptyResult⟩
      exact Or.inl ⟨some nonempty, afterDelimited, by
        simp only [parseNamedTypeArguments, getState, bind, present,
          ↓reduceIte, parsedResult, nonemptyResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseNamedTypeArguments, getState, bind, present,
          ↓reduceIte, parsedResult]⟩
  · have absent : isSymbol input .less = false := by
      cases found : isSymbol input .less with
      | false => rfl
      | true => exact False.elim (present found)
    exact Or.inl ⟨none, input, by
      simp only [parseNamedTypeArguments, getState, bind, absent,
        Bool.false_eq_true, ↓reduceIte, pure]⟩

theorem parseNamedTypeArguments_ne_invariant
    (nested : Parser TypeExpr) (contract : ElementTotalityContract nested)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parseNamedTypeArguments nested input ≠ .invariant error := by
  intro failed
  rcases parseNamedTypeArguments_ordinary nested contract input inputValid with
    ⟨arguments, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- Finishing a named type only performs total state update and construction. -/
theorem finishNamedType_ordinary (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) :
    Parser.Ordinary (finishNamedType name arguments) := by
  intro input
  unfold finishNamedType
  split
  · exact Or.inl ⟨makeNamedType name arguments, _, rfl⟩
  · exact Or.inl ⟨makeNamedType name arguments, input, rfl⟩

theorem finishNamedType_ne_invariant (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr))
    (input : State) (error : ParserInvariantError) :
    finishNamedType name arguments input ≠ .invariant error :=
  (finishNamedType_ordinary name arguments).ne_invariant input error

theorem parseNamedType_ordinary
    (nested : Parser TypeExpr) (contract : ElementTotalityContract nested)
    (input : State) (inputValid : input.ValidFor) :
    (∃ value next, parseNamedType nested input = .ok value next) ∨
    (∃ failure next, parseNamedType nested input = .reject failure next) := by
  rcases (qualifiedName_ordinary .typeExpr .typeExpr) input with
    ⟨name, afterName, nameResult⟩ | ⟨failure, rejected, nameResult⟩
  · have nameValid := qualifiedName_validFor .typeExpr .typeExpr input inputValid
    rw [nameResult] at nameValid
    rcases parseNamedTypeArguments_ordinary nested contract afterName
        nameValid.2.1 with
      ⟨arguments, afterArguments, argumentsResult⟩ |
      ⟨failure, rejected, argumentsResult⟩
    · rcases finishNamedType_ordinary name arguments afterArguments with
        ⟨value, final, finished⟩ | ⟨failure, rejected, finished⟩
      · exact Or.inl ⟨value, final, by
          simp only [parseNamedType, bind, nameResult, argumentsResult,
            finished]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [parseNamedType, bind, nameResult, argumentsResult,
            finished]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseNamedType, bind, nameResult, argumentsResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [parseNamedType, bind, nameResult]⟩

theorem parseNamedType_ne_invariant
    (nested : Parser TypeExpr) (contract : ElementTotalityContract nested)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parseNamedType nested input ≠ .invariant error := by
  intro failed
  rcases parseNamedType_ordinary nested contract input inputValid with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeNamedFuelTotalityProperties
/-! Fuel-aware totality for recursive named-type parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/--
Optional named-type arguments are ordinary when their delimited elements have
one less unit of recursive fuel available at the opening delimiter.
-/
theorem parseNamedTypeArguments_ordinary_of_elementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : FuelElementTotalityContract nested elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1) :
    (∃ arguments next,
      parseNamedTypeArguments nested input = .ok arguments next) ∨
    (∃ failure next,
      parseNamedTypeArguments nested input = .reject failure next) := by
  by_cases present : isSymbol input .less
  · rcases delimited_ordinary_of_elementFuel .less .greater false nested
        .typeExpr .typeExpr elementFuel contract input inputValid adequate with
      ⟨parsed, afterDelimited, parsedResult⟩ |
      ⟨failure, rejected, parsedResult⟩
    · rcases requireNonempty_ok_of_delimited_false_ok .less .greater nested
          .typeExpr .typeExpr parsedResult with
        ⟨nonempty, nonemptyResult⟩
      exact Or.inl ⟨some nonempty, afterDelimited, by
        simp only [parseNamedTypeArguments, getState, bind, present,
          ↓reduceIte, parsedResult, nonemptyResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseNamedTypeArguments, getState, bind, present,
          ↓reduceIte, parsedResult]⟩
  · have absent : isSymbol input .less = false := by
      cases found : isSymbol input .less with
      | false => rfl
      | true => exact False.elim (present found)
    exact Or.inl ⟨none, input, by
      simp only [parseNamedTypeArguments, getState, bind, absent,
        Bool.false_eq_true, ↓reduceIte, pure]⟩

theorem parseNamedTypeArguments_ne_invariant_of_elementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : FuelElementTotalityContract nested elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) :
    parseNamedTypeArguments nested input ≠ .invariant error := by
  intro failed
  rcases parseNamedTypeArguments_ordinary_of_elementFuel nested elementFuel
      contract input inputValid adequate with
    ⟨arguments, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/--
A named type is ordinary with one fuel unit beyond its nested elements. Its
qualified name strictly consumes the unit before optional generic arguments.
-/
theorem parseNamedType_ordinary_of_elementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : FuelElementTotalityContract nested elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1) :
    (∃ value next, parseNamedType nested input = .ok value next) ∨
    (∃ failure next, parseNamedType nested input = .reject failure next) := by
  rcases (qualifiedName_ordinary .typeExpr .typeExpr) input with
    ⟨name, afterName, nameResult⟩ | ⟨failure, rejected, nameResult⟩
  · have nameValid := qualifiedName_validFor .typeExpr .typeExpr
      input inputValid
    rw [nameResult] at nameValid
    have nameWindow := qualifiedName_preservesTokenWindow .typeExpr .typeExpr
      input
    rw [nameResult] at nameWindow
    have afterNameAdequate : afterName.remainingCount < elementFuel :=
      remainingCount_lt_after_strict_progress nameValid.2.1 nameWindow.2
        (qualifiedName_cursor_lt_onSuccess .typeExpr .typeExpr nameResult)
        adequate
    rcases parseNamedTypeArguments_ordinary_of_elementFuel nested elementFuel
        contract afterName nameValid.2.1 (by omega) with
      ⟨arguments, afterArguments, argumentsResult⟩ |
      ⟨failure, rejected, argumentsResult⟩
    · rcases finishNamedType_ordinary name arguments afterArguments with
        ⟨value, final, finished⟩ | ⟨failure, rejected, finished⟩
      · exact Or.inl ⟨value, final, by
          simp only [parseNamedType, bind, nameResult, argumentsResult,
            finished]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [parseNamedType, bind, nameResult, argumentsResult,
            finished]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseNamedType, bind, nameResult, argumentsResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [parseNamedType, bind, nameResult]⟩

theorem parseNamedType_ne_invariant_of_elementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : FuelElementTotalityContract nested elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) :
    parseNamedType nested input ≠ .invariant error := by
  intro failed
  rcases parseNamedType_ordinary_of_elementFuel nested elementFuel contract
      input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeFunctionTotalityProperties
/-! Valid-input totality for function-type parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace TypeFunctionInternals

/-- Optional function returns add no invariant beyond the nested type parser. -/
theorem parseFunctionReturns_invariantFreeOnValid
    (nested : Parser TypeExpr) (contract : ElementTotalityContract nested) :
    Parser.InvariantFreeOnValid (parseFunctionReturns nested) := by
  intro input inputValid
  by_cases present : isContextual input .returns
  · rcases (contextual_ordinary .returns .typeExpr) input with
      ⟨marker, afterMarker, markerResult⟩ |
      ⟨failure, rejected, markerResult⟩
    · have markerValid := contextual_validFor .returns .typeExpr input inputValid
      rw [markerResult] at markerValid
      rcases delimited_ordinary .leftParen .rightParen true nested
          .typeExpr .typeExpr contract afterMarker markerValid.2.1 with
        ⟨values, final, valuesResult⟩ |
        ⟨failure, rejected, valuesResult⟩
      · exact Or.inl ⟨some values, final, by
          simp only [parseFunctionReturns, getState, bind, present,
            ↓reduceIte, markerResult, valuesResult, pure]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [parseFunctionReturns, getState, bind, present,
            ↓reduceIte, markerResult, valuesResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseFunctionReturns, getState, bind, present,
          ↓reduceIte, markerResult]⟩
  · have absent : isContextual input .returns = false := by
      cases found : isContextual input .returns with
      | false => rfl
      | true => exact False.elim (present found)
    exact Or.inl ⟨none, input, by
      simp only [parseFunctionReturns, getState, bind, absent,
        Bool.false_eq_true, ↓reduceIte, pure]⟩

theorem parseFunctionReturns_ordinary
    (nested : Parser TypeExpr) (contract : ElementTotalityContract nested)
    (input : State) (inputValid : input.ValidFor) :
    (∃ returns next, parseFunctionReturns nested input = .ok returns next) ∨
    (∃ failure next,
      parseFunctionReturns nested input = .reject failure next) :=
  parseFunctionReturns_invariantFreeOnValid nested contract input inputValid

theorem parseFunctionReturns_ne_invariant
    (nested : Parser TypeExpr) (contract : ElementTotalityContract nested)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parseFunctionReturns nested input ≠ .invariant error :=
  (parseFunctionReturns_invariantFreeOnValid nested contract).ne_invariant
    input inputValid error

end TypeFunctionInternals

open TypeFunctionInternals

/-- Function types add no invariant beyond their nested type parser. -/
theorem parseFunctionType_invariantFreeOnValid
    (nested : Parser TypeExpr) (contract : ElementTotalityContract nested) :
    Parser.InvariantFreeOnValid (parseFunctionType nested) := by
  intro input inputValid
  rcases (keyword_ordinary .functionKw .typeExpr) input with
    ⟨functionKeyword, afterKeyword, keywordResult⟩ |
    ⟨failure, rejected, keywordResult⟩
  · have keywordValid := keyword_validFor .functionKw .typeExpr input inputValid
    rw [keywordResult] at keywordValid
    rcases delimited_ordinary .leftParen .rightParen true nested
        .typeExpr .typeExpr contract afterKeyword keywordValid.2.1 with
      ⟨parameters, afterParameters, parametersResult⟩ |
      ⟨failure, rejected, parametersResult⟩
    · have parametersValid := delimited_validFor (fun _ _ => True)
        .leftParen .rightParen true nested .typeExpr .typeExpr
        contract.validFor
        contract.preservesTokenWindow.preservesTokensOnSuccess
        afterKeyword keywordValid.2.1
      rw [parametersResult] at parametersValid
      rcases parseFunctionReturns_ordinary nested contract afterParameters
          parametersValid.2.1 with
        ⟨returns, final, returnsResult⟩ |
        ⟨failure, rejected, returnsResult⟩
      · let endSpan := match returns with
          | some values => values.span
          | none => parameters.span
        exact Or.inl ⟨{
            span := SourceSpan.cover functionKeyword.span endSpan
            value := .function functionKeyword.span parameters returns
          }, final, by
            simp only [parseFunctionType, bind, keywordResult,
              parametersResult, returnsResult, pure]
            rfl⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [parseFunctionType, bind, keywordResult,
            parametersResult, returnsResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseFunctionType, bind, keywordResult, parametersResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [parseFunctionType, bind, keywordResult]⟩

theorem parseFunctionType_ordinary
    (nested : Parser TypeExpr) (contract : ElementTotalityContract nested)
    (input : State) (inputValid : input.ValidFor) :
    (∃ value next, parseFunctionType nested input = .ok value next) ∨
    (∃ failure next, parseFunctionType nested input = .reject failure next) :=
  parseFunctionType_invariantFreeOnValid nested contract input inputValid

theorem parseFunctionType_ne_invariant
    (nested : Parser TypeExpr) (contract : ElementTotalityContract nested)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parseFunctionType nested input ≠ .invariant error :=
  (parseFunctionType_invariantFreeOnValid nested contract).ne_invariant
    input inputValid error

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeFunctionFuelTotalityProperties
/-! Fuel-aware totality for recursive function-type parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace TypeFunctionInternals

/--
Optional function returns are ordinary when their input has one unit more than
the nested element-fuel bound. A present `returns` consumes that extra unit
before entering its delimited result list.
-/
theorem parseFunctionReturns_ordinary_of_elementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : FuelElementTotalityContract nested elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1) :
    (∃ returns next, parseFunctionReturns nested input = .ok returns next) ∨
      (∃ failure next,
        parseFunctionReturns nested input = .reject failure next) := by
  by_cases present : isContextual input .returns
  · rcases (contextual_ordinary .returns .typeExpr) input with
      ⟨marker, afterMarker, markerResult⟩ |
      ⟨failure, rejected, markerResult⟩
    · have markerValid := contextual_validFor .returns .typeExpr
        input inputValid
      rw [markerResult] at markerValid
      have markerWindow := contextual_preservesTokenWindow .returns .typeExpr
        input
      rw [markerResult] at markerWindow
      have markerProgress : input.cursor < afterMarker.cursor :=
        acceptToken_cursor_lt_onSuccess (.contextual .returns) .typeExpr
          (·.isContextual .returns) markerResult
      have afterMarkerAdequate :
          afterMarker.remainingCount < elementFuel :=
        remainingCount_lt_after_strict_progress markerValid.2.1
          markerWindow.2 markerProgress adequate
      rcases delimited_ordinary_of_elementFuel .leftParen .rightParen true
          nested .typeExpr .typeExpr elementFuel contract afterMarker
          markerValid.2.1 (by omega) with
        ⟨values, final, valuesResult⟩ |
        ⟨failure, rejected, valuesResult⟩
      · exact Or.inl ⟨some values, final, by
          simp only [parseFunctionReturns, getState, bind, present,
            ↓reduceIte, markerResult, valuesResult, pure]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [parseFunctionReturns, getState, bind, present,
            ↓reduceIte, markerResult, valuesResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseFunctionReturns, getState, bind, present,
          ↓reduceIte, markerResult]⟩
  · have absent : isContextual input .returns = false := by
      cases found : isContextual input .returns with
      | false => rfl
      | true => exact False.elim (present found)
    exact Or.inl ⟨none, input, by
      simp only [parseFunctionReturns, getState, bind, absent,
        Bool.false_eq_true, ↓reduceIte, pure]⟩

theorem parseFunctionReturns_ne_invariant_of_elementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : FuelElementTotalityContract nested elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) :
    parseFunctionReturns nested input ≠ .invariant error := by
  intro failed
  rcases parseFunctionReturns_ordinary_of_elementFuel nested elementFuel
      contract input inputValid adequate with
    ⟨returns, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end TypeFunctionInternals

/--
A function type is ordinary with one unit more than its nested element fuel.
The keyword pays that unit; parameter and return-list successes preserve the
strict remaining-count bound passed to later stages.
-/
theorem parseFunctionType_ordinary_of_elementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : FuelElementTotalityContract nested elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1) :
    (∃ value next, parseFunctionType nested input = .ok value next) ∨
      (∃ failure next,
        parseFunctionType nested input = .reject failure next) := by
  rcases (keyword_ordinary .functionKw .typeExpr) input with
    ⟨functionKeyword, afterKeyword, keywordResult⟩ |
    ⟨failure, rejected, keywordResult⟩
  · have keywordValid := keyword_validFor .functionKw .typeExpr
      input inputValid
    rw [keywordResult] at keywordValid
    have keywordWindow := keyword_preservesTokenWindow .functionKw .typeExpr
      input
    rw [keywordResult] at keywordWindow
    have keywordProgress : input.cursor < afterKeyword.cursor :=
      acceptToken_cursor_lt_onSuccess (.keyword .functionKw) .typeExpr
        (· == .keyword .functionKw) keywordResult
    have afterKeywordAdequate :
        afterKeyword.remainingCount < elementFuel :=
      remainingCount_lt_after_strict_progress keywordValid.2.1
        keywordWindow.2 keywordProgress adequate
    rcases delimited_ordinary_of_elementFuel .leftParen .rightParen true
        nested .typeExpr .typeExpr elementFuel contract afterKeyword
        keywordValid.2.1 (by omega) with
      ⟨parameters, afterParameters, parametersResult⟩ |
      ⟨failure, rejected, parametersResult⟩
    · have parametersValid := delimited_validFor (fun _ _ => True)
        .leftParen .rightParen true nested .typeExpr .typeExpr
        contract.validFor
        contract.preservesTokenWindow.preservesTokensOnSuccess
        afterKeyword keywordValid.2.1
      rw [parametersResult] at parametersValid
      have parametersWindow := delimited_preservesTokenWindow
        .leftParen .rightParen true nested .typeExpr .typeExpr
        contract.preservesTokenWindow afterKeyword
      rw [parametersResult] at parametersWindow
      have parametersMonotone := delimited_cursorMonotoneOnSuccess
        .leftParen .rightParen true nested .typeExpr .typeExpr
        afterKeyword parameters afterParameters parametersResult
      have afterParametersAdequate :
          afterParameters.remainingCount < elementFuel :=
        remainingCount_lt_of_cursor_le parametersWindow.2
          parametersMonotone afterKeywordAdequate
      rcases TypeFunctionInternals.parseFunctionReturns_ordinary_of_elementFuel
          nested elementFuel
          contract afterParameters parametersValid.2.1 (by omega) with
        ⟨returns, final, returnsResult⟩ |
        ⟨failure, rejected, returnsResult⟩
      · let endSpan := match returns with
          | some values => values.span
          | none => parameters.span
        exact Or.inl ⟨{
            span := SourceSpan.cover functionKeyword.span endSpan
            value := .function functionKeyword.span parameters returns
          }, final, by
            simp only [parseFunctionType, bind, keywordResult,
              parametersResult, returnsResult, pure]
            rfl⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [parseFunctionType, bind, keywordResult,
            parametersResult, returnsResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseFunctionType, bind, keywordResult, parametersResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [parseFunctionType, bind, keywordResult]⟩

theorem parseFunctionType_ne_invariant_of_elementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : FuelElementTotalityContract nested elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) :
    parseFunctionType nested input ≠ .invariant error := by
  intro failed
  rcases parseFunctionType_ordinary_of_elementFuel nested elementFuel
      contract input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser
end
