import Solcore.Syntax.Parser.Internal.ExportProofs
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.DelimitedTotality
import Solcore.Syntax.Parser.Internal.ImportProofs

/-!
Totality of the parsers of imports, exports and pragmas: on valid input they make progress
and end in an ordinary outcome.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.PragmaTotalityProperties
/-! Fuel adequacy and ordinary-result classification for pragma parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem acceptToken_ordinary_variant
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) (state : State) :
    (∃ token final,
      acceptToken expected context accepts state = .ok token final) ∨
      (∃ failure final,
        acceptToken expected context accepts state = .reject failure final) := by
  cases found : state.peek? with
  | none =>
      right
      simp [acceptToken, found, rejectAt]
  | some token =>
      by_cases accepted : accepts token.value = true
      · left
        exact ⟨token, { state with cursor := state.cursor + 1 }, by
          simp [acceptToken, found, accepted]⟩
      · right
        simp [acceptToken, found, accepted, rejectAt]

private theorem keyword_ordinary_variant (value : HardKeyword)
    (context : ParseContext) (state : State) :
    (∃ token final, keyword value context state = .ok token final) ∨
      (∃ failure final,
        keyword value context state = .reject failure final) :=
  acceptToken_ordinary_variant (.keyword value) context
    (· == .keyword value) state

private theorem symbol_ordinary_variant (value : Symbol)
    (context : ParseContext) (state : State) :
    (∃ token final, symbol value context state = .ok token final) ∨
      (∃ failure final,
        symbol value context state = .reject failure final) :=
  acceptToken_ordinary_variant (.symbol value) context
    (· == .symbol value) state

private theorem rawIdentifier_ordinary_variant (context : ParseContext)
    (state : State) :
    (∃ name final, rawIdentifier context state = .ok name final) ∨
      (∃ failure final,
        rawIdentifier context state = .reject failure final) := by
  unfold rawIdentifier
  cases found : state.peek? with
  | none =>
      right
      simp [rejectAt]
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp [rejectAt]

private theorem identifier_ordinary_variant (context : ParseContext)
    (state : State) :
    (∃ name final, identifier context state = .ok name final) ∨
      (∃ failure final,
        identifier context state = .reject failure final) := by
  unfold identifier
  rcases rawIdentifier_ordinary_variant context state with
    ⟨name, next, result⟩ | ⟨failure, rejected, result⟩
  · simp only [result]
    split <;> exact Or.inl ⟨name, _, rfl⟩
  · exact Or.inr ⟨failure, rejected, by simp only [result]⟩

private theorem ne_invariant_of_ordinary {alpha : Type}
    {reply : Reply alpha}
    (ordinary : (∃ value final, reply = .ok value final) ∨
      (∃ failure final, reply = .reject failure final))
    (error : ParserInvariantError) : reply ≠ .invariant error := by
  intro invariantResult
  rcases ordinary with ⟨value, final, result⟩ |
      ⟨failure, final, result⟩ <;>
    rw [result] at invariantResult <;> contradiction

namespace PragmaInternals

private theorem remainingCount_lt_after_items_step
    {fuel : Nat} {input afterComma next : State}
    {comma : Token} {item : Identifier}
    (commaResult : symbol .comma .pragmaDecl input = .ok comma afterComma)
    (itemResult : identifier .pragmaDecl afterComma = .ok item next)
    (adequate : input.remainingCount < fuel + 1) :
    next.remainingCount < fuel := by
  rcases symbol_ok_state_shape .comma .pragmaDecl commaResult with
    ⟨commaFound, rfl⟩
  rcases identifier_ok_state_shape .pragmaDecl itemResult with
    ⟨_token, _found, _span, _tokens, itemCursor⟩
  have itemWindow := identifier_preservesTokenWindow .pragmaDecl
    { input with cursor := input.cursor + 1 }
  rw [itemResult] at itemWindow
  have cursorBeforeEnd :=
    State.cursor_lt_endIndex_of_peek?_eq_some commaFound
  have endIndexEq : next.window.endIndex = input.window.endIndex := by
    simpa using congrArg TokenWindow.endIndex itemWindow.2
  have cursorEq : next.cursor = input.cursor + 2 := by
    simpa only [State.cursor] using itemCursor
  simp only [State.remainingCount] at adequate ⊢
  rw [endIndexEq, cursorEq]
  omega

/-- More fuel than remaining tokens rules out pragma-tail fuel exhaustion. -/
theorem pragmaItemsTail_ordinary_of_remainingCount_lt :
    ∀ fuel itemsRev input, input.remainingCount < fuel →
      (∃ items final,
        pragmaItemsTail fuel itemsRev input = .ok items final) ∨
      (∃ failure final,
        pragmaItemsTail fuel itemsRev input = .reject failure final) := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input adequate
      omega
  | succ fuel inductionHypothesis =>
      intro itemsRev input adequate
      unfold pragmaItemsTail
      split
      · rcases symbol_ordinary_variant .comma .pragmaDecl input with
          ⟨comma, afterComma, commaResult⟩ |
          ⟨failure, rejected, commaResult⟩
        · simp only [commaResult]
          split
          · exact Or.inl ⟨_, _, rfl⟩
          · rcases identifier_ordinary_variant .pragmaDecl afterComma with
              ⟨item, next, itemResult⟩ |
              ⟨failure, rejected, itemResult⟩
            · simp only [itemResult]
              exact inductionHypothesis (item :: itemsRev) next
                (remainingCount_lt_after_items_step commaResult itemResult
                  adequate)
            · exact Or.inr ⟨failure, rejected, by
                simp only [itemResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [commaResult]⟩
      · exact Or.inl ⟨_, _, rfl⟩

/-- The production tail fuel is always adequate. -/
theorem pragmaItemsTail_production_ordinary
    (itemsRev : List Identifier) (state : State) :
    (∃ items final,
      pragmaItemsTail (state.remainingCount + 1) itemsRev state =
        .ok items final) ∨
      (∃ failure final,
        pragmaItemsTail (state.remainingCount + 1) itemsRev state =
          .reject failure final) :=
  pragmaItemsTail_ordinary_of_remainingCount_lt
    (state.remainingCount + 1) itemsRev state (by omega)

/-- Production tail parsing cannot expose an invariant failure. -/
theorem pragmaItemsTail_production_ne_invariant
    (itemsRev : List Identifier) (state : State)
    (error : ParserInvariantError) :
    pragmaItemsTail (state.remainingCount + 1) itemsRev state ≠
      .invariant error :=
  ne_invariant_of_ordinary
    (pragmaItemsTail_production_ordinary itemsRev state) error

/-- Pragma-item parsing always returns an ordinary success or rejection. -/
theorem pragmaItems_ordinary (state : State) :
    (∃ items final, pragmaItems state = .ok items final) ∨
      (∃ failure final,
        pragmaItems state = .reject failure final) := by
  unfold pragmaItems
  split
  · exact Or.inl ⟨[], state, rfl⟩
  · rcases identifier_ordinary_variant .pragmaDecl state with
      ⟨item, next, itemResult⟩ | ⟨failure, rejected, itemResult⟩
    · simp only [itemResult]
      exact pragmaItemsTail_production_ordinary [item] next
    · exact Or.inr ⟨failure, rejected, by simp only [itemResult]⟩

/-- Pragma-item parsing cannot expose an invariant failure. -/
theorem pragmaItems_ne_invariant (state : State)
    (error : ParserInvariantError) :
    pragmaItems state ≠ .invariant error :=
  ne_invariant_of_ordinary (pragmaItems_ordinary state) error

end PragmaInternals

/-- A pragma declaration always returns an ordinary success or rejection. -/
theorem pragmaDecl_ordinary (state : State) :
    (∃ declaration final, pragmaDecl state = .ok declaration final) ∨
      (∃ failure final,
        pragmaDecl state = .reject failure final) := by
  unfold pragmaDecl
  rcases keyword_ordinary_variant .pragmaKw .pragmaDecl state with
    ⟨pragmaKeyword, afterKeyword, keywordResult⟩ |
    ⟨failure, rejected, keywordResult⟩
  · simp only [keywordResult, bind]
    rcases rawIdentifier_ordinary_variant .pragmaDecl afterKeyword with
      ⟨name, afterName, nameResult⟩ | ⟨failure, rejected, nameResult⟩
    · simp only [nameResult]
      rcases PragmaInternals.pragmaItems_ordinary afterName with
        ⟨items, afterItems, itemsResult⟩ |
        ⟨failure, rejected, itemsResult⟩
      · simp only [itemsResult]
        rcases symbol_ordinary_variant .semicolon .pragmaDecl afterItems with
          ⟨semicolon, final, semicolonResult⟩ |
          ⟨failure, rejected, semicolonResult⟩
        · refine Or.inl ⟨{
              span := SourceSpan.cover pragmaKeyword.span semicolon.span
              value := { name, items }
            }, final, ?_⟩
          simp only [semicolonResult, pure]
        · exact Or.inr ⟨failure, rejected, by
            simp only [semicolonResult]⟩
      · exact Or.inr ⟨failure, rejected, by simp only [itemsResult]⟩
    · exact Or.inr ⟨failure, rejected, by simp only [nameResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [keywordResult, bind]⟩

/-- Canonical pragma parsing cannot expose an internal invariant failure. -/
theorem pragmaDecl_ne_invariant (state : State)
    (error : ParserInvariantError) :
    pragmaDecl state ≠ .invariant error :=
  ne_invariant_of_ordinary (pragmaDecl_ordinary state) error

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExportConstructorTotalityProperties
/-! Totality for export constructor selections. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExportInternals

/-- A successful syntactically nonempty list satisfies the retained carrier. -/
theorem requireConstructorNames_ok_of_delimitedNoTrailing_false_ok
    {input afterDelimited : State} {values : DelimitedList Identifier}
    (valuesResult : delimitedNoTrailing .leftParen .rightParen false
      (identifier .exportDecl) .exportDecl .topLevel input =
        .ok values afterDelimited) :
    ∃ constructors,
      requireConstructorNames values afterDelimited =
        .ok constructors afterDelimited := by
  have nonempty := delimitedNoTrailing_false_elements_ne_nil_onSuccess
    .leftParen .rightParen (identifier .exportDecl) .exportDecl .topLevel
    valuesResult
  unfold requireConstructorNames
  cases elements : values.elements with
  | nil => exact False.elim (nonempty elements)
  | cons head tail => exact ⟨_, rfl⟩

theorem requireConstructorNames_ne_invariant_of_delimitedNoTrailing_false_ok
    {input afterDelimited : State} {values : DelimitedList Identifier}
    (valuesResult : delimitedNoTrailing .leftParen .rightParen false
      (identifier .exportDecl) .exportDecl .topLevel input =
        .ok values afterDelimited)
    (error : ParserInvariantError) :
    requireConstructorNames values afterDelimited ≠ .invariant error := by
  intro failed
  rcases requireConstructorNames_ok_of_delimitedNoTrailing_false_ok
      valuesResult with ⟨constructors, result⟩
  rw [result] at failed
  contradiction

theorem constructorSelection_invariantFreeOnValid :
    Parser.InvariantFreeOnValid constructorSelection := by
  intro input inputValid
  by_cases all : input.peekOffsetKind? 1 == some (.symbol .star)
  · rcases (symbol_ordinary .leftParen .exportDecl) input with
      ⟨opening, afterOpening, openingResult⟩ |
      ⟨failure, rejected, openingResult⟩
    · have openingValid := symbol_validFor .leftParen .exportDecl input inputValid
      rw [openingResult] at openingValid
      rcases (symbol_ordinary .star .exportDecl) afterOpening with
        ⟨marker, afterMarker, markerResult⟩ |
        ⟨failure, rejected, markerResult⟩
      · have markerValid := symbol_validFor .star .exportDecl afterOpening
          openingValid.2.1
        rw [markerResult] at markerValid
        rcases (symbol_ordinary .rightParen .exportDecl) afterMarker with
          ⟨closing, final, closingResult⟩ |
          ⟨failure, rejected, closingResult⟩
        · exact Or.inl ⟨{
              span := SourceSpan.cover opening.span closing.span
              value := .all marker.span
            }, final, by
              simp only [constructorSelection, getState, bind, all,
                ↓reduceIte, openingResult, markerResult, closingResult, pure]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [constructorSelection, getState, bind, all,
              ↓reduceIte, openingResult, markerResult, closingResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [constructorSelection, getState, bind, all,
            ↓reduceIte, openingResult, markerResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [constructorSelection, getState, bind, all,
          ↓reduceIte, openingResult]⟩
  · have named :
        (input.peekOffsetKind? 1 == some (.symbol .star)) = false := by
      cases found : input.peekOffsetKind? 1 == some (.symbol .star) with
      | false => rfl
      | true => exact False.elim (all found)
    rcases delimitedNoTrailing_ordinary .leftParen .rightParen false
        (identifier .exportDecl) .exportDecl .topLevel
        (identifier_elementTotalityContract .exportDecl) input inputValid with
      ⟨values, afterValues, valuesResult⟩ |
      ⟨failure, rejected, valuesResult⟩
    · rcases requireConstructorNames_ok_of_delimitedNoTrailing_false_ok
        valuesResult with ⟨constructors, constructorsResult⟩
      exact Or.inl ⟨{
          span := values.span
          value := .named constructors
        }, afterValues, by
          simp only [constructorSelection, getState, bind, named,
            Bool.false_eq_true, ↓reduceIte, valuesResult, constructorsResult,
            pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [constructorSelection, getState, bind, named,
          Bool.false_eq_true, ↓reduceIte, valuesResult]⟩

theorem constructorSelection_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ selection next, constructorSelection input = .ok selection next) ∨
    (∃ failure next, constructorSelection input = .reject failure next) :=
  constructorSelection_invariantFreeOnValid input inputValid

theorem constructorSelection_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    constructorSelection input ≠ .invariant error :=
  constructorSelection_invariantFreeOnValid.ne_invariant
    input inputValid error

end Solcore.Syntax.Parser.ExportInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExportNameTotalityProperties
/-! Conditional totality for one exported selector name. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem operatorSelector_value_operator_onSuccess
    (context : ParseContext) {input next : State} {selected : SelectorName}
    (parsed : operatorSelector context input = .ok selected next) :
    ∃ spelling, selected.value = .operator spelling := by
  unfold operatorSelector at parsed
  cases openingResult : symbol .leftParen context input with
  | invariant error => simp [openingResult] at parsed
  | reject failure rejected => simp [openingResult] at parsed
  | ok opening afterOpening =>
      simp only [openingResult] at parsed
      cases partsResult : OperatorInternals.operatorParts context
          (afterOpening.remainingCount + 1) [] afterOpening with
      | invariant error => simp [partsResult] at parsed
      | reject failure rejected => simp [partsResult] at parsed
      | ok parts afterParts =>
          simp only [partsResult] at parsed
          cases closingResult : symbol .rightParen context afterParts with
          | invariant error => simp [closingResult] at parsed
          | reject failure rejected => simp [closingResult] at parsed
          | ok closing final =>
              simp only [closingResult] at parsed
              cases parsed
              exact ⟨String.join parts, rfl⟩

namespace ExportInternals

/--
Export-name dispatch is invariant-free once constructor selections are. The
operator branch cannot reach its defensive identifier/no-progress case because
`operatorSelector` success always constructs an operator selector.
-/
theorem exportName_invariantFreeOnValid
    (constructorSelectionFree :
      Parser.InvariantFreeOnValid constructorSelection) :
    Parser.InvariantFreeOnValid exportName := by
  intro input inputValid
  unfold exportName
  split
  · rcases (symbol_ordinary .star .exportDecl) input with
      ⟨marker, next, markerResult⟩ | ⟨failure, rejected, markerResult⟩
    · exact Or.inl ⟨{
          span := marker.span
          value := .wildcard marker.span
        }, next, by simp only [markerResult]⟩
    · exact Or.inr ⟨failure, rejected, by simp only [markerResult]⟩
  · split
    · rcases (operatorSelector_ordinary .exportDecl) input with
        ⟨selected, next, selectedResult⟩ |
        ⟨failure, rejected, selectedResult⟩
      · rcases operatorSelector_value_operator_onSuccess .exportDecl
          selectedResult with ⟨spelling, selectedShape⟩
        exact Or.inl ⟨{
            span := selected.span
            value := .operator { span := selected.span, value := spelling }
          }, next, by simp only [selectedResult, selectedShape]⟩
      · exact Or.inr ⟨failure, rejected, by simp only [selectedResult]⟩
    · rcases (identifier_ordinary .exportDecl) input with
        ⟨name, afterName, nameResult⟩ |
        ⟨failure, rejected, nameResult⟩
      · have nameValid := identifier_validFor .exportDecl input inputValid
        rw [nameResult] at nameValid
        by_cases present : isSymbol afterName .leftParen
        · rcases constructorSelectionFree afterName nameValid.2.1 with
            ⟨constructors, next, constructorsResult⟩ |
            ⟨failure, rejected, constructorsResult⟩
          · exact Or.inl ⟨{
                span := SourceSpan.cover name.span constructors.span
                value := .identifier name (some constructors)
              }, next, by
                simp only [nameResult, present, if_true, constructorsResult]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [nameResult, present, if_true, constructorsResult]⟩
        · exact Or.inl ⟨{
              span := name.span
              value := .identifier name none
            }, afterName, by
              have absent : isSymbol afterName .leftParen = false := by
                cases found : isSymbol afterName .leftParen with
                | false => rfl
                | true => exact False.elim (present found)
              simp only [nameResult, absent, Bool.false_eq_true, if_false]⟩
      · exact Or.inr ⟨failure, rejected, by simp only [nameResult]⟩

theorem exportName_ordinary
    (constructorSelectionFree :
      Parser.InvariantFreeOnValid constructorSelection)
    (input : State) (inputValid : input.ValidFor) :
    (∃ name next, exportName input = .ok name next) ∨
      (∃ failure next, exportName input = .reject failure next) :=
  exportName_invariantFreeOnValid constructorSelectionFree input inputValid

theorem exportName_ne_invariant
    (constructorSelectionFree :
      Parser.InvariantFreeOnValid constructorSelection)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    exportName input ≠ .invariant error :=
  (exportName_invariantFreeOnValid constructorSelectionFree).ne_invariant
    input inputValid error

/-- Every successful export name consumes its leading marker or identifier. -/
theorem exportName_cursor_lt_onSuccess {input next : State}
    {exported : ExportName}
    (parsed : exportName input = .ok exported next) :
    input.cursor < next.cursor := by
  unfold exportName at parsed
  split at parsed
  · cases markerResult : symbol .star .exportDecl input with
    | invariant error => simp [markerResult] at parsed
    | reject failure rejected => simp [markerResult] at parsed
    | ok marker afterMarker =>
        simp only [markerResult] at parsed
        cases parsed
        exact acceptToken_cursor_lt_onSuccess (.symbol .star) .exportDecl
          (· == .symbol .star) markerResult
  · split at parsed
    · cases selectedResult : operatorSelector .exportDecl input with
      | invariant error => simp [selectedResult] at parsed
      | reject failure rejected => simp [selectedResult] at parsed
      | ok selected afterSelected =>
          simp only [selectedResult] at parsed
          cases selectedValue : selected.value with
          | identifier name => simp [selectedValue] at parsed
          | operator spelling =>
              simp only [selectedValue] at parsed
              cases parsed
              exact operatorSelector_cursor_lt_onSuccess .exportDecl
                selectedResult
    · cases nameResult : identifier .exportDecl input with
      | invariant error => simp [nameResult] at parsed
      | reject failure rejected => simp [nameResult] at parsed
      | ok name afterName =>
          simp only [nameResult] at parsed
          have nameProgress : input.cursor < afterName.cursor := by
            rw [(identifier_ok_state_shape .exportDecl
              nameResult).choose_spec.2.2.2]
            simp
          split at parsed
          · cases constructorsResult : constructorSelection afterName with
            | invariant error => simp [constructorsResult] at parsed
            | reject failure rejected => simp [constructorsResult] at parsed
            | ok constructors afterConstructors =>
                simp only [constructorsResult] at parsed
                cases parsed
                exact Nat.lt_of_lt_of_le nameProgress
                  (constructorSelection_cursorMonotoneOnSuccess afterName
                    constructors next constructorsResult)
          · cases parsed
            exact nameProgress

/-- Conditional export-name totality instantiates the generic element API. -/
theorem exportName_elementTotalityContract
    (constructorSelectionFree :
      Parser.InvariantFreeOnValid constructorSelection) :
    ElementTotalityContract exportName := {
  validFor := exportName_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := exportName_preservesTokenWindow
  cursorLtOnSuccess := exportName_cursor_lt_onSuccess
  invariantFree := fun input inputValid error =>
    exportName_ne_invariant constructorSelectionFree input inputValid error
}

end ExportInternals

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExportPathTotalityProperties
/-! Production-fuel adequacy for export-path parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ExportInternals

/-- More fuel than remaining tokens makes the export-path tail ordinary. -/
theorem exportPathTail_ordinary_of_remainingCount_lt (first : Identifier) :
    ∀ fuel last tailRev state, state.remainingCount < fuel →
      (∃ path next,
        exportPathTail first fuel last tailRev state = .ok path next) ∨
      (∃ failure next,
        exportPathTail first fuel last tailRev state = .reject failure next) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev state adequate
      omega
  | succ fuel inductionHypothesis =>
      intro last tailRev state adequate
      unfold exportPathTail
      split
      · cases dotResult : symbol .dot .exportDecl state with
        | invariant error =>
            exact False.elim
              (symbol_ne_invariant .dot .exportDecl state error dotResult)
        | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
        | ok dot afterDot =>
            dsimp only
            cases componentResult : identifier .exportDecl afterDot with
            | invariant error =>
                exact False.elim
                  (identifier_ne_invariant .exportDecl afterDot error
                    componentResult)
            | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
            | ok component next =>
                change
                  (∃ path final,
                    exportPathTail first fuel component
                      (component :: tailRev) next = .ok path final) ∨
                  (∃ failure final,
                    exportPathTail first fuel component
                      (component :: tailRev) next = .reject failure final)
                apply inductionHypothesis component (component :: tailRev) next
                have dotShape := symbol_ok_state_shape .dot .exportDecl dotResult
                rcases identifier_ok_state_shape .exportDecl componentResult with
                  ⟨_, _, _, _, componentCursor⟩
                have dotWindow := symbol_preservesTokenWindow .dot .exportDecl
                  state
                rw [dotResult] at dotWindow
                have componentWindow := identifier_preservesTokenWindow
                  .exportDecl afterDot
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

theorem exportPathTail_ne_invariant_of_remainingCount_lt
    (first last : Identifier) (fuel : Nat) (tailRev : List Identifier)
    (state : State) (adequate : state.remainingCount < fuel)
    (error : ParserInvariantError) :
    exportPathTail first fuel last tailRev state ≠ .invariant error := by
  intro failed
  rcases exportPathTail_ordinary_of_remainingCount_lt first fuel last tailRev
      state adequate with
    ⟨path, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- The production choice `remainingCount + 1` is adequate. -/
theorem exportPathTail_production_ordinary (first last : Identifier)
    (tailRev : List Identifier) (state : State) :
    (∃ path next,
      exportPathTail first (state.remainingCount + 1) last tailRev state =
        .ok path next) ∨
    (∃ failure next,
      exportPathTail first (state.remainingCount + 1) last tailRev state =
        .reject failure next) :=
  exportPathTail_ordinary_of_remainingCount_lt first
    (state.remainingCount + 1) last tailRev state (by omega)

/-- Public export paths are ordinary on every input. -/
theorem exportPath_ordinary : Parser.Ordinary exportPath := by
  intro input
  unfold exportPath
  cases firstResult : identifier .exportDecl input with
  | invariant error =>
      exact False.elim
        (identifier_ne_invariant .exportDecl input error firstResult)
  | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
  | ok first next =>
      dsimp only
      exact exportPathTail_production_ordinary first first [] next

theorem exportPath_invariantFreeOnValid :
    Parser.InvariantFreeOnValid exportPath :=
  exportPath_ordinary.invariantFreeOnValid

theorem exportPath_ne_invariant (input : State)
    (error : ParserInvariantError) :
    exportPath input ≠ .invariant error :=
  exportPath_ordinary.ne_invariant input error

end ExportInternals

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExportTotalityProperties
/-! Totality boundary for local, path, and public export dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/--
The two leaf obligations below are exactly the export-specific work still below
public dispatch: export-name defenses and delimited item progress.
-/
structure ExportLeafTotalityContract : Prop where
  exportSelectionFree :
    Parser.InvariantFreeOnValid ExportInternals.exportSelection
  localExportItem : ElementTotalityContract ExportInternals.localExportItem

namespace ExportInternals

theorem finishExport_invariantFreeOnValid (start : SourceSpan)
    (value : ExportDeclValue) :
    Parser.InvariantFreeOnValid (finishExport start value) := by
  unfold finishExport
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .semicolon .exportDecl)
    (symbol_ordinary .semicolon .exportDecl).invariantFreeOnValid
  intro semicolon
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover start semicolon.span
    value
  } : ExportDecl)

theorem finishExport_ne_invariant (start : SourceSpan)
    (value : ExportDeclValue) (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    finishExport start value input ≠ .invariant error :=
  (finishExport_invariantFreeOnValid start value).ne_invariant
    input inputValid error

theorem localExport_invariantFreeOnValid (contract : ExportLeafTotalityContract)
    (start : SourceSpan) :
    Parser.InvariantFreeOnValid (localExport start) := by
  unfold localExport
  apply Parser.bind_invariantFreeOnValid
    (delimited_validFor LocalExportItem.ValidFor .leftBrace .rightBrace true
      localExportItem .exportDecl .topLevel localExportItem_validFor
      localExportItem_preservesTokensOnSuccess)
  · exact Parser.invariantFreeOnValid_of_ne_invariant
      (delimited_ne_invariant .leftBrace .rightBrace true localExportItem
        .exportDecl .topLevel contract.localExportItem)
  · intro items
    exact finishExport_invariantFreeOnValid start (.local items)

theorem localExport_ordinary (contract : ExportLeafTotalityContract)
    (start : SourceSpan) (input : State) (inputValid : input.ValidFor) :
    (∃ value next, localExport start input = .ok value next) ∨
    (∃ failure next, localExport start input = .reject failure next) :=
  localExport_invariantFreeOnValid contract start input inputValid

theorem localExport_ne_invariant (contract : ExportLeafTotalityContract)
    (start : SourceSpan) (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    localExport start input ≠ .invariant error :=
  (localExport_invariantFreeOnValid contract start).ne_invariant
    input inputValid error

theorem pathExport_invariantFreeOnValid (contract : ExportLeafTotalityContract)
    (start : SourceSpan) :
    Parser.InvariantFreeOnValid (pathExport start) := by
  unfold pathExport
  apply Parser.bind_invariantFreeOnValid exportPath_validFor
    exportPath_invariantFreeOnValid
  intro path
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro state
  by_cases dotted : isSymbol state .dot
  · simp only [dotted, if_true]
    apply Parser.bind_invariantFreeOnValid
      (symbol_validFor .dot .exportDecl)
      (symbol_ordinary .dot .exportDecl).invariantFreeOnValid
    intro dot
    apply Parser.bind_invariantFreeOnValid exportSelection_validFor
      contract.exportSelectionFree
    intro selection
    exact finishExport_invariantFreeOnValid start (.itemsFrom path selection)
  · simp only [dotted]
    by_cases aliased : isKeyword state .asKw
    · simp only [aliased, if_true]
      apply Parser.bind_invariantFreeOnValid
        (keyword_validFor .asKw .exportDecl)
        (keyword_ordinary .asKw .exportDecl).invariantFreeOnValid
      intro asKeyword
      apply Parser.bind_invariantFreeOnValid
        (identifier_validFor .exportDecl)
        (identifier_ordinary .exportDecl).invariantFreeOnValid
      intro alias
      exact finishExport_invariantFreeOnValid start (.moduleAs path alias)
    · simp only [aliased]
      exact finishExport_invariantFreeOnValid start (.module path)

theorem pathExport_ordinary (contract : ExportLeafTotalityContract)
    (start : SourceSpan) (input : State) (inputValid : input.ValidFor) :
    (∃ value next, pathExport start input = .ok value next) ∨
    (∃ failure next, pathExport start input = .reject failure next) :=
  pathExport_invariantFreeOnValid contract start input inputValid

theorem pathExport_ne_invariant (contract : ExportLeafTotalityContract)
    (start : SourceSpan) (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    pathExport start input ≠ .invariant error :=
  (pathExport_invariantFreeOnValid contract start).ne_invariant
    input inputValid error

end ExportInternals

theorem exportDecl_invariantFreeOnValid_of_leafContract
    (contract : ExportLeafTotalityContract) :
    Parser.InvariantFreeOnValid exportDecl := by
  unfold exportDecl
  apply Parser.bind_invariantFreeOnValid
    (keyword_validFor .exportKw .exportDecl)
    (keyword_ordinary .exportKw .exportDecl).invariantFreeOnValid
  intro exportKeyword
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro state
  by_cases isLocal : isSymbol state .leftBrace
  · simp only [isLocal, if_true]
    exact ExportInternals.localExport_invariantFreeOnValid contract
      exportKeyword.span
  · simp only [isLocal]
    exact ExportInternals.pathExport_invariantFreeOnValid contract
      exportKeyword.span

theorem exportDecl_ordinary_of_leafContract (contract : ExportLeafTotalityContract)
    (input : State) (inputValid : input.ValidFor) :
    (∃ value next, exportDecl input = .ok value next) ∨
    (∃ failure next, exportDecl input = .reject failure next) :=
  exportDecl_invariantFreeOnValid_of_leafContract contract input inputValid

theorem exportDecl_ne_invariant_of_leafContract
    (contract : ExportLeafTotalityContract)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    exportDecl input ≠ .invariant error :=
  (exportDecl_invariantFreeOnValid_of_leafContract contract).ne_invariant
    input inputValid error

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExportSelectionItemTotalityProperties
/-! Export selection and local-item totality from an export-name contract. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ExportInternals

theorem exportSelection_invariantFreeOnValid
    (nameContract : ElementTotalityContract exportName) :
    Parser.InvariantFreeOnValid exportSelection := by
  intro input inputValid
  by_cases wildcard : isSymbol input .star
  · rcases (symbol_ordinary .star .exportDecl) input with
      ⟨marker, next, result⟩ | ⟨failure, rejected, result⟩
    · exact Or.inl ⟨{ span := marker.span, value := .wildcard marker.span },
        next, by simp [exportSelection, wildcard, result]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp [exportSelection, wildcard, result]⟩
  · rcases delimited_ordinary .leftBrace .rightBrace true exportName
        .exportDecl .topLevel nameContract input inputValid with
      ⟨items, next, result⟩ | ⟨failure, rejected, result⟩
    · exact Or.inl ⟨{ span := items.span, value := .selected items }, next, by
        simp [exportSelection, wildcard, result]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp [exportSelection, wildcard, result]⟩

theorem exportSelection_ordinary
    (nameContract : ElementTotalityContract exportName)
    (input : State) (inputValid : input.ValidFor) :
    (∃ selection next, exportSelection input = .ok selection next) ∨
    (∃ failure next, exportSelection input = .reject failure next) :=
  exportSelection_invariantFreeOnValid nameContract input inputValid

theorem exportSelection_ne_invariant
    (nameContract : ElementTotalityContract exportName)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    exportSelection input ≠ .invariant error :=
  (exportSelection_invariantFreeOnValid nameContract).ne_invariant
    input inputValid error

theorem localExportItem_invariantFreeOnValid
    (nameContract : ElementTotalityContract exportName) :
    Parser.InvariantFreeOnValid localExportItem := by
  intro input inputValid
  by_cases qualified : isIdentifier input &&
      isSymbol { input with cursor := input.cursor + 1 } .dot
  · rcases exportPath_ordinary input with
      ⟨path, afterPath, pathResult⟩ |
      ⟨failure, rejected, pathResult⟩
    · have pathValid := exportPath_validFor input inputValid
      rw [pathResult] at pathValid
      rcases (symbol_ordinary .dot .exportDecl) afterPath with
        ⟨dot, afterDot, dotResult⟩ | ⟨failure, rejected, dotResult⟩
      · have dotValid := symbol_validFor .dot .exportDecl afterPath pathValid.2.1
        rw [dotResult] at dotValid
        rcases (symbol_ordinary .star .exportDecl) afterDot with
          ⟨marker, next, markerResult⟩ |
          ⟨failure, rejected, markerResult⟩
        · exact Or.inl ⟨{
              span := SourceSpan.cover path.span marker.span
              value := .moduleWildcard path marker.span
            }, next, by
              simp [localExportItem, qualified, pathResult, dotResult,
                markerResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp [localExportItem, qualified, pathResult, dotResult,
              markerResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp [localExportItem, qualified, pathResult, dotResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp [localExportItem, qualified, pathResult]⟩
  · have nameFree := Parser.invariantFreeOnValid_of_ne_invariant
      nameContract.invariantFree
    rcases nameFree input inputValid with
      ⟨name, next, nameResult⟩ | ⟨failure, rejected, nameResult⟩
    · exact Or.inl ⟨{ span := name.span, value := .name name }, next, by
        simp [localExportItem, qualified, nameResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp [localExportItem, qualified, nameResult]⟩

theorem localExportItem_ordinary
    (nameContract : ElementTotalityContract exportName)
    (input : State) (inputValid : input.ValidFor) :
    (∃ item next, localExportItem input = .ok item next) ∨
    (∃ failure next, localExportItem input = .reject failure next) :=
  localExportItem_invariantFreeOnValid nameContract input inputValid

theorem localExportItem_ne_invariant
    (nameContract : ElementTotalityContract exportName)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    localExportItem input ≠ .invariant error :=
  (localExportItem_invariantFreeOnValid nameContract).ne_invariant
    input inputValid error

theorem localExportItem_cursor_lt_onSuccess
    (nameContract : ElementTotalityContract exportName)
    {input next : State} {item : LocalExportItem}
    (result : localExportItem input = .ok item next) :
    input.cursor < next.cursor := by
  unfold localExportItem at result
  split at result
  · cases pathResult : exportPath input with
    | reject failure rejected => simp [pathResult] at result
    | invariant error => simp [pathResult] at result
    | ok path afterPath =>
        simp only [pathResult] at result
        cases dotResult : symbol .dot .exportDecl afterPath with
        | reject failure rejected => simp [dotResult] at result
        | invariant error => simp [dotResult] at result
        | ok dot afterDot =>
            simp only [dotResult] at result
            cases markerResult : symbol .star .exportDecl afterDot with
            | reject failure rejected => simp [markerResult] at result
            | invariant error => simp [markerResult] at result
            | ok marker final =>
                simp only [markerResult] at result
                have strict := Nat.lt_of_le_of_lt
                  (exportPath_cursorMonotoneOnSuccess input path afterPath
                    pathResult)
                  (Nat.lt_of_lt_of_le
                    (acceptToken_cursor_lt_onSuccess (.symbol .dot) .exportDecl
                      (· == .symbol .dot) dotResult)
                    (symbol_cursorMonotoneOnSuccess .star .exportDecl afterDot
                      marker final markerResult))
                cases result
                exact strict
  · cases nameResult : exportName input with
    | reject failure rejected => simp [nameResult] at result
    | invariant error => simp [nameResult] at result
    | ok name final =>
        simp only [nameResult] at result
        have strict := nameContract.cursorLtOnSuccess nameResult
        cases result
        exact strict

theorem localExportItem_elementTotalityContract
    (nameContract : ElementTotalityContract exportName) :
    ElementTotalityContract localExportItem := {
  validFor := localExportItem_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := localExportItem_preservesTokenWindow
  cursorLtOnSuccess := localExportItem_cursor_lt_onSuccess nameContract
  invariantFree := fun input inputValid error =>
    localExportItem_ne_invariant nameContract input inputValid error
}

end ExportInternals

theorem exportLeafTotalityContract
    (nameContract : ElementTotalityContract ExportInternals.exportName) :
    ExportLeafTotalityContract := {
  exportSelectionFree :=
    ExportInternals.exportSelection_invariantFreeOnValid nameContract
  localExportItem :=
    ExportInternals.localExportItem_elementTotalityContract nameContract
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExportCanonicalTotalityProperties
/-! Unconditional valid-input totality for canonical export declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem exportDecl_invariantFreeOnValid :
    Parser.InvariantFreeOnValid exportDecl := by
  let nameContract := ExportInternals.exportName_elementTotalityContract
    ExportInternals.constructorSelection_invariantFreeOnValid
  exact exportDecl_invariantFreeOnValid_of_leafContract
    (exportLeafTotalityContract nameContract)

theorem exportDecl_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ value next, exportDecl input = .ok value next) ∨
    (∃ failure next, exportDecl input = .reject failure next) :=
  exportDecl_invariantFreeOnValid input inputValid

theorem exportDecl_ne_invariant (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    exportDecl input ≠ .invariant error :=
  exportDecl_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ImportSelectionTotalityProperties
/-! Totality for selected-import and hiding-clause parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem pure_ordinary {alpha : Type} (value : alpha) :
    Parser.Ordinary (pure value : Parser alpha) :=
  fun input => Or.inl ⟨value, input, rfl⟩

private theorem getState_ordinary : Parser.Ordinary getState :=
  fun input => Or.inl ⟨input, input, rfl⟩

private theorem bind_ordinary {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    (firstOrdinary : Parser.Ordinary first)
    (nextOrdinary : ∀ value, Parser.Ordinary (next value)) :
    Parser.Ordinary (first >>= next) := by
  intro input
  rcases firstOrdinary input with
    ⟨firstValue, afterFirst, firstResult⟩ |
    ⟨failure, rejected, firstResult⟩
  · rcases nextOrdinary firstValue afterFirst with
      ⟨value, final, nextResult⟩ | ⟨failure, final, nextResult⟩
    · exact Or.inl ⟨value, final, by
        simp only [bind, firstResult, nextResult]⟩
    · exact Or.inr ⟨failure, final, by
        simp only [bind, firstResult, nextResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [bind, firstResult]⟩

/-- Optional selected-import aliases are ordinary on every input. -/
theorem selectedAlias_ordinary :
    Parser.Ordinary ImportInternals.selectedAlias := by
  unfold ImportInternals.selectedAlias
  apply bind_ordinary getState_ordinary
  intro observed
  by_cases present : isKeyword observed .asKw = true
  · simp only [present, if_true]
    apply bind_ordinary (keyword_ordinary .asKw .importDecl)
    intro marker
    apply bind_ordinary (identifier_ordinary .importDecl)
    intro name
    exact pure_ordinary (some name)
  · simp only [present, Bool.false_eq_true, if_false]
    exact pure_ordinary none

theorem selectedAlias_ne_invariant (input : State)
    (error : ParserInvariantError) :
    ImportInternals.selectedAlias input ≠ .invariant error :=
  selectedAlias_ordinary.ne_invariant input error

/-- One selected import is ordinary on every input. -/
theorem selectedImport_ordinary : Parser.Ordinary selectedImport := by
  unfold selectedImport
  apply bind_ordinary (selectorName_ordinary .importDecl)
  intro source
  apply bind_ordinary selectedAlias_ordinary
  intro alias
  exact pure_ordinary _

theorem selectedImport_ne_invariant (input : State)
    (error : ParserInvariantError) :
    selectedImport input ≠ .invariant error :=
  selectedImport_ordinary.ne_invariant input error

/-- A selected import strictly consumes its leading selector. -/
theorem selectedImport_cursor_lt_onSuccess {input next : State}
    {selection : SelectedImport}
    (parsed : selectedImport input = .ok selection next) :
    input.cursor < next.cursor := by
  unfold selectedImport at parsed
  cases sourceResult : selectorName .importDecl input with
  | invariant error =>
      simp only [bind, sourceResult] at parsed
      contradiction
  | reject failure rejected =>
      simp only [bind, sourceResult] at parsed
      contradiction
  | ok source afterSource =>
      simp only [sourceResult, bind] at parsed
      cases aliasResult : ImportInternals.selectedAlias afterSource with
      | invariant error => simp [aliasResult] at parsed
      | reject failure rejected => simp [aliasResult] at parsed
      | ok alias afterAlias =>
          simp only [aliasResult, pure] at parsed
          cases parsed
          exact Nat.lt_of_lt_of_le
            (selectorName_cursor_lt_onSuccess .importDecl sourceResult)
            (selectedAlias_cursorMonotoneOnSuccess afterSource alias next
              aliasResult)

/-- Selected imports instantiate the generic delimited-element boundary. -/
theorem selectedImport_elementTotalityContract :
    ElementTotalityContract selectedImport := {
  validFor := selectedImport_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := selectedImport_preservesTokenWindow
  cursorLtOnSuccess := selectedImport_cursor_lt_onSuccess
  invariantFree := fun input _inputValid error =>
    selectedImport_ne_invariant input error
}

namespace ImportInternals

/-- A successful nonempty selected list makes `requireSelected` ordinary. -/
theorem requireSelected_ordinary_of_delimited_success
    {input afterValues : State} {values : DelimitedList SelectedImport}
    (parsed : delimited .leftBrace .rightBrace false selectedImport
      .importDecl .topLevel input = .ok values afterValues) :
    Parser.Ordinary (requireSelected values) := by
  have nonempty := delimited_false_elements_ne_nil_onSuccess
    .leftBrace .rightBrace selectedImport .importDecl .topLevel parsed
  unfold requireSelected
  cases elements : values.elements with
  | nil => exact False.elim (nonempty elements)
  | cons head tail => exact pure_ordinary _

theorem requireSelected_ne_invariant_of_delimited_success
    {input afterValues : State} {values : DelimitedList SelectedImport}
    (parsed : delimited .leftBrace .rightBrace false selectedImport
      .importDecl .topLevel input = .ok values afterValues)
    (state : State) (error : ParserInvariantError) :
    requireSelected values state ≠ .invariant error :=
  (requireSelected_ordinary_of_delimited_success parsed).ne_invariant
    state error

/-- A successful nonempty hiding list makes its shape check ordinary. -/
theorem requireSelectorNames_ordinary_of_delimited_success
    {input afterValues : State} {values : DelimitedList SelectorName}
    (parsed : delimited .leftBrace .rightBrace false
      (selectorName .importDecl) .importDecl .topLevel input =
        .ok values afterValues) :
    Parser.Ordinary (requireSelectorNames values) := by
  have nonempty := delimited_false_elements_ne_nil_onSuccess
    .leftBrace .rightBrace (selectorName .importDecl) .importDecl .topLevel
    parsed
  unfold requireSelectorNames
  cases elements : values.elements with
  | nil => exact False.elim (nonempty elements)
  | cons head tail => exact pure_ordinary _

theorem requireSelectorNames_ne_invariant_of_delimited_success
    {input afterValues : State} {values : DelimitedList SelectorName}
    (parsed : delimited .leftBrace .rightBrace false
      (selectorName .importDecl) .importDecl .topLevel input =
        .ok values afterValues)
    (state : State) (error : ParserInvariantError) :
    requireSelectorNames values state ≠ .invariant error :=
  (requireSelectorNames_ordinary_of_delimited_success parsed).ne_invariant
    state error

/-- Selected-import lists have only ordinary replies on valid input. -/
theorem selectedImports_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ selection next, selectedImports input = .ok selection next) ∨
      (∃ failure next, selectedImports input = .reject failure next) := by
  rcases delimited_ordinary .leftBrace .rightBrace false selectedImport
      .importDecl .topLevel selectedImport_elementTotalityContract input
      inputValid with
    ⟨values, afterValues, valuesResult⟩ |
    ⟨failure, rejected, valuesResult⟩
  · rcases requireSelected_ordinary_of_delimited_success valuesResult
      afterValues with
      ⟨selection, next, selectionResult⟩ |
      ⟨failure, rejected, selectionResult⟩
    · exact Or.inl ⟨selection, next, by
        unfold selectedImports
        simp only [bind, valuesResult, selectionResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        unfold selectedImports
        simp only [bind, valuesResult, selectionResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      unfold selectedImports
      simp only [bind, valuesResult]⟩

theorem selectedImports_invariantFreeOnValid :
    Parser.InvariantFreeOnValid selectedImports :=
  selectedImports_ordinary

theorem selectedImports_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    selectedImports input ≠ .invariant error :=
  selectedImports_invariantFreeOnValid.ne_invariant input inputValid error

/-- Hiding clauses have only ordinary replies on valid input. -/
theorem hidingClause_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ clause next, hidingClause input = .ok clause next) ∨
      (∃ failure next, hidingClause input = .reject failure next) := by
  rcases (contextual_ordinary .hiding .importDecl) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := contextual_validFor .hiding .importDecl
      input inputValid
    rw [markerResult] at markerReply
    rcases delimited_ordinary .leftBrace .rightBrace false
        (selectorName .importDecl) .importDecl .topLevel
        (selectorName_elementTotalityContract .importDecl) afterMarker
        markerReply.2.1 with
      ⟨values, afterValues, valuesResult⟩ |
      ⟨failure, rejected, valuesResult⟩
    · rcases requireSelectorNames_ordinary_of_delimited_success valuesResult
        afterValues with
        ⟨names, afterNames, namesResult⟩ |
        ⟨failure, rejected, namesResult⟩
      · refine Or.inl ⟨{
            span := SourceSpan.cover marker.span values.span
            value := { names }
          }, afterNames, ?_⟩
        unfold hidingClause
        simp only [bind, markerResult, valuesResult, namesResult, pure]
      · exact Or.inr ⟨failure, rejected, by
          unfold hidingClause
          simp only [bind, markerResult, valuesResult, namesResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        unfold hidingClause
        simp only [bind, markerResult, valuesResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      unfold hidingClause
      simp only [bind, markerResult]⟩

theorem hidingClause_invariantFreeOnValid :
    Parser.InvariantFreeOnValid hidingClause :=
  hidingClause_ordinary

theorem hidingClause_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    hidingClause input ≠ .invariant error :=
  hidingClause_invariantFreeOnValid.ne_invariant input inputValid error

/-- Optional hiding dispatch has only ordinary replies on valid input. -/
theorem optionalHiding_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ clause next, optionalHiding input = .ok clause next) ∨
      (∃ failure next, optionalHiding input = .reject failure next) := by
  unfold optionalHiding
  simp only [getState, bind]
  split
  · rcases hidingClause_ordinary input inputValid with
      ⟨clause, next, result⟩ | ⟨failure, rejected, result⟩
    · exact Or.inl ⟨some clause, next, by simp only [result, pure]⟩
    · exact Or.inr ⟨failure, rejected, by simp only [result]⟩
  · exact Or.inl ⟨none, input, rfl⟩

theorem optionalHiding_invariantFreeOnValid :
    Parser.InvariantFreeOnValid optionalHiding :=
  optionalHiding_ordinary

theorem optionalHiding_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    optionalHiding input ≠ .invariant error :=
  optionalHiding_invariantFreeOnValid.ne_invariant input inputValid error

end ImportInternals

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ImportBaseTotalityProperties
/-! Totality laws for import terminators and the two basic import forms. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem pure_ordinary_variant {α : Type} (value : α) :
    Parser.Ordinary (pure value : Parser α) := by
  intro input
  exact Or.inl ⟨value, input, rfl⟩

private theorem bind_ordinary_variant {α β : Type} {first : Parser α}
    {next : α → Parser β} (firstOrdinary : Parser.Ordinary first)
    (nextOrdinary : ∀ value, Parser.Ordinary (next value)) :
    Parser.Ordinary (first >>= next) := by
  intro input
  rcases firstOrdinary input with
    ⟨value, middle, firstResult⟩ | ⟨failure, rejected, firstResult⟩
  · rcases nextOrdinary value middle with
      ⟨result, final, nextResult⟩ | ⟨failure, rejected, nextResult⟩
    · exact Or.inl ⟨result, final, by
        simp only [bind, firstResult, nextResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [bind, firstResult, nextResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [bind, firstResult]⟩

namespace ImportInternals

/-- An import terminator always succeeds or reports a source rejection. -/
theorem terminator_ordinary (lastSpan : SourceSpan) :
    Parser.Ordinary (terminator lastSpan) := by
  intro input
  unfold terminator
  split
  · rcases symbol_ordinary .semicolon .importDecl input with
      ⟨token, next, result⟩ | ⟨failure, rejected, result⟩
    · exact Or.inl ⟨token.span, next, by simp only [result]⟩
    · exact Or.inr ⟨failure, rejected, by simp only [result]⟩
  · split
    · exact Or.inl ⟨lastSpan, input.emit {
          span := input.currentSpan
          kind := .constraintViolation
            (.trailingSemicolonRequired .importDecl)
        }, rfl⟩
    · exact Or.inr ⟨_, input, rfl⟩

/-- Import terminators cannot expose an internal parser invariant. -/
theorem terminator_ne_invariant (lastSpan : SourceSpan) (input : State)
    (error : ParserInvariantError) :
    terminator lastSpan input ≠ .invariant error :=
  (terminator_ordinary lastSpan).ne_invariant input error

/-- Finishing an already parsed import payload is ordinary on every input. -/
theorem finish_ordinary (start last : SourceSpan) (value : ImportDeclValue) :
    Parser.Ordinary (finish start last value) := by
  unfold finish
  exact bind_ordinary_variant (terminator_ordinary last) (fun endSpan =>
    pure_ordinary_variant ({
      span := SourceSpan.cover start endSpan
      value
    } : ImportDecl))

/-- Import finishing cannot introduce an internal invariant. -/
theorem finish_ne_invariant (start last : SourceSpan)
    (value : ImportDeclValue) (input : State)
    (error : ParserInvariantError) :
    finish start last value input ≠ .invariant error :=
  (finish_ordinary start last value).ne_invariant input error

/-- Plain module imports are ordinary on every input. -/
theorem plainImport_ordinary (start : SourceSpan) :
    Parser.Ordinary (plainImport start) := by
  unfold plainImport
  exact bind_ordinary_variant (modulePath_ordinary .importDecl) (fun path =>
    finish_ordinary start path.span (.plain path))

/-- Plain module imports cannot expose an internal invariant. -/
theorem plainImport_ne_invariant (start : SourceSpan) (input : State)
    (error : ParserInvariantError) :
    plainImport start input ≠ .invariant error :=
  (plainImport_ordinary start).ne_invariant input error

/-- Wildcard namespace-alias imports are ordinary on every input. -/
theorem namespaceImport_ordinary (start : SourceSpan) :
    Parser.Ordinary (namespaceImport start) := by
  unfold namespaceImport
  exact bind_ordinary_variant (symbol_ordinary .star .importDecl) (fun _ =>
    bind_ordinary_variant (keyword_ordinary .asKw .importDecl) (fun _ =>
      bind_ordinary_variant (identifier_ordinary .importDecl) (fun alias =>
        bind_ordinary_variant (contextual_ordinary .from .importDecl) (fun _ =>
          bind_ordinary_variant (modulePath_ordinary .importDecl) (fun path =>
            finish_ordinary start path.span (.namespace path alias))))))

/-- Namespace imports cannot expose an internal invariant. -/
theorem namespaceImport_ne_invariant (start : SourceSpan) (input : State)
    (error : ParserInvariantError) :
    namespaceImport start input ≠ .invariant error :=
  (namespaceImport_ordinary start).ne_invariant input error

end ImportInternals
end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ImportTotalityProperties
/-! Totality laws for complete canonical import declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ImportInternals

/-- Wildcard imports are invariant-free on every canonical valid input. -/
theorem wildcardImport_invariantFreeOnValid (start : SourceSpan) :
    Parser.InvariantFreeOnValid (wildcardImport start) := by
  unfold wildcardImport
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .star .importDecl)
    (symbol_ordinary .star .importDecl).invariantFreeOnValid
  intro _star
  apply Parser.bind_invariantFreeOnValid
    (contextual_validFor .from .importDecl)
    (contextual_ordinary .from .importDecl).invariantFreeOnValid
  intro _fromMarker
  apply Parser.bind_invariantFreeOnValid
    (modulePath_validFor .importDecl)
    (modulePath_ordinary .importDecl).invariantFreeOnValid
  intro path
  apply Parser.bind_invariantFreeOnValid optionalHiding_validFor
    optionalHiding_invariantFreeOnValid
  intro hidden
  exact (finish_ordinary start
    (match hidden with
      | some clause => clause.span
      | none => path.span)
    (.wildcard path hidden)).invariantFreeOnValid

/-- A wildcard import has an ordinary success or rejection on valid input. -/
theorem wildcardImport_ordinary (start : SourceSpan) (input : State)
    (inputValid : input.ValidFor) :
    (∃ value next, wildcardImport start input = .ok value next) ∨
      (∃ failure next, wildcardImport start input = .reject failure next) :=
  wildcardImport_invariantFreeOnValid start input inputValid

theorem wildcardImport_ne_invariant (start : SourceSpan) (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    wildcardImport start input ≠ .invariant error :=
  (wildcardImport_invariantFreeOnValid start).ne_invariant
    input inputValid error

/-- Selective imports are invariant-free on every canonical valid input. -/
theorem selectiveImport_invariantFreeOnValid (start : SourceSpan) :
    Parser.InvariantFreeOnValid (selectiveImport start) := by
  unfold selectiveImport
  apply Parser.bind_invariantFreeOnValid selectedImports_validFor
    selectedImports_invariantFreeOnValid
  intro _selection
  apply Parser.bind_invariantFreeOnValid
    (contextual_validFor .from .importDecl)
    (contextual_ordinary .from .importDecl).invariantFreeOnValid
  intro _fromMarker
  apply Parser.bind_invariantFreeOnValid
    (modulePath_validFor .importDecl)
    (modulePath_ordinary .importDecl).invariantFreeOnValid
  intro path
  apply Parser.bind_invariantFreeOnValid optionalHiding_validFor
    optionalHiding_invariantFreeOnValid
  intro hidden
  exact (finish_ordinary start
    (match hidden with
      | some clause => clause.span
      | none => path.span)
    (.selected _selection path hidden)).invariantFreeOnValid

/-- A selective import has an ordinary success or rejection on valid input. -/
theorem selectiveImport_ordinary (start : SourceSpan) (input : State)
    (inputValid : input.ValidFor) :
    (∃ value next, selectiveImport start input = .ok value next) ∨
      (∃ failure next, selectiveImport start input = .reject failure next) :=
  selectiveImport_invariantFreeOnValid start input inputValid

theorem selectiveImport_ne_invariant (start : SourceSpan) (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    selectiveImport start input ≠ .invariant error :=
  (selectiveImport_invariantFreeOnValid start).ne_invariant
    input inputValid error

end ImportInternals

/-- Complete import dispatch is invariant-free on canonical valid input. -/
theorem importDecl_invariantFreeOnValid :
    Parser.InvariantFreeOnValid importDecl := by
  unfold importDecl
  apply Parser.bind_invariantFreeOnValid
    (keyword_validFor .importKw .importDecl)
    (keyword_ordinary .importKw .importDecl).invariantFreeOnValid
  intro importKeyword
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro observed
  by_cases star : isSymbol observed .star
  · simp only [star, if_true]
    by_cases namespaceAlias :
        observed.peekOffsetKind? 1 == some (.keyword .asKw)
    · simp only [namespaceAlias, if_true]
      exact (ImportInternals.namespaceImport_ordinary
        importKeyword.span).invariantFreeOnValid
    · simp only [namespaceAlias, Bool.false_eq_true, if_false]
      exact ImportInternals.wildcardImport_invariantFreeOnValid
        importKeyword.span
  · simp only [star, Bool.false_eq_true, if_false]
    by_cases selected : isSymbol observed .leftBrace
    · simp only [selected, if_true]
      exact ImportInternals.selectiveImport_invariantFreeOnValid
        importKeyword.span
    · simp only [selected, Bool.false_eq_true, if_false]
      exact (ImportInternals.plainImport_ordinary
        importKeyword.span).invariantFreeOnValid

/-- Complete import parsing has an ordinary reply on valid input. -/
theorem importDecl_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ value next, importDecl input = .ok value next) ∨
      (∃ failure next, importDecl input = .reject failure next) :=
  importDecl_invariantFreeOnValid input inputValid

theorem importDecl_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    importDecl input ≠ .invariant error :=
  importDecl_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser
end
