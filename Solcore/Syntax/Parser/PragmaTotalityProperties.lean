import Solcore.Syntax.Parser.Pragma

/-! Fuel adequacy and ordinary-result classification for pragma parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem acceptToken_ordinary
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

private theorem keyword_ordinary (value : HardKeyword)
    (context : ParseContext) (state : State) :
    (∃ token final, keyword value context state = .ok token final) ∨
      (∃ failure final,
        keyword value context state = .reject failure final) :=
  acceptToken_ordinary (.keyword value) context
    (· == .keyword value) state

private theorem symbol_ordinary (value : Symbol)
    (context : ParseContext) (state : State) :
    (∃ token final, symbol value context state = .ok token final) ∨
      (∃ failure final,
        symbol value context state = .reject failure final) :=
  acceptToken_ordinary (.symbol value) context
    (· == .symbol value) state

private theorem rawIdentifier_ordinary (context : ParseContext)
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

private theorem identifier_ordinary (context : ParseContext)
    (state : State) :
    (∃ name final, identifier context state = .ok name final) ∨
      (∃ failure final,
        identifier context state = .reject failure final) := by
  unfold identifier
  rcases rawIdentifier_ordinary context state with
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
      · rcases symbol_ordinary .comma .pragmaDecl input with
          ⟨comma, afterComma, commaResult⟩ |
          ⟨failure, rejected, commaResult⟩
        · simp only [commaResult]
          split
          · exact Or.inl ⟨_, _, rfl⟩
          · rcases identifier_ordinary .pragmaDecl afterComma with
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
  · rcases identifier_ordinary .pragmaDecl state with
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
  rcases keyword_ordinary .pragmaKw .pragmaDecl state with
    ⟨pragmaKeyword, afterKeyword, keywordResult⟩ |
    ⟨failure, rejected, keywordResult⟩
  · simp only [keywordResult, bind]
    rcases rawIdentifier_ordinary .pragmaDecl afterKeyword with
      ⟨name, afterName, nameResult⟩ | ⟨failure, rejected, nameResult⟩
    · simp only [nameResult]
      rcases PragmaInternals.pragmaItems_ordinary afterName with
        ⟨items, afterItems, itemsResult⟩ |
        ⟨failure, rejected, itemsResult⟩
      · simp only [itemsResult]
        rcases symbol_ordinary .semicolon .pragmaDecl afterItems with
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
