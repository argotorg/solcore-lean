import Solcore.Syntax.Parser.Type

/-! Contracts for the named branch of the recursive type parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components {α β : Type} {first : Parser α}
    {next : α → Parser β} {input final : State} {value : β}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

private theorem requireNonempty_preservesTokensOnSuccess {α : Type}
    (parsed : DelimitedList α) (phase : ParserPhase) :
    Parser.PreservesTokensOnSuccess (requireNonempty parsed phase) := by
  intro input value next result
  unfold requireNonempty at result
  cases elements : parsed.elements with
  | nil => rw [elements] at result; contradiction
  | cons head tail => rw [elements] at result; cases result; rfl

private theorem requireNonempty_cursorMonotoneOnSuccess {α : Type}
    (parsed : DelimitedList α) (phase : ParserPhase) :
    Parser.CursorMonotoneOnSuccess (requireNonempty parsed phase) := by
  intro input value next result
  unfold requireNonempty at result
  cases elements : parsed.elements with
  | nil => rw [elements] at result; contradiction
  | cons head tail =>
      rw [elements] at result
      cases result
      exact Nat.le_refl _

private theorem requireNonempty_preservesTokenWindow {α : Type}
    (parsed : DelimitedList α) (phase : ParserPhase) :
    Parser.PreservesTokenWindow (requireNonempty parsed phase) := by
  intro input
  unfold requireNonempty
  cases parsed.elements with
  | nil => trivial
  | cons head tail => exact ⟨rfl, rfl⟩

/-- Optional named-type arguments preserve delimiter and element provenance. -/
theorem parseNamedTypeArguments_validFor (nested : Parser TypeExpr)
    (nestedValid : nested.ValidFor TypeExpr.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (parseNamedTypeArguments nested).ValidFor
      (Option.ValidFor
        (NonemptyDelimitedList.ValidFor TypeExpr.ValidFor)) := by
  unfold parseNamedTypeArguments
  apply Parser.bind_validFor getState_validFor
  intro observed
  by_cases present : isSymbol observed .less
  · simp only [present, if_true]
    apply Parser.bind_validFor_of_value
      (delimited_validFor TypeExpr.ValidFor .less .greater false nested
        .typeExpr .typeExpr nestedValid nestedPreserves)
    intro parsed input inputValid parsedValid
    unfold requireNonempty
    cases elements : parsed.elements with
    | nil => simp only [bind, Reply.ValidFor]
    | cons head tail =>
        simp only [bind, Reply.ValidFor, Option.ValidFor,
          NonemptyDelimitedList.ValidFor]
        refine ⟨⟨parsedValid.1, ?_⟩, inputValid, rfl⟩
        intro element member
        exact parsedValid.2 element (by
          simpa [NonemptyList.toList, elements] using member)
  · simp only [present]
    exact Parser.pure_validFor none _ (fun _ => trivial)

/-- Optional named-type arguments retain the recursive token carrier. -/
theorem parseNamedTypeArguments_preservesTokensOnSuccess
    (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (parseNamedTypeArguments nested) := by
  unfold parseNamedTypeArguments
  apply Parser.bind_preservesTokensOnSuccess getState_preservesTokensOnSuccess
  intro observed
  by_cases present : isSymbol observed .less
  · simp only [present, if_true]
    apply Parser.bind_preservesTokensOnSuccess
      (delimited_preservesTokensOnSuccess .less .greater false nested
        .typeExpr .typeExpr nestedPreserves)
    intro parsed
    apply Parser.bind_preservesTokensOnSuccess
      (requireNonempty_preservesTokensOnSuccess parsed .typeExpr)
    intro nonempty
    exact Parser.pure_preservesTokensOnSuccess _
  · simp only [present]
    exact Parser.pure_preservesTokensOnSuccess none

/-- Optional named-type arguments preserve every ordinary token window. -/
theorem parseNamedTypeArguments_preservesTokenWindow
    (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (parseNamedTypeArguments nested) := by
  unfold parseNamedTypeArguments
  apply Parser.bind_preservesTokenWindow getState_preservesTokenWindow
  intro observed
  by_cases present : isSymbol observed .less
  · simp only [present, if_true]
    apply Parser.bind_preservesTokenWindow
      (delimited_preservesTokenWindow .less .greater false nested
        .typeExpr .typeExpr nestedPreserves)
    intro parsed
    apply Parser.bind_preservesTokenWindow
      (requireNonempty_preservesTokenWindow parsed .typeExpr)
    intro nonempty
    exact Parser.pure_preservesTokenWindow _
  · simp only [present]
    exact Parser.pure_preservesTokenWindow none

/-- Optional named-type arguments never rewind the recursive cursor. -/
theorem parseNamedTypeArguments_cursorMonotoneOnSuccess
    (nested : Parser TypeExpr) :
    Parser.CursorMonotoneOnSuccess (parseNamedTypeArguments nested) := by
  unfold parseNamedTypeArguments
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isSymbol observed .less
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (delimited_cursorMonotoneOnSuccess .less .greater false nested
        .typeExpr .typeExpr)
    intro parsed
    apply Parser.bind_cursorMonotoneOnSuccess
      (requireNonempty_cursorMonotoneOnSuccess parsed .typeExpr)
    intro nonempty
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none

/-- Present named-type arguments start at the current `<` token. -/
theorem parseNamedTypeArguments_some_startsAtCurrentTokenOnSuccess
    (nested : Parser TypeExpr) {input next : State}
    {arguments : NonemptyDelimitedList TypeExpr}
    (result : parseNamedTypeArguments nested input = .ok (some arguments) next) :
    ∃ token, input.peek? = some token ∧
      token.span.startByte = arguments.span.startByte := by
  unfold parseNamedTypeArguments getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .less
  · simp only [present, if_true] at result
    rcases bind_ok_components result with
      ⟨parsed, afterParsed, parsedResult, rest⟩
    rcases bind_ok_components rest with
      ⟨nonempty, afterNonempty, nonemptyResult, finished⟩
    unfold requireNonempty at nonemptyResult
    cases elements : parsed.elements with
    | nil => rw [elements] at nonemptyResult; contradiction
    | cons head tail =>
        have starts := delimited_startsAtCurrentTokenOnSuccess .less .greater
          false nested .typeExpr .typeExpr input parsed afterParsed parsedResult
        rw [elements] at nonemptyResult
        cases nonemptyResult
        cases finished
        exact starts
  · simp only [present] at result
    cases result

private theorem finishNamedType_validFor {name : QualifiedName}
    {arguments : Option (NonemptyDelimitedList TypeExpr)} {input : State}
    (inputValid : input.ValidFor)
    (valueValid : TypeExpr.ValidFor input.file
      (makeNamedType name arguments)) :
    (finishNamedType name arguments input).ValidFor input
      TypeExpr.ValidFor := by
  unfold finishNamedType
  dsimp only
  split
  · unfold emitDiagnostic modifyState Reply.ValidFor
    exact ⟨valueValid,
      inputValid.emit_validFor _ valueValid.span_valid, rfl⟩
  · exact ⟨valueValid, inputValid, rfl⟩

/-- Named-type parsing retains all name, argument, and outer provenance. -/
theorem parseNamedType_validFor (nested : Parser TypeExpr)
    (nestedValid : nested.ValidFor TypeExpr.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (parseNamedType nested).ValidFor TypeExpr.ValidFor := by
  intro input inputValid
  unfold parseNamedType
  cases nameResult : qualifiedName .typeExpr .typeExpr input with
  | invariant error =>
      simp only [bind, nameResult, Reply.ValidFor]
  | reject failure rejected =>
      have valid := qualifiedName_validFor .typeExpr .typeExpr input inputValid
      rw [nameResult] at valid
      simp only [bind, nameResult, Reply.ValidFor]
      exact ⟨valid.1, valid.2.1, valid.2.2⟩
  | ok name afterName =>
      have nameValid := qualifiedName_validFor .typeExpr .typeExpr input inputValid
      rw [nameResult] at nameValid
      simp only [bind, nameResult]
      cases argumentsResult : parseNamedTypeArguments nested afterName with
      | invariant error => trivial
      | reject failure rejected =>
          have valid := parseNamedTypeArguments_validFor nested nestedValid
            nestedPreserves afterName nameValid.2.1
          rw [argumentsResult] at valid
          exact valid.of_file_eq nameValid.2.2
      | ok arguments afterArguments =>
          have argumentsValid := parseNamedTypeArguments_validFor nested
            nestedValid nestedPreserves afterName nameValid.2.1
          rw [argumentsResult] at argumentsValid
          simp only
          have nameValidFinal : QualifiedName.ValidFor afterArguments.file name := by
            simpa [argumentsValid.2.2] using
              (show QualifiedName.ValidFor afterName.file name from
                by simpa [nameValid.2.2] using nameValid.1)
          have valueValid : TypeExpr.ValidFor afterArguments.file
              (makeNamedType name arguments) := by
            cases arguments with
            | none => exact .namedWithoutArguments nameValidFinal.1 nameValidFinal
            | some values =>
                have valuesValid : NonemptyDelimitedList.ValidFor
                    TypeExpr.ValidFor afterArguments.file values := by
                  simpa [Option.ValidFor, argumentsValid.2.2] using argumentsValid.1
                rcases qualifiedName_startsAtCurrentTokenOnSuccess .typeExpr
                    .typeExpr input name afterName nameResult with
                  ⟨first, firstFound, nameStart⟩
                rcases parseNamedTypeArguments_some_startsAtCurrentTokenOnSuccess
                    nested argumentsResult with ⟨opening, openingFound, argsStart⟩
                have firstAtAfter : afterName.tokens[input.cursor]? = some first := by
                  rw [qualifiedName_preservesTokensOnSuccess .typeExpr .typeExpr
                    input name afterName nameResult]
                  exact State.getElem?_eq_some_of_peek?_eq_some firstFound
                have openingAtAfter :=
                  State.getElem?_eq_some_of_peek?_eq_some openingFound
                have ordered := nameValid.2.1.token_end_le_token_start_of_getElem?_lt
                  firstAtAfter openingAtAfter
                  (qualifiedName_cursor_lt_onSuccess .typeExpr .typeExpr nameResult)
                have firstValid := nameValid.2.1.token_span_validFor_of_getElem?_eq_some
                  firstAtAfter
                have outerOrder : name.span.startByte ≤ values.span.endByte := by
                  rw [← nameStart]
                  exact Nat.le_trans firstValid.2.1
                    (Nat.le_trans ordered (by
                      rw [argsStart]
                      exact valuesValid.1.2.1))
                exact .namedWithArguments
                  (SourceSpan.cover_validFor nameValidFinal.1 valuesValid.1
                    outerOrder)
                  nameValidFinal valuesValid.1 valuesValid.2
          exact (finishNamedType_validFor argumentsValid.2.1 valueValid).of_file_eq
            (argumentsValid.2.2.trans nameValid.2.2)

/-- Finishing a named type preserves the full ordinary token window. -/
theorem finishNamedType_preservesTokenWindow (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) :
    Parser.PreservesTokenWindow (finishNamedType name arguments) := by
  intro input
  unfold finishNamedType
  dsimp only
  split
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- Finishing a named type leaves the cursor in place. -/
theorem finishNamedType_cursorMonotoneOnSuccess (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) :
    Parser.CursorMonotoneOnSuccess (finishNamedType name arguments) := by
  intro input value next result
  unfold finishNamedType at result
  dsimp only at result
  split at result
  · unfold emitDiagnostic modifyState at result
    simp only [bind] at result
    cases result
    exact Nat.le_refl _
  · cases result
    exact Nat.le_refl _

/-- Named-type parsing preserves tokens and its active window on every reply. -/
theorem parseNamedType_preservesTokenWindow (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (parseNamedType nested) := by
  unfold parseNamedType
  apply Parser.bind_preservesTokenWindow
    (qualifiedName_preservesTokenWindow .typeExpr .typeExpr)
  intro name
  apply Parser.bind_preservesTokenWindow
    (parseNamedTypeArguments_preservesTokenWindow nested nestedPreserves)
  intro arguments
  exact finishNamedType_preservesTokenWindow name arguments

/-- Successful named-type parsing retains the recursive token carrier. -/
theorem parseNamedType_preservesTokensOnSuccess (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (parseNamedType nested) := by
  unfold parseNamedType
  apply Parser.bind_preservesTokensOnSuccess
    (qualifiedName_preservesTokensOnSuccess .typeExpr .typeExpr)
  intro name
  apply Parser.bind_preservesTokensOnSuccess
    (parseNamedTypeArguments_preservesTokensOnSuccess nested nestedPreserves)
  intro arguments
  exact (finishNamedType_preservesTokenWindow name arguments).preservesTokensOnSuccess

/-- Named-type parsing never rewinds the recursive parser cursor. -/
theorem parseNamedType_cursorMonotoneOnSuccess (nested : Parser TypeExpr) :
    Parser.CursorMonotoneOnSuccess (parseNamedType nested) := by
  unfold parseNamedType
  apply Parser.bind_cursorMonotoneOnSuccess
    (qualifiedName_cursorMonotoneOnSuccess .typeExpr .typeExpr)
  intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    (parseNamedTypeArguments_cursorMonotoneOnSuccess nested)
  intro arguments
  exact finishNamedType_cursorMonotoneOnSuccess name arguments

private theorem finishNamedType_ok_value {name : QualifiedName}
    {arguments : Option (NonemptyDelimitedList TypeExpr)}
    {input next : State} {value : TypeExpr}
    (result : finishNamedType name arguments input = .ok value next) :
    value = makeNamedType name arguments := by
  unfold finishNamedType at result
  dsimp only at result
  split at result
  · unfold emitDiagnostic modifyState at result
    simp only [bind] at result
    cases result
    rfl
  · cases result
    rfl

/-- A named type starts at the first component of its qualified name. -/
theorem parseNamedType_startsAtCurrentTokenOnSuccess
    (nested : Parser TypeExpr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (parseNamedType nested) (·.span) := by
  unfold parseNamedType
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (qualifiedName_startsAtCurrentTokenOnSuccess .typeExpr .typeExpr)
  intro name input value final parsed
  rcases bind_ok_components parsed with
    ⟨arguments, afterArguments, _argumentsResult, finished⟩
  rw [finishNamedType_ok_value finished]
  cases arguments <;> rfl

end Solcore.Syntax.Parser
