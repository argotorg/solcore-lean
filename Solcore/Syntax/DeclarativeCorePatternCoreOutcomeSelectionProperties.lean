import Solcore.Syntax.DeclarativeCorePatternCoreOutcomeLeafProperties

/-! Unique selection of the seven ordered `patternCore` branches. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex cursor : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex cursor kind)
    (present : TokenAt tokens endIndex cursor { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- Ordered Core-pattern guard evidence selects a unique branch. -/
theorem PatternCoreBranchSelected.branch_unique
    {left right : PatternCoreBranch} {input : Remainder}
    (leftSelected : PatternCoreBranchSelected left input)
    (rightSelected : PatternCoreBranchSelected right input) : left = right := by
  cases leftSelected with
  | wildcard leftMarker =>
      cases rightSelected with
      | wildcard => rfl
      | literal rightAbsent _
      | boolean rightAbsent _ _
      | parenthesized rightAbsent _ _ _
      | dotConstructor rightAbsent _ _ _ _
      | comptime rightAbsent _ _ _ _ _
      | qualified rightAbsent _ _ _ _ _ _ =>
          exact False.elim (absent_conflicts_token rightAbsent leftMarker)
  | literal leftUnderscoreAbsent leftStarts =>
      cases rightSelected with
      | wildcard rightMarker =>
          exact False.elim
            (absent_conflicts_token leftUnderscoreAbsent rightMarker)
      | literal => rfl
      | boolean _ rightAbsent _
      | parenthesized _ rightAbsent _ _
      | dotConstructor _ rightAbsent _ _ _
      | comptime _ rightAbsent _ _ _ _
      | qualified _ rightAbsent _ _ _ _ _ =>
          exact False.elim (rightAbsent leftStarts)
  | boolean leftUnderscoreAbsent leftLiteralAbsent leftStarts =>
      cases rightSelected with
      | wildcard rightMarker =>
          exact False.elim
            (absent_conflicts_token leftUnderscoreAbsent rightMarker)
      | literal _ rightStarts => exact False.elim (leftLiteralAbsent rightStarts)
      | boolean => rfl
      | parenthesized _ _ rightAbsent _
      | dotConstructor _ _ rightAbsent _ _
      | comptime _ _ rightAbsent _ _ _
      | qualified _ _ rightAbsent _ _ _ _ =>
          exact False.elim (rightAbsent leftStarts)
  | parenthesized leftUnderscoreAbsent leftLiteralAbsent leftBooleanAbsent
        leftMarker =>
      cases rightSelected with
      | wildcard rightMarker =>
          exact False.elim
            (absent_conflicts_token leftUnderscoreAbsent rightMarker)
      | literal _ rightStarts => exact False.elim (leftLiteralAbsent rightStarts)
      | boolean _ _ rightStarts =>
          exact False.elim (leftBooleanAbsent rightStarts)
      | parenthesized => rfl
      | dotConstructor _ _ _ rightAbsent _
      | comptime _ _ _ rightAbsent _ _
      | qualified _ _ _ rightAbsent _ _ _ =>
          exact False.elim (absent_conflicts_token rightAbsent leftMarker)
  | dotConstructor leftUnderscoreAbsent leftLiteralAbsent leftBooleanAbsent
        leftParenAbsent leftMarker =>
      cases rightSelected with
      | wildcard rightMarker =>
          exact False.elim
            (absent_conflicts_token leftUnderscoreAbsent rightMarker)
      | literal _ rightStarts => exact False.elim (leftLiteralAbsent rightStarts)
      | boolean _ _ rightStarts =>
          exact False.elim (leftBooleanAbsent rightStarts)
      | parenthesized _ _ _ rightMarker =>
          exact False.elim
            (absent_conflicts_token leftParenAbsent rightMarker)
      | dotConstructor => rfl
      | comptime _ _ _ _ rightAbsent _
      | qualified _ _ _ _ rightAbsent _ _ =>
          exact False.elim (absent_conflicts_token rightAbsent leftMarker)
  | comptime leftUnderscoreAbsent leftLiteralAbsent leftBooleanAbsent
        leftParenAbsent leftDotAbsent leftMarker =>
      cases rightSelected with
      | wildcard rightMarker =>
          exact False.elim
            (absent_conflicts_token leftUnderscoreAbsent rightMarker)
      | literal _ rightStarts => exact False.elim (leftLiteralAbsent rightStarts)
      | boolean _ _ rightStarts =>
          exact False.elim (leftBooleanAbsent rightStarts)
      | parenthesized _ _ _ rightMarker =>
          exact False.elim
            (absent_conflicts_token leftParenAbsent rightMarker)
      | dotConstructor _ _ _ _ rightMarker =>
          exact False.elim (absent_conflicts_token leftDotAbsent rightMarker)
      | comptime => rfl
      | qualified _ _ _ _ _ rightAbsent _ =>
          exact False.elim (absent_conflicts_token rightAbsent leftMarker)
  | qualified leftUnderscoreAbsent leftLiteralAbsent leftBooleanAbsent
        leftParenAbsent leftDotAbsent leftComptimeAbsent leftMarker =>
      cases rightSelected with
      | wildcard rightMarker =>
          exact False.elim
            (absent_conflicts_token leftUnderscoreAbsent rightMarker)
      | literal _ rightStarts => exact False.elim (leftLiteralAbsent rightStarts)
      | boolean _ _ rightStarts =>
          exact False.elim (leftBooleanAbsent rightStarts)
      | parenthesized _ _ _ rightMarker =>
          exact False.elim
            (absent_conflicts_token leftParenAbsent rightMarker)
      | dotConstructor _ _ _ _ rightMarker =>
          exact False.elim (absent_conflicts_token leftDotAbsent rightMarker)
      | comptime _ _ _ _ _ rightMarker =>
          exact False.elim
            (absent_conflicts_token leftComptimeAbsent rightMarker)
      | qualified => rfl

/-- Every ordinary success retains its exact branch selection. -/
theorem PatternCoreOrdinaryParses.exists_branch_selected
    {parenthesizedOrdinary dotConstructorOrdinary comptimeOrdinary
      qualifiedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {input output : Remainder} {pattern : Syntax.Pattern}
    (parsed : PatternCoreOrdinaryParses parenthesizedOrdinary
      dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary input pattern
        output) :
    ∃ branch, PatternCoreBranchSelected branch input := by
  cases parsed with
  | selected selection _ => exact ⟨_, selection⟩

/-- The exact final rejection excludes every selected branch. -/
theorem PatternCoreFinalRejects.disjointSelected
    {input rejected : Remainder}
    (rejection : PatternCoreFinalRejects input rejected) :
    ¬ ∃ branch, PatternCoreBranchSelected branch input := by
  rintro ⟨branch, selected⟩
  cases rejection with
  | final underscoreAbsent literalAbsent booleanAbsent leftParenAbsent
        dotAbsent comptimeAbsent identifierAbsent =>
      cases selected with
      | wildcard marker => exact absent_conflicts_token underscoreAbsent marker
      | literal _ starts => exact literalAbsent starts
      | boolean _ _ starts => exact booleanAbsent starts
      | parenthesized _ _ _ marker =>
          exact absent_conflicts_token leftParenAbsent marker
      | dotConstructor _ _ _ _ marker =>
          exact absent_conflicts_token dotAbsent marker
      | comptime _ _ _ _ _ marker =>
          exact absent_conflicts_token comptimeAbsent marker
      | qualified _ _ _ _ _ _ marker =>
          exact identifierAbsent ⟨_, _, marker⟩

end Solcore.Syntax.DeclarativeGrammar
