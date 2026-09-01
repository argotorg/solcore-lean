import Solcore.Syntax.DeclarativeCoreTypeListOutcomeProperties
import Solcore.Syntax.DeclarativeCoreExpressionPostfixOrdinaryProperties

/-! Disjointness facts for recursive Core-type qualified names. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact qualified-name-tail rejection excludes a dotted-tail success. -/
theorem TypeQualifiedNameTailRejects.disjointDotted
    {input rejected : Remainder}
    (rejection : TypeQualifiedNameTailRejects input rejected) :
    ¬ ∃ components finish,
      DottedIdentifierTailParses input.tokens input.endIndex input.cursor
        components finish := by
  induction rejection with
  | componentRejected dotSpan dotParsed componentRejected =>
      rintro ⟨components, finish, successful⟩
      cases successful with
      | done cursor dotAbsent =>
          exact typeTokenAbsent_conflicts_token dotAbsent dotParsed.1
      | next _ successfulDot componentToken tail =>
          have afterDotEq := dotParsed.2
          subst afterDotEq
          cases componentRejected with
          | absent identifierAbsent =>
              exact identifierAbsent ⟨_, _, componentToken⟩
  | @laterRejected rejectionInput afterDot afterComponent rejected component
        dotSpan dotParsed componentParsed laterRejected inductionHypothesis =>
      rintro ⟨components, finish, successful⟩
      cases successful with
      | done cursor dotAbsent =>
          exact typeTokenAbsent_conflicts_token dotAbsent dotParsed.1
      | @next _ _ component components _ successfulDot componentToken tail =>
          have afterDotEq := dotParsed.2
          subst afterDotEq
          have successfulComponent : IdentifierParses
              { rejectionInput with
                cursor := rejectionInput.cursor + 1 } component
              { rejectionInput with
                cursor := rejectionInput.cursor + 2 } := by
            refine ⟨componentToken, rfl, rfl, ?_⟩
            simp
          have outputEq := IdentifierParses.output_unique componentParsed
            successfulComponent
          subst outputEq
          exact inductionHypothesis ⟨_, _, tail⟩

/-- Exact qualified-name rejection excludes qualified-name success. -/
theorem TypeQualifiedNameRejects.disjointQualified
    {input rejected : Remainder}
    (rejection : TypeQualifiedNameRejects input rejected) :
    ¬ ∃ name output, QualifiedNameParses input name output := by
  rintro ⟨name, output, successful⟩
  rcases successful with
    ⟨tokensEq, endIndexEq, firstToken, successfulTail, spanEq⟩
  cases rejection with
  | firstRejected firstRejected =>
      cases firstRejected with
      | absent identifierAbsent =>
          exact identifierAbsent ⟨_, _, firstToken⟩
  | tailRejected firstParsed tailRejected =>
      have successfulFirst : IdentifierParses input
          name.value.components.head { input with cursor := input.cursor + 1 } :=
        ⟨firstToken, rfl, rfl, rfl⟩
      have outputEq := IdentifierParses.output_unique firstParsed
        successfulFirst
      subst outputEq
      exact tailRejected.disjointDotted ⟨_, _, successfulTail⟩

end Solcore.Syntax.DeclarativeGrammar
