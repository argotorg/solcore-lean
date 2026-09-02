import Solcore.Syntax.DeclarativeCoreIdentifierOutcomeGrammar

/-!
Parser-independent exact rejection traces for dotted derive targets.

The established `DeriveComponentParses`, `DeriveTargetTailParses`, and
`DeriveTargetParses` relations already describe every ordinary success,
including diagnosed reserved-keyword components.  The relations below add
the complementary rejection path without changing those successes.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- No hard keyword admitted as a diagnosed derive component occurs at the
current cursor. -/
def DeriveReservedComponentAbsentAt (input : Remainder) : Prop :=
  ∀ keyword, ReservedDeriveTargetKeyword keyword →
    TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword keyword)

/-- Exact nonconsuming rejection of one derive component after both the
reserved-keyword recovery branch and the identifier branch are unavailable. -/
inductive DeriveComponentRejects : Remainder → Remainder → Prop where
  | unavailable {input : Remainder}
      (reservedAbsent : DeriveReservedComponentAbsentAt input)
      (identifierRejected : IdentifierRejects input input) :
      DeriveComponentRejects input input

/-- Exact rejection while consuming the dotted tail of one derive target.
The dot advances once before a component rejection; a successful component
delegates only to the later tail. -/
inductive DeriveTargetTailRejects : Remainder → Remainder → Prop where
  | componentRejected {input afterDot rejected : Remainder}
      (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (componentRejected : DeriveComponentRejects afterDot rejected) :
      DeriveTargetTailRejects input rejected
  | laterRejected {input afterDot afterComponent rejected : Remainder}
      {component : Syntax.Identifier} (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (componentParsed : DeriveComponentParses afterDot component
        afterComponent)
      (laterRejected : DeriveTargetTailRejects afterComponent rejected) :
      DeriveTargetTailRejects input rejected

/-- Exact first or later component rejection of a complete derive target. -/
inductive DeriveTargetRejects : Remainder → Remainder → Prop where
  | firstRejected {input rejected : Remainder}
      (componentRejected : DeriveComponentRejects input rejected) :
      DeriveTargetRejects input rejected
  | tailRejected {input afterFirst rejected : Remainder}
      {first : Syntax.Identifier}
      (firstParsed : DeriveComponentParses input first afterFirst)
      (tailRejected : DeriveTargetTailRejects afterFirst rejected) :
      DeriveTargetRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
