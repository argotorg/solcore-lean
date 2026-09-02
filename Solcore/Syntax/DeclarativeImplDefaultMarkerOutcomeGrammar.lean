import Solcore.Syntax.DeclarativeGrammar

/-!
Parser-independent ordinary success and impossible rejection for the optional
leading `default` implementation marker.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary optional-default success is the existing exact prioritized
grammar. -/
abbrev OptionalImplDefaultMarkerOrdinaryParses :=
  OptionalImplDefaultMarkerParses

/-- The guarded optional-default parser has no executable reject branch. -/
def OptionalImplDefaultMarkerRejects (_input _rejected : Remainder) : Prop :=
  False

end Solcore.Syntax.DeclarativeGrammar
