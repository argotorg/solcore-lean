import Solcore.Syntax.DeclarativeCoreIdentifierOutcomeGrammar

/-!
Parser-independent broad ordinary outcomes for an optional selected-import
alias.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary selected-alias success is the existing exact prioritized
grammar: absence is nonconsuming, while `as` commits to one identifier. -/
abbrev SelectedAliasOrdinaryParses := SelectedAliasParses

/-- Exact rejection after a present `as` marker commits to its identifier. -/
inductive SelectedAliasRejects : Remainder → Remainder → Prop where
  | nameRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .asKw) input markerSpan
        afterMarker)
      (nameRejected : IdentifierRejects afterMarker rejected) :
      SelectedAliasRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
