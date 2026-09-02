import Solcore.Syntax.DeclarativeCoreTypeOutcomeGrammar

/-! Parser-independent broad ordinary outcomes for module paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary module-path success is the existing exact prioritized grammar. -/
abbrev ModulePathOrdinaryParses := ModulePathParses

/-- Exact module-path rejection in local and external-package priority order. -/
inductive ModulePathRejects : Remainder → Remainder → Prop where
  | localRejected {input rejected : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .at))
      (nameRejected : TypeQualifiedNameRejects input rejected) :
      ModulePathRejects input rejected
  | externalRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.symbol .at) input markerSpan
        afterMarker)
      (nameRejected : TypeQualifiedNameRejects afterMarker rejected) :
      ModulePathRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
