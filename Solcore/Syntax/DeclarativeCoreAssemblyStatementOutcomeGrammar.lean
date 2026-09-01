import Solcore.Syntax.DeclarativeCoreAssemblyStatementGrammar
import Solcore.Syntax.DeclarativeYulBodyGrammar

/-! Ordinary success and exact rejection for Core `assembly`. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Diagnostic-inclusive Core assembly success with the concrete public Yul
body relation. -/
abbrev AssemblyStatementOrdinaryParses :=
  AssemblyStatementParses YulBodyOrdinaryParses

/-- Exact first rejection stage of one Core assembly wrapper. -/
inductive AssemblyStatementRejects : Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .assemblyKw)) :
      AssemblyStatementRejects input input
  | bodyRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .assemblyKw) input markerSpan
        afterMarker)
      (bodyRejected : YulBodyRejects afterMarker rejected) :
      AssemblyStatementRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
