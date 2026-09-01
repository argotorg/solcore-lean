import Solcore.Syntax.DeclarativeYulBlockOutcomeProperties
import Solcore.Syntax.DeclarativeYulStatementFuelGrammar

/-!
Concrete parser-independent grammar and outcomes for the public braced
inline-Yul body parser.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Diagnostic-free public Yul body grammar. -/
abbrev YulBodyParses := YulBlockParses YulStatementParses

/-- Ordinary public Yul body grammar, including diagnosed statements. -/
abbrev YulBodyOrdinaryParses :=
  YulBlockOrdinaryParses YulStatementOrdinaryParses

/-- Exact rejection traces for the public Yul body parser. -/
abbrev YulBodyRejects :=
  YulBlockRejects YulStatementOrdinaryParses YulStatementRejects

/-- Packaged ordinary body relation used by deterministic outcome laws. -/
abbrev YulBodyOutcomeParses :=
  YulBlockOutcomeParses YulStatementOrdinaryParses

/-- Public Yul body success and rejection have deterministic outcomes. -/
theorem yulBodyDeterministicOutcomeSpec :
    DeterministicOutcomeSpec YulBodyOutcomeParses YulBodyRejects :=
  yulBlockDeterministicOutcomeSpec
    yulStatementPublicDeterministicOutcomeSpec

/-- Every diagnostic-free public body is the same ordinary body. -/
theorem YulBodyParses.toOrdinary
    {input output : Remainder} {bodySpan : SourceSpan}
    {body : List Syntax.YulStmt}
    (parsed : YulBodyParses input bodySpan body output) :
    YulBodyOrdinaryParses input bodySpan body output :=
  YulBlockParses.toOrdinary
    (fun statement => statement.toOrdinary) parsed

end Solcore.Syntax.DeclarativeGrammar
