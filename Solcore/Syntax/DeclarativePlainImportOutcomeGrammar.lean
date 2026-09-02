import Solcore.Syntax.DeclarativeImportTerminatorOutcomeGrammar
import Solcore.Syntax.DeclarativeModulePathOutcomeGrammar

/-! Parser-independent broad ordinary outcomes for plain import payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact broad success of `plainImport` after the outer `import` keyword. -/
inductive PlainImportOrdinaryParses (start : SourceSpan) :
    Remainder → Syntax.ImportDecl → Remainder → Prop where
  | parsed {input afterPath output : Remainder}
      {path : Syntax.ModulePath} {endSpan : SourceSpan}
      (pathParsed : ModulePathOrdinaryParses input path afterPath)
      (terminatorParsed : ImportTerminatorOrdinaryParses path.span afterPath
        endSpan output) :
      PlainImportOrdinaryParses start input {
        span := SourceSpan.cover start endSpan
        value := .plain path
      } output

/-- Exact first rejecting stage of a plain import payload. -/
inductive PlainImportRejects : Remainder → Remainder → Prop where
  | pathRejected {input rejected : Remainder}
      (pathRejected : ModulePathRejects input rejected) :
      PlainImportRejects input rejected
  | terminatorRejected {input afterPath rejected : Remainder}
      {path : Syntax.ModulePath}
      (pathParsed : ModulePathOrdinaryParses input path afterPath)
      (terminatorRejected : ImportTerminatorRejects afterPath rejected) :
      PlainImportRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
