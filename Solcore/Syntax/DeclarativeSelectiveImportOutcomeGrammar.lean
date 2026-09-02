import Solcore.Syntax.DeclarativeHidingClauseOutcomeGrammar
import Solcore.Syntax.DeclarativeImportTerminatorOutcomeGrammar
import Solcore.Syntax.DeclarativeModulePathOutcomeGrammar
import Solcore.Syntax.DeclarativeSelectedImportsOutcomeGrammar

/-!
Parser-independent broad ordinary outcomes for selective import payloads.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact broad selective-import success in executable stage order, including
optional hiding and explicit-or-recovered terminator success. -/
inductive SelectiveImportOrdinaryParses (start : SourceSpan) :
    Remainder → Syntax.ImportDecl → Remainder → Prop where
  | parsed
      {input afterSelection afterFrom afterPath afterHiding
        output : Remainder}
      {selection : NonemptyDelimitedList Syntax.SelectedImport}
      {path : Syntax.ModulePath} {hidden : Option Syntax.HidingClause}
      {endSpan : SourceSpan} (fromSpan : SourceSpan)
      (selectionParsed : SelectedImportsOrdinaryParses input selection
        afterSelection)
      (fromParsed : ExactTokenParses
        (.identifier ContextualKeyword.from.spelling) afterSelection fromSpan
          afterFrom)
      (pathParsed : ModulePathOrdinaryParses afterFrom path afterPath)
      (hidingParsed : OptionalHidingOrdinaryParses afterPath hidden
        afterHiding)
      (terminatorParsed : ImportTerminatorOrdinaryParses
        (match hidden with
          | some clause => clause.span
          | none => path.span)
        afterHiding endSpan output) :
      SelectiveImportOrdinaryParses start input {
        span := SourceSpan.cover start endSpan
        value := .selected selection path hidden
      } output

/-- Exact first rejecting stage of one selective-import helper attempt. -/
inductive SelectiveImportRejects : Remainder → Remainder → Prop where
  | selectionRejected {input rejected : Remainder}
      (selectionRejected : SelectedImportsRejects input rejected) :
      SelectiveImportRejects input rejected
  | fromMissing {input afterSelection : Remainder}
      {selection : NonemptyDelimitedList Syntax.SelectedImport}
      (selectionParsed : SelectedImportsOrdinaryParses input selection
        afterSelection)
      (fromAbsent : TokenKindAbsentAt afterSelection.tokens
        afterSelection.endIndex afterSelection.cursor
          (.identifier ContextualKeyword.from.spelling)) :
      SelectiveImportRejects input afterSelection
  | pathRejected
      {input afterSelection afterFrom rejected : Remainder}
      {selection : NonemptyDelimitedList Syntax.SelectedImport}
      (fromSpan : SourceSpan)
      (selectionParsed : SelectedImportsOrdinaryParses input selection
        afterSelection)
      (fromParsed : ExactTokenParses
        (.identifier ContextualKeyword.from.spelling) afterSelection fromSpan
          afterFrom)
      (pathRejected : ModulePathRejects afterFrom rejected) :
      SelectiveImportRejects input rejected
  | hidingRejected
      {input afterSelection afterFrom afterPath rejected : Remainder}
      {selection : NonemptyDelimitedList Syntax.SelectedImport}
      {path : Syntax.ModulePath} (fromSpan : SourceSpan)
      (selectionParsed : SelectedImportsOrdinaryParses input selection
        afterSelection)
      (fromParsed : ExactTokenParses
        (.identifier ContextualKeyword.from.spelling) afterSelection fromSpan
          afterFrom)
      (pathParsed : ModulePathOrdinaryParses afterFrom path afterPath)
      (hidingRejected : OptionalHidingRejects afterPath rejected) :
      SelectiveImportRejects input rejected
  | terminatorRejected
      {input afterSelection afterFrom afterPath afterHiding
        rejected : Remainder}
      {selection : NonemptyDelimitedList Syntax.SelectedImport}
      {path : Syntax.ModulePath} {hidden : Option Syntax.HidingClause}
      (fromSpan : SourceSpan)
      (selectionParsed : SelectedImportsOrdinaryParses input selection
        afterSelection)
      (fromParsed : ExactTokenParses
        (.identifier ContextualKeyword.from.spelling) afterSelection fromSpan
          afterFrom)
      (pathParsed : ModulePathOrdinaryParses afterFrom path afterPath)
      (hidingParsed : OptionalHidingOrdinaryParses afterPath hidden
        afterHiding)
      (terminatorRejected : ImportTerminatorRejects afterHiding rejected) :
      SelectiveImportRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
