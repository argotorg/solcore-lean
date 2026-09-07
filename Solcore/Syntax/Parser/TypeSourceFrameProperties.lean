import Solcore.Syntax.Parser.DelimitedSourceFrameProperties
import Solcore.Syntax.Parser.Type

/-! Every ordinary recursive-type reply retains the complete input source
file, including rejection after successful children. Raw forms require only
that child source law. No validity, progress, token, window, diagnostic, or
ordinary-outcome premise is used; invariant replies carry no returned state. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem requireNonempty_preservesFile {α : Type}
    (parsed : DelimitedList α) (phase : ParserPhase) :
    Parser.PreservesFile (requireNonempty parsed phase) := by
  intro input
  unfold requireNonempty
  cases parsed.elements with
  | nil => trivial
  | cons head tail => rfl

theorem parseNamedTypeArguments_preservesFile (nested : Parser TypeExpr)
    (nestedFile : Parser.PreservesFile nested) :
    Parser.PreservesFile (parseNamedTypeArguments nested) := by
  unfold parseNamedTypeArguments
  apply Parser.bind_preservesFile getState_preservesFile
  intro observed
  split
  · apply Parser.bind_preservesFile
      (delimited_preservesFile .less .greater false nested .typeExpr .typeExpr nestedFile)
    intro parsed
    apply Parser.bind_preservesFile (requireNonempty_preservesFile parsed .typeExpr)
    intro nonempty
    exact Parser.pure_preservesFile _
  · exact Parser.pure_preservesFile none

theorem finishNamedType_preservesFile (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) :
    Parser.PreservesFile (finishNamedType name arguments) := by
  unfold finishNamedType
  split
  · apply Parser.bind_preservesFile (emitDiagnostic_preservesFile _)
    intro ignored
    exact Parser.pure_preservesFile _
  · exact Parser.pure_preservesFile _

theorem parseNamedType_preservesFile (nested : Parser TypeExpr)
    (nestedFile : Parser.PreservesFile nested) :
    Parser.PreservesFile (parseNamedType nested) := by
  unfold parseNamedType
  apply Parser.bind_preservesFile (qualifiedName_preservesFile .typeExpr .typeExpr)
  intro name
  apply Parser.bind_preservesFile (parseNamedTypeArguments_preservesFile nested nestedFile)
  intro arguments
  exact finishNamedType_preservesFile name arguments

theorem parseMappingType_preservesFile (nested : Parser TypeExpr)
    (nestedFile : Parser.PreservesFile nested) :
    Parser.PreservesFile (parseMappingType nested) := by
  unfold parseMappingType
  apply Parser.bind_preservesFile (contextual_preservesFile .mapping .typeExpr)
  intro marker
  apply Parser.bind_preservesFile (symbol_preservesFile .leftParen .typeExpr)
  intro opening
  apply Parser.bind_preservesFile nestedFile
  intro key
  apply Parser.bind_preservesFile (symbol_preservesFile .fatArrow .typeExpr)
  intro arrow
  apply Parser.bind_preservesFile nestedFile
  intro value
  apply Parser.bind_preservesFile (symbol_preservesFile .rightParen .typeExpr)
  intro closing
  exact Parser.pure_preservesFile _

theorem parseComptimeType_preservesFile (nested : Parser TypeExpr)
    (nestedFile : Parser.PreservesFile nested) :
    Parser.PreservesFile (parseComptimeType nested) := by
  unfold parseComptimeType
  apply Parser.bind_preservesFile (contextual_preservesFile .comptime .typeExpr)
  intro marker
  apply Parser.bind_preservesFile (symbol_preservesFile .less .typeExpr)
  intro opening
  apply Parser.bind_preservesFile nestedFile
  intro inner
  apply Parser.bind_preservesFile (symbol_preservesFile .greater .typeExpr)
  intro closing
  exact Parser.pure_preservesFile _

theorem parseProxyType_preservesFile (nested : Parser TypeExpr)
    (nestedFile : Parser.PreservesFile nested) :
    Parser.PreservesFile (parseProxyType nested) := by
  intro input
  unfold parseProxyType
  cases markerResult : symbol .at .typeExpr input with
  | invariant error => trivial
  | reject failure rejected => exact (symbol_preservesFile .at .typeExpr).file_eq_of_reject markerResult
  | ok marker afterMarker =>
      have markerFile := (symbol_preservesFile .at .typeExpr).file_eq_of_ok markerResult
      simp only
      cases innerResult : nested afterMarker with
      | invariant error => trivial
      | ok inner output => exact Eq.trans (nestedFile.file_eq_of_ok innerResult) markerFile
      | reject failure rejected => exact Eq.trans (nestedFile.file_eq_of_reject innerResult) markerFile

theorem parseTupleType_preservesFile (nested : Parser TypeExpr)
    (nestedFile : Parser.PreservesFile nested) :
    Parser.PreservesFile (parseTupleType nested) := by
  unfold parseTupleType
  apply Parser.bind_preservesFile
    (delimited_preservesFile .leftParen .rightParen true nested .typeExpr .typeExpr nestedFile)
  intro tuple
  exact Parser.pure_preservesFile _

theorem TypeFunctionInternals.parseFunctionReturns_preservesFile (nested : Parser TypeExpr)
    (nestedFile : Parser.PreservesFile nested) :
    Parser.PreservesFile (TypeFunctionInternals.parseFunctionReturns nested) := by
  unfold TypeFunctionInternals.parseFunctionReturns
  apply Parser.bind_preservesFile getState_preservesFile
  intro observed
  split
  · apply Parser.bind_preservesFile (contextual_preservesFile .returns .typeExpr)
    intro marker
    apply Parser.bind_preservesFile
      (delimited_preservesFile .leftParen .rightParen true nested .typeExpr .typeExpr nestedFile)
    intro values
    exact Parser.pure_preservesFile _
  · exact Parser.pure_preservesFile none

theorem parseFunctionType_preservesFile (nested : Parser TypeExpr)
    (nestedFile : Parser.PreservesFile nested) :
    Parser.PreservesFile (parseFunctionType nested) := by
  unfold parseFunctionType
  apply Parser.bind_preservesFile (keyword_preservesFile .functionKw .typeExpr)
  intro marker
  apply Parser.bind_preservesFile
    (delimited_preservesFile .leftParen .rightParen true nested .typeExpr .typeExpr nestedFile)
  intro parameters
  apply Parser.bind_preservesFile (TypeFunctionInternals.parseFunctionReturns_preservesFile nested nestedFile)
  intro returns
  exact Parser.pure_preservesFile _

theorem typeExprWithFuel_preservesFile (fuel : Nat) :
    Parser.PreservesFile (typeExprWithFuel fuel) := by
  induction fuel with
  | zero => intro input; trivial
  | succ fuel ih =>
      intro input
      simp only [typeExprWithFuel]
      split
      · exact parseFunctionType_preservesFile _ ih input
      · split
        · exact parseComptimeType_preservesFile _ ih input
        · split
          · exact parseMappingType_preservesFile _ ih input
          · split
            · exact parseProxyType_preservesFile _ ih input
            · split
              · exact parseTupleType_preservesFile _ ih input
              · split
                · exact parseNamedType_preservesFile _ ih input
                · exact rejectAt_preservesFile input _ .typeExpr

theorem typeExpr_preservesFile : Parser.PreservesFile typeExpr := by
  intro input
  exact typeExprWithFuel_preservesFile (input.remainingCount + 1) input

end Solcore.Syntax.Parser
