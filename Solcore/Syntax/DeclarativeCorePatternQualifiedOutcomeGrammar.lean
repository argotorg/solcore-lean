import Solcore.Syntax.DeclarativeCorePatternArgumentsOutcomeGrammar
import Solcore.Syntax.DeclarativeCorePatternQualifiedNameOutcomeGrammar

/-! Ordinary outcomes for qualified Core binder and constructor patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact diagnostic-inclusive qualified-pattern success.  Optional arguments
retain absence, transactional rewind, and committed-present outcomes. -/
inductive QualifiedPatternOrdinaryParses
    (nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Syntax.Pattern → Remainder → Prop where
  | binder {input afterPath output : Remainder}
      {path : Syntax.QualifiedName} {name : Syntax.Identifier}
      {arguments : Option (NonemptyDelimitedList Syntax.Pattern)}
      (pathParsed : PatternQualifiedNameOrdinaryParses input path afterPath)
      (argumentsParsed : OptionalConstructorArgumentsOrdinaryParses
        nestedOrdinary nestedRejects afterPath arguments output)
      (componentsReversed : path.value.components.toList.reverse = [name])
      (choice : qualifiedPatternIsBinder [] arguments name = true) :
      QualifiedPatternOrdinaryParses nestedOrdinary nestedRejects input {
        span := path.span
        value := .binder name
      } output
  | constructor {input afterPath output : Remainder}
      {path : Syntax.QualifiedName} {name : Syntax.Identifier}
      {qualifiersRev : List Syntax.Identifier}
      {arguments : Option (NonemptyDelimitedList Syntax.Pattern)}
      (pathParsed : PatternQualifiedNameOrdinaryParses input path afterPath)
      (argumentsParsed : OptionalConstructorArgumentsOrdinaryParses
        nestedOrdinary nestedRejects afterPath arguments output)
      (componentsReversed :
        path.value.components.toList.reverse = name :: qualifiersRev)
      (choice : qualifiedPatternIsBinder qualifiersRev arguments name =
        false) :
      QualifiedPatternOrdinaryParses nestedOrdinary nestedRejects input {
        span := SourceSpan.cover path.span
          (arguments.map (fun values => values.span) |>.getD path.span)
        value := .constructor none qualifiersRev.reverse name arguments
      } output

/-- Exact sequential rejection.  The second constructor records the
formally complete optional-arguments stage, whose concrete rejection relation
is empty because that parser transactionally rewinds. -/
inductive QualifiedPatternRejects
    (nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | pathRejected {input rejected : Remainder}
      (rejectedPath : PatternQualifiedNameRejects input rejected) :
      QualifiedPatternRejects nestedOrdinary nestedRejects input rejected
  | argumentsRejected {input afterPath rejected : Remainder}
      {path : Syntax.QualifiedName}
      (pathParsed : PatternQualifiedNameOrdinaryParses input path afterPath)
      (rejectedArguments : OptionalConstructorArgumentsRejects afterPath
        rejected) :
      QualifiedPatternRejects nestedOrdinary nestedRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
