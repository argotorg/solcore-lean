import Solcore.Syntax.Parser.QualifiedNameSoundnessProperties

/-! External consumers for canonical qualified-name success soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserQualifiedNameSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @TokenKindAbsentAt
example := @finalIdentifier
example := @DottedIdentifierTailParses
example := @QualifiedNameParses
example := @symbolAbsentAt_of_isSymbol_eq_false
example := @qualifiedName_success_sound
example := @qualifiedName_success_sound_and_validFor

example (context : ParseContext) (phase : ParserPhase)
    {input next : State} {name : QualifiedName}
    (result : qualifiedName context phase input = .ok name next) :
    QualifiedNameParses input.declarativeRemainder name
      next.declarativeRemainder :=
  qualifiedName_success_sound context phase result

example (context : ParseContext) (phase : ParserPhase)
    {input next : State} {name : QualifiedName}
    (inputValid : input.ValidFor)
    (result : qualifiedName context phase input = .ok name next) :
    QualifiedNameParses input.declarativeRemainder name
        next.declarativeRemainder ∧
      name.ValidFor input.file :=
  qualifiedName_success_sound_and_validFor context phase inputValid result

end Solcore.Test.SyntaxParserQualifiedNameSoundnessProperties
