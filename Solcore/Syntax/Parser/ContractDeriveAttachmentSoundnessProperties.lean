import Solcore.Syntax.Parser.Contract
import Solcore.Syntax.Parser.EnumDeclSoundnessProperties

/-! Declarative transformation performed when a contract enum gains `derive`. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/--
Attaching an already parsed derive attribute changes only the enum's retained
attribute and outer start.  Its marker-to-body token derivation and final
remainder stay unchanged.
-/
theorem EnumDeclParses.withDerive
    {input output : Remainder} {declaration : Syntax.EnumDecl}
    (derive : Syntax.DeriveAttribute)
    (parsed : EnumDeclParses none input declaration output) :
    EnumDeclParses (some derive) input {
      declaration with
      span := SourceSpan.cover derive.span declaration.span
      value := {
        declaration.value with deriveAttribute := some derive
      }
    } output := by
  cases parsed with
  | parsed markerSpan markerToken nameParsed parametersParsed bodyParsed =>
      simpa [SourceSpan.cover] using
        (EnumDeclParses.parsed (deriveAttribute := some derive) markerSpan
          markerToken nameParsed parametersParsed bodyParsed)

end Solcore.Syntax.DeclarativeGrammar
