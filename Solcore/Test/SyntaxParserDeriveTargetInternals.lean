import Solcore.Syntax.Parser.Derive

/-! External compile consumers for proof-visible derive-target internals. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDeriveTargetInternals

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.DeriveTargetInternals

example : reservedDeriveKeyword? (.keyword .contractKw) =
    some .contractKw := rfl

example : reservedDeriveKeyword? (.keyword .returnKw) = none := rfl

example : reservedDeriveKeyword? (.identifier "Trait") = none := rfl

example : Parser Identifier := deriveComponent

example (first last : Identifier) (tailRev : List Identifier) :
    Parser DeriveTarget := finishDeriveTarget first last tailRev

example (first : Identifier) :
    Nat → Identifier → List Identifier → State → Reply DeriveTarget :=
  deriveTargetTail first

example (first last : Identifier) (tailRev : List Identifier)
    (state : State) :
    finishDeriveTarget first last tailRev state = .ok {
      span := SourceSpan.cover first.span last.span
      value := {
        components := {
          head := first
          tail := tailRev.reverse
        }
      }
    } state := rfl

end Solcore.Test.SyntaxParserDeriveTargetInternals
