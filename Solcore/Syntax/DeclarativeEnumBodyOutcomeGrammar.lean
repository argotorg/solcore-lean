import Solcore.Syntax.DeclarativeEnumConstructorOutcomeGrammar

/-! Parser-independent ordinary outcomes for canonical enum bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary enum-body success is the existing exact possibly-empty,
trailing-comma grammar. -/
abbrev EnumBodyOrdinaryParses := EnumBodyParses

/-- Single-output adapter retaining the body span and constructor list. -/
def EnumBodyOrdinaryOutcomeParses (input : Remainder)
    (body : SourceSpan × List Syntax.EnumConstructor)
    (output : Remainder) : Prop :=
  EnumBodyOrdinaryParses input body.1 body.2 output

/-- Exact rejection of the allow-empty, allow-trailing enum body. -/
abbrev EnumBodyRejects :=
  DelimitedListRejects .leftBrace .rightBrace true true
    EnumConstructorOrdinaryParses EnumConstructorRejects

end Solcore.Syntax.DeclarativeGrammar
