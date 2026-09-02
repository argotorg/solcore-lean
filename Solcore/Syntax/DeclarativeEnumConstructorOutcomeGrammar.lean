import Solcore.Syntax.DeclarativeCoreTypeOutcomeGrammar

/-!
Parser-independent ordinary success and exact sequential rejection for enum
constructors and their optional tuple payloads.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary optional constructor fields reuse the exact prioritized grammar
with public Core type success. -/
abbrev OptionalEnumConstructorFieldsOrdinaryParses :=
  OptionalEnumConstructorFieldsParses

/-- A positive `(` lookahead commits optional constructor fields to the
allow-empty, no-trailing delimited attempt. -/
inductive OptionalEnumConstructorFieldsRejects :
    Remainder → Remainder → Prop where
  | present {input rejected : Remainder}
      (openingPresent : ∃ span,
        TokenAt input.tokens input.endIndex input.cursor {
          span, value := .symbol .leftParen })
      (fieldsRejected : DelimitedListRejects .leftParen .rightParen true false
        TypeExprOrdinaryParses TypeExprRejects input rejected) :
      OptionalEnumConstructorFieldsRejects input rejected

/-- Ordinary enum-constructor success is the existing exact retained grammar. -/
abbrev EnumConstructorOrdinaryParses := EnumConstructorParses

/-- Exact first rejecting stage of one enum-constructor attempt. -/
inductive EnumConstructorRejects : Remainder → Remainder → Prop where
  | nameRejected {input rejected : Remainder}
      (nameRejected : IdentifierRejects input rejected) :
      EnumConstructorRejects input rejected
  | fieldsRejected {input afterName rejected : Remainder}
      {name : Syntax.Identifier}
      (nameParsed : IdentifierParses input name afterName)
      (fieldsRejected : OptionalEnumConstructorFieldsRejects afterName
        rejected) :
      EnumConstructorRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
