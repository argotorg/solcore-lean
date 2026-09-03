import Solcore.Syntax.DeclarativeEnumBodyExactnessProperties
import Solcore.Syntax.DeclarativeEnumDeclarationOutcomeProperties
import Solcore.Syntax.DeclarativeGenericParametersExactnessProperties

/-! Exact values and rejection endpoints for complete enum declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem enumDecl_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- At any fixed supplied derive attribute, successful enum declarations fix
their complete AST. -/
theorem EnumDeclOrdinaryParses.value_unique
    (deriveAttribute : Option Syntax.DeriveAttribute)
    {input : Remainder} {left right : Syntax.EnumDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : EnumDeclOrdinaryParses deriveAttribute input left afterLeft)
    (rightParsed : EnumDeclOrdinaryParses deriveAttribute input right
      afterRight) : left = right := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftName leftParameters leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightName rightParameters
          rightBody =>
          rcases leftMarker.result_unique rightMarker with
            ⟨markerSpanEq, afterMarkerEq⟩
          subst markerSpanEq
          subst afterMarkerEq
          rcases identifierExactOutcomeSpec.successResultUnique leftName
              rightName with ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          rcases optionalGenericParametersExactOutcomeSpec.successResultUnique
              leftParameters rightParameters with
            ⟨parametersEq, afterParametersEq⟩
          subst parametersEq
          subst afterParametersEq
          rcases EnumBodyOrdinaryParses.result_unique leftBody rightBody with
            ⟨bodySpanEq, constructorsEq, afterBodyEq⟩
          subst bodySpanEq
          subst constructorsEq
          rfl

/-- At any fixed supplied derive attribute, successful enum declarations fix
their AST and final remainder. -/
theorem EnumDeclOrdinaryParses.result_unique
    (deriveAttribute : Option Syntax.DeriveAttribute)
    {input : Remainder} {left right : Syntax.EnumDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : EnumDeclOrdinaryParses deriveAttribute input left afterLeft)
    (rightParsed : EnumDeclOrdinaryParses deriveAttribute input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique deriveAttribute rightParsed,
    leftParsed.output_unique deriveAttribute rightParsed⟩

/-- The four-stage enum-declaration rejection sequence has one endpoint. -/
theorem EnumDeclRejects.output_unique
    {input left right : Remainder}
    (leftRejected : EnumDeclRejects input left)
    (rightRejected : EnumDeclRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind (ematch := 10) [enumDecl_absent_conflicts_exact,
      ExactTokenParses.output_unique,
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique,
      optionalGenericParametersExactOutcomeSpec.successOutputUnique,
      optionalGenericParametersExactOutcomeSpec.successRejectDisjoint,
      optionalGenericParametersExactOutcomeSpec.rejectOutputUnique,
      enumBodyExactOutcomeSpec.successOutputUnique,
      enumBodyExactOutcomeSpec.successRejectDisjoint,
      enumBodyExactOutcomeSpec.rejectOutputUnique]

/-- For every fixed supplied derive attribute, complete enum declarations have
fully exact ordinary outcomes. -/
theorem enumDeclExactOutcomeSpec
    (deriveAttribute : Option Syntax.DeriveAttribute) :
    ExactDeterministicOutcomeSpec (EnumDeclOrdinaryParses deriveAttribute)
      EnumDeclRejects where
  toDeterministicOutcomeSpec :=
    enumDeclDeterministicOutcomeSpec deriveAttribute
  successValueUnique :=
    EnumDeclOrdinaryParses.value_unique deriveAttribute
  rejectOutputUnique := EnumDeclRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
