import Solcore.Syntax.Parser.Enum
import Solcore.Syntax.Parser.FunctionParameterDiagnosticReflectionProperties
import Solcore.Syntax.Parser.SignatureLeafDiagnosticReflectionProperties
import Solcore.Syntax.Parser.TypeAliasRecoveryDiagnosticProperties

/-! Backward diagnostic reflection for alias and enum declaration leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace TypeAliasInternals

/-- Alias-value recovery cannot make a diagnostic-free success. -/
theorem parseAliasValue_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess parseAliasValue := by
  intro input value next result diagnosticFree
  unfold parseAliasValue at result
  cases coreResult : typeExpr input with
  | ok parsed afterCore =>
      simp only [coreResult] at result
      cases result
      exact typeExpr_reflectsDiagnosticFreeOnSuccess input value next
        coreResult diagnosticFree
  | reject failure failedState =>
      simp only [coreResult] at result
      change (if ({ failedState with cursor := input.cursor } : State).atEnd ||
          isSymbol { failedState with cursor := input.cursor } .semicolon then
          .reject failure { failedState with cursor := input.cursor }
        else recoverTypeAliasValue
          (({ failedState with cursor := input.cursor } : State).emit
            failure.toDiagnostic)) = .ok value next at result
      split at result
      · contradiction
      · exact False.elim
          (recoverTypeAliasValue_diagnostics_ne_nil_onSuccess result
            diagnosticFree)
  | invariant error => simp [coreResult] at result

end TypeAliasInternals

/-- Optional type-alias parameters cannot erase diagnostics. -/
theorem parseTypeAliasParameters_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess parseTypeAliasParameters := by
  unfold parseTypeAliasParameters
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (delimited_reflectsDiagnosticFreeOnSuccess .leftParen .rightParen true
        (identifier .parameter) .typeAlias .typeAlias
        (identifier_reflectsDiagnosticFreeOnSuccess .parameter))
    intro parameters
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

/-- Complete type-alias parsing cannot erase incoming diagnostics. -/
theorem typeAlias_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess typeAlias := by
  unfold typeAlias
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .typeKw .typeAlias)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (identifier_reflectsDiagnosticFreeOnSuccess .typeAlias)
  intro name
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    parseTypeAliasParameters_reflectsDiagnosticFreeOnSuccess
  intro parameters
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .equal .typeAlias)
  intro equal
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    TypeAliasInternals.parseAliasValue_reflectsDiagnosticFreeOnSuccess
  intro value
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .semicolon .typeAlias)
  intro semicolon
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

namespace EnumInternals

/-- Optional enum payload parsing cannot erase incoming diagnostics. -/
theorem enumConstructorFields_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess enumConstructorFields := by
  unfold enumConstructorFields
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (delimitedNoTrailing_reflectsDiagnosticFreeOnSuccess
        .leftParen .rightParen true typeExpr .typeExpr .topLevel
        typeExpr_reflectsDiagnosticFreeOnSuccess)
    intro fields
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

/-- One enum constructor cannot erase incoming diagnostics. -/
theorem enumConstructor_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess enumConstructor := by
  unfold enumConstructor
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (identifier_reflectsDiagnosticFreeOnSuccess .topItem)
  intro name
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    enumConstructorFields_reflectsDiagnosticFreeOnSuccess
  intro fields
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem closeEnumBody_reflectsDiagnosticFreeOnSuccess
    (opening : Token) (constructorsRev : List EnumConstructor) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (closeEnumBody opening constructorsRev) := by
  unfold closeEnumBody
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .rightBrace .topItem)
  intro closing
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem enumConstructors_reflectsDiagnosticFreeOnSuccess
    (opening : Token) : ∀ fuel constructorsRev,
    Parser.ReflectsDiagnosticFreeOnSuccess
      (enumConstructors opening fuel constructorsRev) := by
  intro fuel
  induction fuel with
  | zero => intro constructorsRev input body next result diagnosticFree
            simp [enumConstructors] at result
  | succ fuel inductionHypothesis =>
      intro constructorsRev input body next result diagnosticFree
      unfold enumConstructors at result
      split at result
      · cases commaResult : symbol .comma .topItem input with
        | invariant error => simp [commaResult] at result
        | reject failure rejected => simp [commaResult] at result
        | ok comma afterComma =>
            simp only [commaResult] at result
            split at result
            · have afterCommaFree :=
                closeEnumBody_reflectsDiagnosticFreeOnSuccess opening
                  constructorsRev afterComma body next result diagnosticFree
              exact symbol_reflectsDiagnosticFreeOnSuccess .comma .topItem
                input comma afterComma commaResult afterCommaFree
            · cases constructorResult : enumConstructor afterComma with
              | invariant error => simp [constructorResult] at result
              | reject failure rejected => simp [constructorResult] at result
              | ok constructor afterConstructor =>
                  simp only [constructorResult] at result
                  split at result
                  · have afterConstructorFree := inductionHypothesis
                      (constructor :: constructorsRev) afterConstructor body
                        next result diagnosticFree
                    have afterCommaFree :=
                      enumConstructor_reflectsDiagnosticFreeOnSuccess
                        afterComma constructor afterConstructor
                          constructorResult afterConstructorFree
                    exact symbol_reflectsDiagnosticFreeOnSuccess .comma
                      .topItem input comma afterComma commaResult afterCommaFree
                  · contradiction
      · exact closeEnumBody_reflectsDiagnosticFreeOnSuccess opening
          constructorsRev input body next result diagnosticFree

/-- Complete enum-body parsing cannot erase incoming diagnostics. -/
theorem enumBody_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess enumBody := by
  intro input body next result diagnosticFree
  unfold enumBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      split at result
      · have afterOpeningFree :=
          closeEnumBody_reflectsDiagnosticFreeOnSuccess opening []
            afterOpening body next result diagnosticFree
        exact symbol_reflectsDiagnosticFreeOnSuccess .leftBrace .topItem
          input opening afterOpening openingResult afterOpeningFree
      · cases constructorResult : enumConstructor afterOpening with
        | invariant error => simp [constructorResult] at result
        | reject failure rejected => simp [constructorResult] at result
        | ok constructor afterConstructor =>
            simp only [constructorResult] at result
            have afterConstructorFree :=
              enumConstructors_reflectsDiagnosticFreeOnSuccess opening
                (afterConstructor.remainingCount + 1) [constructor]
                  afterConstructor body next result diagnosticFree
            have afterOpeningFree :=
              enumConstructor_reflectsDiagnosticFreeOnSuccess afterOpening
                constructor afterConstructor constructorResult
                  afterConstructorFree
            exact symbol_reflectsDiagnosticFreeOnSuccess .leftBrace .topItem
              input opening afterOpening openingResult afterOpeningFree

end EnumInternals

/-- Complete enum parsing cannot erase incoming diagnostics. -/
theorem enumDecl_reflectsDiagnosticFreeOnSuccess
    (deriveAttribute : Option DeriveAttribute) :
    Parser.ReflectsDiagnosticFreeOnSuccess (enumDecl deriveAttribute) := by
  unfold enumDecl
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (contextual_reflectsDiagnosticFreeOnSuccess .enum .topItem)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (identifier_reflectsDiagnosticFreeOnSuccess .topItem)
  intro name
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    optionalGenericParameters_reflectsDiagnosticFreeOnSuccess
  intro parameters
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    EnumInternals.enumBody_reflectsDiagnosticFreeOnSuccess
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser
