import Solcore.Syntax.Parser.FunctionParameterDiagnosticReflectionProperties
import Solcore.Syntax.Parser.PredicateSequenceDiagnosticReflectionProperties
import Solcore.Syntax.Parser.Signature
import Solcore.Syntax.Parser.TypeDiagnosticReflectionProperties

/-! Diagnostic-free reflection for non-predicate function-signature leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem requireGenericParameters_reflectsDiagnosticFreeOnSuccess
    (values : DelimitedList Identifier) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (requireGenericParameters values) := by
  intro input parameters next parsed diagnosticFree
  unfold requireGenericParameters at parsed
  cases elements : values.elements with
  | nil => simp [elements] at parsed
  | cons head tail =>
      simp only [elements, pure] at parsed
      cases parsed
      exact diagnosticFree

/-- Generic-parameter parsing cannot erase an incoming diagnostic. -/
theorem genericParameters_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess genericParameters := by
  unfold genericParameters
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimited_reflectsDiagnosticFreeOnSuccess .less .greater false
      (identifier .parameter) .parameter .topLevel
      (identifier_reflectsDiagnosticFreeOnSuccess .parameter))
  exact requireGenericParameters_reflectsDiagnosticFreeOnSuccess

/-- Optional generic-parameter parsing reflects diagnostic freedom. -/
theorem optionalGenericParameters_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess optionalGenericParameters := by
  unfold optionalGenericParameters
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro state
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      genericParameters_reflectsDiagnosticFreeOnSuccess
    intro values
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

/-- Function-parameter delimiters and elements cannot erase diagnostics. -/
theorem functionParameters_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess functionParameters := by
  unfold functionParameters
  exact delimited_reflectsDiagnosticFreeOnSuccess .leftParen .rightParen true
    namedParameter .parameter .topLevel
      namedParameter_reflectsDiagnosticFreeOnSuccess

/-- One optional hard-keyword modifier reflects diagnostic freedom. -/
theorem optionalFunctionModifier_reflectsDiagnosticFreeOnSuccess
    (keywordValue : HardKeyword) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (optionalFunctionModifier keywordValue) := by
  unfold optionalFunctionModifier
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro state
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (keyword_reflectsDiagnosticFreeOnSuccess keywordValue .parameter)
    intro marker
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

private def modifierPolicyForReflection (location : FunctionLocation)
    (keywordValue : HardKeyword) (marker : Option SourceSpan) : Parser Unit :=
  match location, marker with
  | .module, some span => emitDiagnostic {
      span
      kind := .constraintViolation (.modifierOutsideContract keywordValue)
    }
  | _, _ => pure ()

private def finishFunctionModifiersForReflection (location : FunctionLocation)
    (publicMarker payableMarker : Option SourceSpan) :
    Parser FunctionModifiers := do
  let _ ← modifierPolicyForReflection location .publicKw publicMarker
  let _ ← modifierPolicyForReflection location .payableKw payableMarker
  pure { publicMarker, payableMarker }

private theorem modifierPolicyForReflection_reflectsDiagnosticFreeOnSuccess
    (location : FunctionLocation) (keywordValue : HardKeyword)
    (marker : Option SourceSpan) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (modifierPolicyForReflection location keywordValue marker) := by
  unfold modifierPolicyForReflection
  cases location <;> cases marker
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess ()
  · exact emitDiagnostic_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess ()
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess ()

private theorem finishFunctionModifiersForReflection_reflectsDiagnosticFree
    (location : FunctionLocation) (publicMarker payableMarker : Option SourceSpan) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (finishFunctionModifiersForReflection location publicMarker
        payableMarker) := by
  unfold finishFunctionModifiersForReflection
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (modifierPolicyForReflection_reflectsDiagnosticFreeOnSuccess location
      .publicKw publicMarker)
  intro publicChecked
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (modifierPolicyForReflection_reflectsDiagnosticFreeOnSuccess location
      .payableKw payableMarker)
  intro payableChecked
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Location-policy diagnostics are only added, never erased. -/
theorem functionModifiers_reflectsDiagnosticFreeOnSuccess
    (location : FunctionLocation) :
    Parser.ReflectsDiagnosticFreeOnSuccess (functionModifiers location) := by
  unfold functionModifiers
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (optionalFunctionModifier_reflectsDiagnosticFreeOnSuccess .publicKw)
  intro publicMarker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (optionalFunctionModifier_reflectsDiagnosticFreeOnSuccess .payableKw)
  intro payableMarker
  change Parser.ReflectsDiagnosticFreeOnSuccess
    (finishFunctionModifiersForReflection location publicMarker payableMarker)
  exact finishFunctionModifiersForReflection_reflectsDiagnosticFree location
    publicMarker payableMarker

/-- Optional return-clause parsing cannot erase incoming diagnostics. -/
theorem returnClause_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess returnClause := by
  unfold returnClause
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro state
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (contextual_reflectsDiagnosticFreeOnSuccess .returns .typeExpr)
    intro marker
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (delimited_reflectsDiagnosticFreeOnSuccess .leftParen .rightParen true
        typeExpr .typeExpr .typeExpr
        typeExpr_reflectsDiagnosticFreeOnSuccess)
    intro types
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

end Solcore.Syntax.Parser
