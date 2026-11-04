import Solcore.Syntax.Parser.Signatures
import Solcore.Syntax.Parser.Internal.ParameterBasics
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Parser.Internal.TypeBasics
import Solcore.Syntax.Validity
import Solcore.Syntax.Parser.FunctionParameterDiagnosticReflectionProperties
import Solcore.Syntax.Parser.PredicateSequenceDiagnosticReflectionProperties
import Solcore.Syntax.Parser.TypeDiagnosticReflectionProperties

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A generic parameter list starts at its opening angle bracket. -/
theorem genericParameters_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess genericParameters (·.span) := by
  unfold genericParameters
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (delimited_startsAtCurrentTokenOnSuccess .less .greater false
      (identifier .parameter) .parameter .topLevel)
  intro values input result next parsed
  unfold requireGenericParameters at parsed
  cases elements : values.elements with
  | nil =>
      simp only [elements] at parsed
      contradiction
  | cons head tail =>
      simp only [elements] at parsed
      cases parsed
      rfl

/-- Complete function signatures retain only source-valid syntax. -/
theorem functionSignature_validFor (location : FunctionLocation) :
    (functionSignature location).ValidFor FunctionSignature.ValidFor :=
  functionSignature_validFor_of_span location whereClause_validFor
    (fun _ _ _ inputValid parsed =>
      functionSignature_span_validOnSuccess location inputValid parsed)

/-- Complete signatures preserve token windows when `where` parsing does. -/
theorem functionSignature_preservesTokenWindow_of_where (location : FunctionLocation)
    (whereWindow : Parser.PreservesTokenWindow whereClause) :
    Parser.PreservesTokenWindow (functionSignature location) := by
  unfold functionSignature
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .functionKw .topItem)
  intro functionToken
  apply Parser.bind_preservesTokenWindow
    (identifier_preservesTokenWindow .topItem)
  intro name
  apply Parser.bind_preservesTokenWindow
    optionalGenericParameters_preservesTokenWindow
  intro genericParameters
  apply Parser.bind_preservesTokenWindow functionParameters_preservesTokenWindow
  intro parameters
  apply Parser.bind_preservesTokenWindow
    (functionModifiers_preservesTokenWindow location)
  intro modifiers
  apply Parser.bind_preservesTokenWindow returnClause_preservesTokenWindow
  intro returnsClause
  apply Parser.bind_preservesTokenWindow whereWindow
  intro parsedWhereClause
  exact Parser.pure_preservesTokenWindow _

theorem functionSignature_preservesTokensOnSuccess_of_where
    (location : FunctionLocation)
    (whereWindow : Parser.PreservesTokenWindow whereClause) :
    Parser.PreservesTokensOnSuccess (functionSignature location) :=
  (functionSignature_preservesTokenWindow_of_where location whereWindow
    ).preservesTokensOnSuccess

/-- Complete signatures never rewind when `where` parsing is monotone. -/
theorem functionSignature_cursorMonotoneOnSuccess_of_where
    (location : FunctionLocation)
    (whereCursor : Parser.CursorMonotoneOnSuccess whereClause) :
    Parser.CursorMonotoneOnSuccess (functionSignature location) := by
  unfold functionSignature
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .functionKw .topItem)
  intro functionToken
  apply Parser.bind_cursorMonotoneOnSuccess
    (identifier_cursorMonotoneOnSuccess .topItem)
  intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    optionalGenericParameters_cursorMonotoneOnSuccess
  intro genericParameters
  apply Parser.bind_cursorMonotoneOnSuccess
    functionParameters_cursorMonotoneOnSuccess
  intro parameters
  apply Parser.bind_cursorMonotoneOnSuccess
    (functionModifiers_cursorMonotoneOnSuccess location)
  intro modifiers
  apply Parser.bind_cursorMonotoneOnSuccess
    returnClause_cursorMonotoneOnSuccess
  intro returnsClause
  apply Parser.bind_cursorMonotoneOnSuccess whereCursor
  intro parsedWhereClause
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- Complete signatures preserve token windows. -/
theorem functionSignature_preservesTokenWindow (location : FunctionLocation) :
    Parser.PreservesTokenWindow (functionSignature location) :=
  functionSignature_preservesTokenWindow_of_where location
    whereClause_preservesTokenWindow

theorem functionSignature_preservesTokensOnSuccess
    (location : FunctionLocation) :
    Parser.PreservesTokensOnSuccess (functionSignature location) :=
  (functionSignature_preservesTokenWindow location).preservesTokensOnSuccess

/-- Complete signatures never rewind. -/
theorem functionSignature_cursorMonotoneOnSuccess
    (location : FunctionLocation) :
    Parser.CursorMonotoneOnSuccess (functionSignature location) :=
  functionSignature_cursorMonotoneOnSuccess_of_where location
    whereClause_cursorMonotoneOnSuccess

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.SignatureLeafDiagnosticReflectionProperties`
-/

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
