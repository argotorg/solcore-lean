import Solcore.Syntax.Parser.ContractEntry
import Solcore.Syntax.Parser.FunctionParameterDiagnosticReflectionProperties
import Solcore.Syntax.Parser.SignatureLeafDiagnosticReflectionProperties

/-! Backward diagnostic reflection for constructor and fallback entry leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ContractEntryInternals

/-- Contract-entry parameter parsing cannot erase incoming diagnostics. -/
theorem entryParameters_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess entryParameters := by
  simpa [entryParameters, functionParameters] using
    functionParameters_reflectsDiagnosticFreeOnSuccess

/-- One optional entry modifier cannot erase incoming diagnostics. -/
theorem optionalModifier_reflectsDiagnosticFreeOnSuccess
    (modifier : HardKeyword) :
    Parser.ReflectsDiagnosticFreeOnSuccess (optionalModifier modifier) := by
  unfold optionalModifier
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (keyword_reflectsDiagnosticFreeOnSuccess modifier .contractMember)
    intro marker
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

/--
Implicit-public validation and its following optional payable marker never
remove diagnostics.  An explicit `public` success is therefore incompatible
with a diagnostic-free result.
-/
theorem implicitPublicModifiers_reflectsDiagnosticFreeOnSuccess
    (declaration : HardKeyword) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (implicitPublicModifiers declaration) := by
  unfold implicitPublicModifiers
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (optionalModifier_reflectsDiagnosticFreeOnSuccess .publicKw)
  intro publicMarker
  cases publicMarker with
  | none =>
      exact optionalModifier_reflectsDiagnosticFreeOnSuccess .payableKw
  | some span =>
      apply Parser.bind_reflectsDiagnosticFreeOnSuccess
        (emitDiagnostic_reflectsDiagnosticFreeOnSuccess _)
      intro emitted
      exact optionalModifier_reflectsDiagnosticFreeOnSuccess .payableKw

end ContractEntryInternals

/-- Constructor parsing reflects diagnostic freedom through its required body. -/
theorem constructorDecl_reflectsDiagnosticFreeOnSuccess
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require))) :
    Parser.ReflectsDiagnosticFreeOnSuccess constructorDecl := by
  unfold constructorDecl
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .constructorKw .contractMember)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    ContractEntryInternals.entryParameters_reflectsDiagnosticFreeOnSuccess
  intro parameters
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (ContractEntryInternals.implicitPublicModifiers_reflectsDiagnosticFreeOnSuccess
      .constructorKw)
  intro payableMarker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess bodyReflects
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Fallback validation and parsing reflect diagnostic freedom through the body. -/
theorem fallbackDecl_reflectsDiagnosticFreeOnSuccess
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require))) :
    Parser.ReflectsDiagnosticFreeOnSuccess fallbackDecl := by
  unfold fallbackDecl
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .fallbackKw .contractMember)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    ContractEntryInternals.entryParameters_reflectsDiagnosticFreeOnSuccess
  intro parameters
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (ContractEntryInternals.implicitPublicModifiers_reflectsDiagnosticFreeOnSuccess
        .fallbackKw)
    intro payableMarker
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess bodyReflects
    intro body
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (emitDiagnostic_reflectsDiagnosticFreeOnSuccess _)
    intro emitted
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (ContractEntryInternals.implicitPublicModifiers_reflectsDiagnosticFreeOnSuccess
        .fallbackKw)
    intro payableMarker
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess bodyReflects
    intro body
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser
