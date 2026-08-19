import Solcore.Surface.Multi.Syntax

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace

/-- A closed lexical diagnostic with its exact primary source span. -/
inductive LexicalDiagnostic where
  | invalidCharacter (span : SourceSpan) (character : Char)
  | unterminatedBlockComment (span : SourceSpan)
  | unterminatedString (span : SourceSpan)
  | invalidStringEscape (span : SourceSpan) (character : Option Char)
  | unterminatedAssemblyString (span : SourceSpan)
  | unterminatedAssemblyComment (span : SourceSpan)
  | unterminatedAssemblyBlock (span : SourceSpan)
  deriving Repr, BEq, DecidableEq

/-- The closed terminal classes reported at the complete parse frontier. -/
inductive Expected where
  | hardKeyword (keyword : HardKeyword)
  | contextualKeyword (keyword : ContextualKeyword)
  | pragmaName (kind : PragmaKind)
  | symbol (symbol : Symbol)
  | identifier
  | pathComponent
  | literal
  | assemblyBlock
  | endOfFile
  deriving Repr, BEq, DecidableEq

/-- The token class found at a failing parse cursor. -/
inductive Found where
  | token (kind : TokenKind)
  | endOfFile
  deriving Repr, BEq, DecidableEq

/-- The two nonassociative infix precedence levels. -/
inductive NonAssociativeLevel where
  | relational
  | equality
  deriving Repr, BEq, DecidableEq

/-- A closed parse diagnostic with its exact primary source span. -/
inductive ParseDiagnostic where
  | unexpected
      (span : SourceSpan)
      (found : Found)
      (expected : NonemptyList Expected)
  | repeatedNonAssociative
      (span : SourceSpan)
      (level : NonAssociativeLevel)
      (operator : Located InfixOperator)
  deriving Repr, BEq, DecidableEq

/-- The two loop-control statement kinds. -/
inductive ControlKind where
  | breakControl
  | continueControl
  deriving Repr, BEq, DecidableEq

/-- Declaration positions in which a modifier can be rejected. -/
inductive ModifierContext where
  | topLevelFunction
  | classMethod
  | instanceMethod
  | fallback
  | contractConstructor
  deriving Repr, BEq, DecidableEq

/-- Declaration positions in which a parameter type is required. -/
inductive ParameterContext where
  | topLevelFunction
  | contractFunction
  | classMethod
  | instanceMethod
  | contractConstructor
  deriving Repr, BEq, DecidableEq

/-- A closed structural diagnostic with its exact primary source span. -/
inductive StructuralDiagnostic where
  | emptyImportSelection (span : SourceSpan)
  | mixedImportWildcard (span : SourceSpan)
  | duplicateImportSourceName
      (span : SourceSpan)
      (identifier : Identifier)
  | duplicateImportLocalName
      (span : SourceSpan)
      (identifier : Identifier)
  | emptyHidingClause (span : SourceSpan)
  | duplicateHiddenName
      (span : SourceSpan)
      (identifier : Identifier)
  | emptyLocalExportList (span : SourceSpan)
  | emptyRemoteExportList (span : SourceSpan)
  | mixedExportWildcard (span : SourceSpan)
  | duplicateExportName
      (span : SourceSpan)
      (identifier : Identifier)
  | duplicateExportModuleReference
      (span : SourceSpan)
      (reference : ModuleReferenceShape)
  | duplicateExportConstructor
      (span : SourceSpan)
      (identifier : Identifier)
  | matchPatternArityMismatch
      (span : SourceSpan)
      (expected : Nat)
      (actual : Nat)
  | emptyGenericPragmaTargets (span : SourceSpan)
  | duplicatePragmaTarget
      (span : SourceSpan)
      (identifier : Identifier)
  | modifierNotAllowed
      (span : SourceSpan)
      (context : ModifierContext)
      (marker : SyntaxMarker)
  | fallbackHasParameters (span : SourceSpan) (count : Nat)
  | fallbackHasNonUnitReturn (span : SourceSpan)
  | requiredParameterTypeMissing
      (span : SourceSpan)
      (context : ParameterContext)
  | controlOutsideLoop
      (span : SourceSpan)
      (control : ControlKind)
  deriving Repr, BEq, DecidableEq

/-- The first-failing parser phase and its structured diagnostic. -/
inductive SurfaceDiagnostic where
  | lexical (diagnostic : LexicalDiagnostic)
  | parse (diagnostic : ParseDiagnostic)
  | structural (diagnostic : StructuralDiagnostic)
  deriving Repr, BEq, DecidableEq

namespace LexicalDiagnostic

/-- The exact primary span of a lexical diagnostic. -/
def span : LexicalDiagnostic → SourceSpan
  | .invalidCharacter span _ => span
  | .unterminatedBlockComment span => span
  | .unterminatedString span => span
  | .invalidStringEscape span _ => span
  | .unterminatedAssemblyString span => span
  | .unterminatedAssemblyComment span => span
  | .unterminatedAssemblyBlock span => span

/-- The stable code assigned to a lexical diagnostic constructor. -/
def code : LexicalDiagnostic → String
  | .invalidCharacter _ _ => "MSL0001"
  | .unterminatedBlockComment _ => "MSL0002"
  | .unterminatedString _ => "MSL0003"
  | .invalidStringEscape _ _ => "MSL0004"
  | .unterminatedAssemblyString _ => "MSL0005"
  | .unterminatedAssemblyComment _ => "MSL0006"
  | .unterminatedAssemblyBlock _ => "MSL0007"

end LexicalDiagnostic

namespace ParseDiagnostic

/-- The exact primary span of a parse diagnostic. -/
def span : ParseDiagnostic → SourceSpan
  | .unexpected span _ _ => span
  | .repeatedNonAssociative span _ _ => span

/-- The stable code assigned to a parse diagnostic constructor. -/
def code : ParseDiagnostic → String
  | .unexpected _ _ _ => "MSP0001"
  | .repeatedNonAssociative _ _ _ => "MSP0002"

end ParseDiagnostic

namespace StructuralDiagnostic

/-- The exact primary span of a structural diagnostic. -/
def span : StructuralDiagnostic → SourceSpan
  | .emptyImportSelection span => span
  | .mixedImportWildcard span => span
  | .duplicateImportSourceName span _ => span
  | .duplicateImportLocalName span _ => span
  | .emptyHidingClause span => span
  | .duplicateHiddenName span _ => span
  | .emptyLocalExportList span => span
  | .emptyRemoteExportList span => span
  | .mixedExportWildcard span => span
  | .duplicateExportName span _ => span
  | .duplicateExportModuleReference span _ => span
  | .duplicateExportConstructor span _ => span
  | .matchPatternArityMismatch span _ _ => span
  | .emptyGenericPragmaTargets span => span
  | .duplicatePragmaTarget span _ => span
  | .modifierNotAllowed span _ _ => span
  | .fallbackHasParameters span _ => span
  | .fallbackHasNonUnitReturn span => span
  | .requiredParameterTypeMissing span _ => span
  | .controlOutsideLoop span _ => span

/-- The stable code assigned to a structural diagnostic constructor. -/
def code : StructuralDiagnostic → String
  | .emptyImportSelection _ => "MSS0001"
  | .mixedImportWildcard _ => "MSS0002"
  | .duplicateImportSourceName _ _ => "MSS0003"
  | .duplicateImportLocalName _ _ => "MSS0004"
  | .emptyHidingClause _ => "MSS0005"
  | .duplicateHiddenName _ _ => "MSS0006"
  | .emptyLocalExportList _ => "MSS0007"
  | .emptyRemoteExportList _ => "MSS0008"
  | .mixedExportWildcard _ => "MSS0009"
  | .duplicateExportName _ _ => "MSS0010"
  | .duplicateExportModuleReference _ _ => "MSS0011"
  | .duplicateExportConstructor _ _ => "MSS0012"
  | .matchPatternArityMismatch _ _ _ => "MSS0013"
  | .emptyGenericPragmaTargets _ => "MSS0014"
  | .duplicatePragmaTarget _ _ => "MSS0015"
  | .modifierNotAllowed _ _ _ => "MSS0016"
  | .fallbackHasParameters _ _ => "MSS0017"
  | .fallbackHasNonUnitReturn _ => "MSS0018"
  | .requiredParameterTypeMissing _ _ => "MSS0019"
  | .controlOutsideLoop _ _ => "MSS0020"

end StructuralDiagnostic

/-- The total exact primary-span projection for every surface diagnostic. -/
def diagnosticSpan : SurfaceDiagnostic → SourceSpan
  | .lexical diagnostic => diagnostic.span
  | .parse diagnostic => diagnostic.span
  | .structural diagnostic => diagnostic.span

/-- The total structured source-identity projection for every diagnostic. -/
def diagnosticSource (diagnostic : SurfaceDiagnostic) : SourceId :=
  (diagnosticSpan diagnostic).source

/-- The total stable-code projection for every surface diagnostic. -/
def diagnosticCode : SurfaceDiagnostic → String
  | .lexical diagnostic => diagnostic.code
  | .parse diagnostic => diagnostic.code
  | .structural diagnostic => diagnostic.code

end Solcore.Surface.Multi
