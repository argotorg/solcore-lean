import Solcore.Syntax.Term

set_option autoImplicit false

namespace Solcore.Syntax

/-- Dotted source module name, optionally rooted in an external package. -/
structure ModulePathValue where
  externalMarker : Option SourceSpan
  components : NonemptyList Identifier
  deriving Repr, BEq, DecidableEq

abbrev ModulePath := Located ModulePathValue

/-- Name accepted in an import or export selector. -/
inductive SelectorNameValue where
  | identifier (name : Identifier)
  | operator (spelling : String)
  deriving Repr, BEq, DecidableEq

abbrev SelectorName := Located SelectorNameValue

/-- One named import and its optional local alias. -/
structure SelectedImportValue where
  source : SelectorName
  alias : Option Identifier
  deriving Repr, BEq, DecidableEq

abbrev SelectedImport := Located SelectedImportValue

/-- Nonempty trailing `hiding { ... }` clause. -/
structure HidingClauseValue where
  names : NonemptyList SelectorName
  deriving Repr, BEq, DecidableEq

abbrev HidingClause := Located HidingClauseValue

/-- Complete canonical import declaration payload. -/
inductive ImportDeclValue where
  | plain (modulePath : ModulePath)
  | namespace
      (modulePath : ModulePath)
      (alias : Identifier)
  | wildcard
      (modulePath : ModulePath)
      (hidingClause : Option HidingClause)
  | selected
      (selection : NonemptyDelimitedList SelectedImport)
      (modulePath : ModulePath)
      (hidingClause : Option HidingClause)
  deriving Repr, BEq, DecidableEq

abbrev ImportDecl := Located ImportDeclValue

/-- Constructor selection attached to one exported type name. -/
inductive ConstructorSelectionValue where
  | all (marker : SourceSpan)
  | named (constructors : NonemptyList Identifier)
  deriving Repr, BEq, DecidableEq

abbrev ConstructorSelection := Located ConstructorSelectionValue

/-- One entry in a local or remote export list. -/
inductive ExportItemValue where
  | wildcard (marker : SourceSpan)
  | named
      (name : SelectorName)
      (constructors : Option ConstructorSelection)
  | moduleWildcard (modulePath : QualifiedName) (marker : SourceSpan)
  deriving Repr, BEq, DecidableEq

abbrev ExportItem := Located ExportItemValue

/-- Selection suffix of `export Module.*` or `export Module.{...}`. -/
inductive ExportSelectionValue where
  | wildcard (marker : SourceSpan)
  | selected (items : DelimitedList ExportItem)
  deriving Repr, BEq, DecidableEq

abbrev ExportSelection := Located ExportSelectionValue

/-- Complete canonical export declaration payload. -/
inductive ExportDeclValue where
  | local (items : DelimitedList ExportItem)
  | module (modulePath : QualifiedName)
  | moduleAs
      (modulePath : QualifiedName)
      (alias : Identifier)
  | itemsFrom
      (modulePath : QualifiedName)
      (selection : ExportSelection)
  deriving Repr, BEq, DecidableEq

abbrev ExportDecl := Located ExportDeclValue

/-- Provisional pragma syntax implemented by the pinned Rust parser. -/
structure PragmaDeclValue where
  name : SpannedText
  items : List Identifier
  deriving Repr, BEq, DecidableEq

abbrev PragmaDecl := Located PragmaDeclValue

end Solcore.Syntax
