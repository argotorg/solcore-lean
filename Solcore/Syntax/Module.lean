import Solcore.Syntax.Term
import Solcore.Syntax.NameValidity

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

/-- Export name accepted both locally and after a remote module path. -/
inductive ExportNameValue where
  | wildcard (marker : SourceSpan)
  | identifier
      (name : Identifier)
      (constructors : Option ConstructorSelection)
  | operator (spelling : SpannedText)
  deriving Repr, BEq, DecidableEq

abbrev ExportName := Located ExportNameValue

/-- Entry accepted only in a current-module `export { ... }` list. -/
inductive LocalExportItemValue where
  | name (name : ExportName)
  | moduleWildcard (modulePath : QualifiedName) (marker : SourceSpan)
  deriving Repr, BEq, DecidableEq

abbrev LocalExportItem := Located LocalExportItemValue

/-- Selection suffix of `export Module.*` or `export Module.{...}`. -/
inductive ExportSelectionValue where
  | wildcard (marker : SourceSpan)
  | selected (items : DelimitedList ExportName)
  deriving Repr, BEq, DecidableEq

abbrev ExportSelection := Located ExportSelectionValue

/-- Complete canonical export declaration payload. -/
inductive ExportDeclValue where
  | local (items : DelimitedList LocalExportItem)
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

/-!
## Consolidated module: `Solcore.Syntax.ModuleValidity`
-/

/-! Source-validity contracts for canonical modules, imports, and exports. -/

set_option autoImplicit false

namespace Solcore.Syntax

namespace ModulePath

/-- Every range retained by a module path belongs to one source. -/
def ValidFor (file : SourceFile) (path : ModulePath) : Prop :=
  path.span.ValidFor file ∧
    (match path.value.externalMarker with
    | some marker => marker.ValidFor file
    | none => True) ∧
    ∀ component ∈ path.value.components.toList,
      component.span.ValidFor file

end ModulePath

namespace SelectorName

/-- A selector and its optional identifier payload belong to one source. -/
def ValidFor (file : SourceFile) (selector : SelectorName) : Prop :=
  selector.span.ValidFor file ∧
    match selector.value with
    | .identifier name => name.span.ValidFor file
    | .operator _ => True

end SelectorName

namespace SelectedImport

/-- A selected import retains valid source and alias ranges. -/
def ValidFor (file : SourceFile) (selection : SelectedImport) : Prop :=
  selection.span.ValidFor file ∧
    selection.value.source.ValidFor file ∧
    ∀ alias ∈ selection.value.alias, alias.span.ValidFor file

end SelectedImport

namespace HidingClause

/-- A hiding clause and all of its selector names belong to one source. -/
def ValidFor (file : SourceFile) (clause : HidingClause) : Prop :=
  clause.span.ValidFor file ∧
    ∀ name ∈ clause.value.names.toList, SelectorName.ValidFor file name

end HidingClause

namespace ImportDecl

/-- Every range retained by a complete import declaration is valid. -/
def ValidFor (file : SourceFile) (declaration : ImportDecl) : Prop :=
  declaration.span.ValidFor file ∧
    match declaration.value with
    | .plain modulePath => ModulePath.ValidFor file modulePath
    | .namespace modulePath alias =>
        ModulePath.ValidFor file modulePath ∧ alias.span.ValidFor file
    | .wildcard modulePath hidingClause =>
        ModulePath.ValidFor file modulePath ∧
          ∀ clause ∈ hidingClause, HidingClause.ValidFor file clause
    | .selected selection modulePath hidingClause =>
        selection.span.ValidFor file ∧
          (∀ item ∈ selection.elements.toList,
            SelectedImport.ValidFor file item) ∧
          ModulePath.ValidFor file modulePath ∧
          ∀ clause ∈ hidingClause, HidingClause.ValidFor file clause

end ImportDecl

namespace ConstructorSelection

/-- Every marker or constructor name in an export selection is valid. -/
def ValidFor (file : SourceFile) (selection : ConstructorSelection) : Prop :=
  selection.span.ValidFor file ∧
    match selection.value with
    | .all marker => marker.ValidFor file
    | .named constructors => ∀ constructor ∈ constructors.toList,
        constructor.span.ValidFor file

end ConstructorSelection

namespace ExportName

/-- Every range retained by an exported name belongs to one source. -/
def ValidFor (file : SourceFile) (name : ExportName) : Prop :=
  name.span.ValidFor file ∧
    match name.value with
    | .wildcard marker => marker.ValidFor file
    | .identifier identifier constructors =>
        identifier.span.ValidFor file ∧
          ∀ selection ∈ constructors,
            ConstructorSelection.ValidFor file selection
    | .operator spelling => spelling.span.ValidFor file

end ExportName

namespace LocalExportItem

/-- Every range retained by a local export item is source-valid. -/
def ValidFor (file : SourceFile) (item : LocalExportItem) : Prop :=
  item.span.ValidFor file ∧
    match item.value with
    | .name name => ExportName.ValidFor file name
    | .moduleWildcard modulePath marker =>
        QualifiedName.ValidFor file modulePath ∧ marker.ValidFor file

end LocalExportItem

namespace ExportSelection

/-- A remote export suffix retains valid wildcard or selected-name ranges. -/
def ValidFor (file : SourceFile) (selection : ExportSelection) : Prop :=
  selection.span.ValidFor file ∧
    match selection.value with
    | .wildcard marker => marker.ValidFor file
    | .selected items =>
        items.span.ValidFor file ∧
          ∀ item ∈ items.elements, ExportName.ValidFor file item

end ExportSelection

namespace ExportDecl

/-- Every range retained by a complete export declaration is valid. -/
def ValidFor (file : SourceFile) (declaration : ExportDecl) : Prop :=
  declaration.span.ValidFor file ∧
    match declaration.value with
    | .local items =>
        items.span.ValidFor file ∧
          ∀ item ∈ items.elements, LocalExportItem.ValidFor file item
    | .module modulePath => QualifiedName.ValidFor file modulePath
    | .moduleAs modulePath alias =>
        QualifiedName.ValidFor file modulePath ∧ alias.span.ValidFor file
    | .itemsFrom modulePath selection =>
        QualifiedName.ValidFor file modulePath ∧
          ExportSelection.ValidFor file selection

end ExportDecl

namespace PragmaDecl

/-- Every range retained by a pragma declaration belongs to one source. -/
def ValidFor (file : SourceFile) (declaration : PragmaDecl) : Prop :=
  declaration.span.ValidFor file ∧
    declaration.value.name.span.ValidFor file ∧
    ∀ item ∈ declaration.value.items, item.span.ValidFor file

end PragmaDecl

end Solcore.Syntax
