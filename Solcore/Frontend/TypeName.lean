import Solcore.Core.Syntax
import Solcore.Syntax.Type

/-! Explicit interpretation of canonical named types without type arguments.
Qualified spelling components remain separate, and no spelling is reserved. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Ordered caller meanings for exact qualified spelling-component lists. -/
abbrev TypeNameTable := List (List String × Core.Ty)

namespace TypeNameTable

def lookup? : TypeNameTable → List String → Option Core.Ty
  | [], _ => none
  | (candidate, type) :: table, key =>
      if candidate = key then some type else lookup? table key

/-- The first matching key determines meaning, independently of `lookup?`. -/
inductive Lookup : TypeNameTable → List String → Core.Ty → Prop where
  | head {table : TypeNameTable} {key : List String} {type : Core.Ty} :
      Lookup ((key, type) :: table) key type
  | tail {table : TypeNameTable} {key candidate : List String}
      {type candidateType : Core.Ty}
      (different : candidate ≠ key) (found : Lookup table key type) :
      Lookup ((candidate, candidateType) :: table) key type

end TypeNameTable

/-- Exact component strings in written order; occurrence ranges are ignored. -/
def qualifiedTypeNameKey (name : Syntax.QualifiedName) : List String :=
  name.value.components.toList.map (·.value)

/-- `none` means unmapped or outside this adapter, not general source invalidity. -/
def interpretTypeName? (table : TypeNameTable) (source : Syntax.TypeExpr) : Option Core.Ty :=
  match source with
  | ⟨_, .named name none⟩ => table.lookup? (qualifiedTypeNameKey name)
  | _ => none

/-- Independent canonical meaning for this deliberately restricted type fragment. -/
inductive TypeNameDenotes (table : TypeNameTable) : Syntax.TypeExpr → Core.Ty → Prop where
  | named {span : Syntax.SourceSpan} {name : Syntax.QualifiedName} {type : Core.Ty}
      (found : TypeNameTable.Lookup table (qualifiedTypeNameKey name) type) :
      TypeNameDenotes table ⟨span, .named name none⟩ type

end Solcore.Frontend
