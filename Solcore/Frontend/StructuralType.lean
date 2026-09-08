import Solcore.Frontend.TypeName

/-! An opt-in structural type fragment over the original canonical syntax.
Named-only interpretation and existing parameter/header/let gates stay unchanged. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Exact named leaves, nullary Unit, singleton identity and ordered binary products.
Larger lists and other type constructors are outside this restricted adapter. -/
def interpretStructuralType? (table : TypeNameTable) (source : Syntax.TypeExpr) : Option Core.Ty :=
  match source with
  | ⟨_, .named name none⟩ => table.lookup? (qualifiedTypeNameKey name)
  | ⟨_, .tuple []⟩ => some .unit
  | ⟨_, .tuple [child]⟩ => interpretStructuralType? table child
  | ⟨_, .tuple [left, right]⟩ => do
      let first ← interpretStructuralType? table left
      let second ← interpretStructuralType? table right
      return .product first second
  | _ => none
termination_by sizeOf source

/-- Source meaning is specified independently of the executable interpreter.
Every child keeps the same table, including duplicate first-match priorities. -/
inductive StructuralTypeDenotes (table : TypeNameTable) : Syntax.TypeExpr → Core.Ty → Prop where
  | named {span : Syntax.SourceSpan} {name : Syntax.QualifiedName} {type : Core.Ty}
      (found : TypeNameTable.Lookup table (qualifiedTypeNameKey name) type) :
      StructuralTypeDenotes table ⟨span, .named name none⟩ type
  | unit {span : Syntax.SourceSpan} : StructuralTypeDenotes table ⟨span, .tuple []⟩ .unit
  | single {span : Syntax.SourceSpan} {child : Syntax.TypeExpr} {type : Core.Ty}
      (meaning : StructuralTypeDenotes table child type) :
      StructuralTypeDenotes table ⟨span, .tuple [child]⟩ type
  | pair {span : Syntax.SourceSpan} {left right : Syntax.TypeExpr} {leftType rightType : Core.Ty}
      (first : StructuralTypeDenotes table left leftType)
      (second : StructuralTypeDenotes table right rightType) :
      StructuralTypeDenotes table ⟨span, .tuple [left, right]⟩ (.product leftType rightType)

end Solcore.Frontend
