import Solcore.Frontend.TypeName

/-! Structural type meanings over original canonical syntax, shared by entry annotations.
The separate named-only interpreter and its whole-result membership law stay unchanged. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Exact named leaves, Unit, singleton identity, right-associated products and unary
function annotations. Original child nesting and source parameter arity are retained. -/
def interpretStructuralType? (table : TypeNameTable) (source : Syntax.TypeExpr) : Option Core.Ty :=
  match source with
  | ⟨_, .named name none⟩ => table.lookup? (qualifiedTypeNameKey name)
  | ⟨_, .tuple []⟩ => some .unit
  | ⟨_, .tuple [child]⟩ => interpretStructuralType? table child
  | ⟨_, .tuple [left, right]⟩ => do
      let first ← interpretStructuralType? table left
      let second ← interpretStructuralType? table right
      return .product first second
  | ⟨span, .tuple (first :: second :: third :: rest)⟩ => do
      let headType ← interpretStructuralType? table first
      let tailType ← interpretStructuralType? table ⟨span, .tuple (second :: third :: rest)⟩
      return .product headType tailType
  | ⟨_, .function _ ⟨_, [parameter]⟩ none⟩ => do
      let parameterType ← interpretStructuralType? table parameter
      return .function parameterType .unit
  | ⟨_, .function _ ⟨_, [parameter]⟩ (some ⟨returnsSpan, results⟩)⟩ => do
      let parameterType ← interpretStructuralType? table parameter
      let returnType ← interpretStructuralType? table ⟨returnsSpan, .tuple results⟩
      return .function parameterType returnType
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
  | many {span : Syntax.SourceSpan} {first second third : Syntax.TypeExpr}
      {rest : List Syntax.TypeExpr} {firstType tailType : Core.Ty}
      (headMeaning : StructuralTypeDenotes table first firstType)
      (tailMeaning : StructuralTypeDenotes table ⟨span, .tuple (second :: third :: rest)⟩ tailType) :
      StructuralTypeDenotes table ⟨span, .tuple (first :: second :: third :: rest)⟩ (.product firstType tailType)
  | functionDefault {span keyword parametersSpan : Syntax.SourceSpan}
      {parameter : Syntax.TypeExpr} {parameterType : Core.Ty}
      (parameterMeaning : StructuralTypeDenotes table parameter parameterType) :
      StructuralTypeDenotes table ⟨span, .function keyword ⟨parametersSpan, [parameter]⟩ none⟩
        (.function parameterType .unit)
  | functionReturns {span keyword parametersSpan returnsSpan : Syntax.SourceSpan}
      {parameter : Syntax.TypeExpr} {results : List Syntax.TypeExpr} {parameterType returnType : Core.Ty}
      (parameterMeaning : StructuralTypeDenotes table parameter parameterType)
      (returnMeaning : StructuralTypeDenotes table ⟨returnsSpan, .tuple results⟩ returnType) :
      StructuralTypeDenotes table
        ⟨span, .function keyword ⟨parametersSpan, [parameter]⟩ (some ⟨returnsSpan, results⟩)⟩
        (.function parameterType returnType)

end Solcore.Frontend
