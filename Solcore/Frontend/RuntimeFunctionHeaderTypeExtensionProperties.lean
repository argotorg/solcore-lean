import Solcore.Frontend.StructuralTypeTableProperties
import Solcore.Frontend.RuntimeFunctionHeader

/-! Retain complete runtime header policy while extending caller type meanings.
Absent returns still mean Unit; exact annotations retain their original types. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeReturnTypeDenotes.extend_types {old next : TypeNameTable}
    {clause : Option Syntax.ReturnClause} {type : Core.Ty}
    (meaning : RuntimeReturnTypeDenotes old clause type)
    (extension : TypeNameTable.Extends old next) : RuntimeReturnTypeDenotes next clause type := by
  cases meaning with
  | absent => exact .absent
  | single annotation => exact .single (annotation.extend_types extension)

theorem RuntimeFunctionHeader.extend_types {old next : TypeNameTable}
    {signature : Syntax.FunctionSignature} {type : Core.Ty}
    (header : RuntimeFunctionHeader old signature type)
    (extension : TypeNameTable.Extends old next) : RuntimeFunctionHeader next signature type :=
  ⟨header.noGenerics, header.noWhere, header.noPublic, header.noPayable,
    header.returnsMeaning.extend_types extension⟩

end Solcore.Frontend
