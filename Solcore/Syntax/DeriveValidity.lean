import Solcore.Syntax.CollectionValidity
import Solcore.Syntax.Declaration
import Solcore.Syntax.NameValidity

/-! Source-validity contract for canonical derive attributes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeriveAttribute

/-- Every range retained by a derive attribute belongs to one source file. -/
def ValidFor (file : SourceFile) (value : DeriveAttribute) : Prop :=
  value.span.ValidFor file ∧
    value.value.targets.ValidFor QualifiedName.ValidFor file

end Solcore.Syntax.DeriveAttribute
