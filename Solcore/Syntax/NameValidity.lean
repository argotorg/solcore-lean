import Solcore.Syntax.Foundation

/-! Source-validity contract for canonical qualified names. -/

set_option autoImplicit false

namespace Solcore.Syntax

namespace QualifiedName

/-- Every source range stored by a qualified name belongs to one input file. -/
def ValidFor (file : SourceFile) (name : QualifiedName) : Prop :=
  name.span.ValidFor file ∧
    ∀ component ∈ name.value.components.toList,
      component.span.ValidFor file

end QualifiedName

end Solcore.Syntax
