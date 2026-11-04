import Solcore.Syntax.Foundation

/-!
Source validity of collections and qualified names.

Main declarations: `List.ValidFor`, `DelimitedList.ValidFor`, `QualifiedName.ValidFor`.
The AST's own files use these, so they come before the AST. The judgments about the AST
are in `Validity`.
-/

section
-- leanmerge: from Solcore.Syntax.CollectionValidity
/-! Source-validity contracts for syntax collection carriers. -/

set_option autoImplicit false

namespace Solcore.Syntax

namespace List

/-- Every element of a list belongs to one source. -/
def ValidFor {α : Type} (elementValid : SourceFile → α → Prop)
    (file : SourceFile) (values : List α) : Prop :=
  ∀ element ∈ values, elementValid file element

end List

namespace NonemptyList

/-- Every element of a structurally nonempty list belongs to one source. -/
def ValidFor {α : Type} (elementValid : SourceFile → α → Prop)
    (file : SourceFile) (values : NonemptyList α) : Prop :=
  ∀ element ∈ values.toList, elementValid file element

end NonemptyList

namespace DelimitedList

/-- The delimiter range and every retained element belong to one input file. -/
def ValidFor {α : Type} (elementValid : SourceFile → α → Prop)
    (file : SourceFile) (values : DelimitedList α) : Prop :=
  values.span.ValidFor file ∧
    ∀ element ∈ values.elements, elementValid file element

end DelimitedList

namespace NonemptyDelimitedList

/-- A nonempty delimited list has valid delimiters and valid elements. -/
def ValidFor {α : Type} (elementValid : SourceFile → α → Prop)
    (file : SourceFile) (values : NonemptyDelimitedList α) : Prop :=
  values.span.ValidFor file ∧ values.elements.ValidFor elementValid file

end NonemptyDelimitedList

namespace Option

/-- An optional syntax value is valid when its present value is valid. -/
def ValidFor {α : Type} (elementValid : SourceFile → α → Prop)
    (file : SourceFile) : Option α → Prop
  | none => True
  | some value => elementValid file value

end Option

end Solcore.Syntax
end

section
-- leanmerge: from Solcore.Syntax.NameValidity
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
end
