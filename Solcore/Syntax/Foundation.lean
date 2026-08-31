import Solcore.Syntax.Token

set_option autoImplicit false

namespace Solcore.Syntax

/-- A list whose non-emptiness is represented by its shape. -/
structure NonemptyList (α : Type) where
  head : α
  tail : List α
  deriving Repr, BEq, DecidableEq

namespace NonemptyList

def toList {α : Type} (values : NonemptyList α) : List α :=
  values.head :: values.tail

def map {α β : Type} (f : α → β)
    (values : NonemptyList α) : NonemptyList β := {
  head := f values.head
  tail := values.tail.map f
}

@[simp] theorem toList_map {α β : Type} (f : α → β)
    (values : NonemptyList α) :
    (values.map f).toList = values.toList.map f := by
  simp [map, toList]

@[simp] theorem length_toList {α : Type} (values : NonemptyList α) :
    values.toList.length = values.tail.length + 1 := by
  simp [toList]

end NonemptyList

/-- One identifier occurrence accepted by an identifier grammar position. -/
abbrev Identifier := SpannedText

/-- Nonempty dotted identifier path in written order. -/
structure QualifiedNameValue where
  components : NonemptyList Identifier
  deriving Repr, BEq, DecidableEq

/-- A dotted identifier path paired with its complete source range. -/
abbrev QualifiedName := Located QualifiedNameValue

/-- A delimiter range paired with the values written between its delimiters. -/
structure DelimitedList (α : Type) where
  span : SourceSpan
  elements : List α
  deriving Repr, BEq, DecidableEq

/-- A nonempty delimited list, used where empty brackets are not grammatical. -/
structure NonemptyDelimitedList (α : Type) where
  span : SourceSpan
  elements : NonemptyList α
  deriving Repr, BEq, DecidableEq

end Solcore.Syntax
