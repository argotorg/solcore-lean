import Solcore.Syntax.DeclarativeCoreTypeNameExactnessProperties

/-! Internal motives shared by the recursive Core type value proof. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar.CoreTypeExactnessInternals

theorem nonemptyDelimited_eq_of_toList_eq {alpha : Type}
    {left right : NonemptyDelimitedList alpha}
    (spanEq : left.span = right.span)
    (elementsEq : left.elements.toList = right.elements.toList) :
    left = right := by
  cases left with
  | mk _ leftElements =>
      cases leftElements with
      | mk _ _ =>
          cases right with
          | mk _ rightElements =>
              cases rightElements with
              | mk _ _ => simp_all [Syntax.NonemptyList.toList]

def typeValueMotive (input : Remainder) (value : Syntax.TypeExpr)
    (output : Remainder) (_ : TypeExprParses input value output) : Prop :=
  ∀ {right afterRight}, TypeExprParses input right afterRight → value = right

def tailValueMotive (closing : Symbol) (input : Remainder)
    (values : List Syntax.TypeExpr) (closingSpan : SourceSpan)
    (output : Remainder)
    (_ : TypeExprTrailingDelimitedTailParses closing input values closingSpan
      output) : Prop :=
  ∀ {right rightClosing afterRight},
    TypeExprTrailingDelimitedTailParses closing input right rightClosing
      afterRight →
    values = right ∧ closingSpan = rightClosing ∧ output = afterRight

def listValueMotive (opening closing : Symbol) (input : Remainder)
    (value : DelimitedList Syntax.TypeExpr) (output : Remainder)
    (_ : TypeExprTrailingDelimitedListParses opening closing input value
      output) : Prop :=
  ∀ {right afterRight},
    TypeExprTrailingDelimitedListParses opening closing input right afterRight →
    value = right ∧ output = afterRight

def argumentsValueMotive (input : Remainder)
    (value : Option (NonemptyDelimitedList Syntax.TypeExpr))
    (output : Remainder)
    (_ : OptionalNamedTypeArgumentsParses input value output) : Prop :=
  ∀ {right afterRight}, OptionalNamedTypeArgumentsParses input right afterRight →
    value = right ∧ output = afterRight

def returnsValueMotive (input : Remainder)
    (value : Option (DelimitedList Syntax.TypeExpr)) (output : Remainder)
    (_ : OptionalFunctionTypeReturnsParses input value output) : Prop :=
  ∀ {right afterRight}, OptionalFunctionTypeReturnsParses input right afterRight →
    value = right ∧ output = afterRight

end Solcore.Syntax.DeclarativeGrammar.CoreTypeExactnessInternals
