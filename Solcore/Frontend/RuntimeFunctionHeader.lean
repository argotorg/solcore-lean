import Solcore.Frontend.StructuralTypeProperties
import Solcore.Syntax.Declaration

/-! Explicit single-return contracts for unmodified, nongeneric runtime entries.
The one written annotation has structural meaning; parameters and lets are unchanged.
Empty/multiple return clauses are outside this profile, not invalid syntax. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive RuntimeReturnTypeDenotes (types : TypeNameTable) : Option Syntax.ReturnClause → Core.Ty → Prop where
  | absent : RuntimeReturnTypeDenotes types none .unit
  | single {clauseSpan typesSpan : Syntax.SourceSpan} {annotation : Syntax.TypeExpr} {type : Core.Ty}
      (meaning : StructuralTypeDenotes types annotation type) :
      RuntimeReturnTypeDenotes types
        (some { span := clauseSpan, types := ⟨typesSpan, [annotation]⟩ }) type

def interpretRuntimeReturnType? (types : TypeNameTable) : Option Syntax.ReturnClause → Option Core.Ty
  | none => some .unit
  | some clause => match clause.types.elements with
    | [annotation] => interpretStructuralType? types annotation
    | _ => none

/-- Header shape restrictions are independent of any executable check. -/
structure RuntimeFunctionHeader (types : TypeNameTable)
    (signature : Syntax.FunctionSignature) (returnType : Core.Ty) : Prop where
  noGenerics : signature.genericParameters = none
  noWhere : signature.whereClause = none
  noPublic : signature.modifiers.publicMarker = none
  noPayable : signature.modifiers.payableMarker = none
  returnsMeaning : RuntimeReturnTypeDenotes types signature.returnsClause returnType

def interpretRuntimeFunctionHeader? (types : TypeNameTable)
    (signature : Syntax.FunctionSignature) : Option Core.Ty :=
  match signature.genericParameters, signature.whereClause,
      signature.modifiers.publicMarker, signature.modifiers.payableMarker with
  | none, none, none, none => interpretRuntimeReturnType? types signature.returnsClause
  | _, _, _, _ => none

theorem interpretRuntimeReturnType?_iff {types : TypeNameTable}
    {clause : Option Syntax.ReturnClause} {type : Core.Ty} :
    interpretRuntimeReturnType? types clause = some type ↔ RuntimeReturnTypeDenotes types clause type := by
  constructor
  · intro accepted
    cases clause with
    | none =>
        simp only [interpretRuntimeReturnType?, Option.some.injEq] at accepted
        subst type
        exact .absent
    | some clause =>
        rcases clause with ⟨clauseSpan, ⟨typesSpan, annotations⟩⟩
        cases annotations with
        | nil => simp only [interpretRuntimeReturnType?, reduceCtorEq] at accepted
        | cons annotation rest =>
            cases rest with
            | nil => exact .single (interpretStructuralType?_sound accepted)
            | cons next rest => simp only [interpretRuntimeReturnType?, reduceCtorEq] at accepted
  · intro meaning
    cases meaning with
    | absent => rfl
    | single annotation => exact annotation.complete

theorem RuntimeReturnTypeDenotes.type_unique {types : TypeNameTable}
    {clause : Option Syntax.ReturnClause} {left right : Core.Ty}
    (first : RuntimeReturnTypeDenotes types clause left)
    (second : RuntimeReturnTypeDenotes types clause right) : left = right :=
  Option.some.inj ((interpretRuntimeReturnType?_iff.mpr first).symm.trans
    (interpretRuntimeReturnType?_iff.mpr second))

theorem interpretRuntimeFunctionHeader?_iff {types : TypeNameTable}
    {signature : Syntax.FunctionSignature} {type : Core.Ty} :
    interpretRuntimeFunctionHeader? types signature = some type ↔
      RuntimeFunctionHeader types signature type := by
  constructor
  · intro accepted
    rcases signature with ⟨span, name, generics, parameters, ⟨publicMarker, payableMarker⟩, returns, whereClause⟩
    cases generics <;> cases whereClause <;> cases publicMarker <;> cases payableMarker <;>
      simp only [interpretRuntimeFunctionHeader?, reduceCtorEq] at accepted
    exact ⟨rfl, rfl, rfl, rfl, interpretRuntimeReturnType?_iff.mp accepted⟩
  · intro header
    simp only [interpretRuntimeFunctionHeader?, header.noGenerics, header.noWhere,
      header.noPublic, header.noPayable]
    exact interpretRuntimeReturnType?_iff.mpr header.returnsMeaning

theorem RuntimeFunctionHeader.type_unique {types : TypeNameTable}
    {signature : Syntax.FunctionSignature} {left right : Core.Ty}
    (first : RuntimeFunctionHeader types signature left)
    (second : RuntimeFunctionHeader types signature right) : left = right :=
  first.returnsMeaning.type_unique second.returnsMeaning

theorem interpretRuntimeFunctionHeader?_eq_none_iff {types : TypeNameTable}
    {signature : Syntax.FunctionSignature} :
    interpretRuntimeFunctionHeader? types signature = none ↔
      ¬ ∃ type, RuntimeFunctionHeader types signature type := by
  constructor
  · intro rejected ⟨type, header⟩
    have accepted := interpretRuntimeFunctionHeader?_iff.mpr header
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases accepted : interpretRuntimeFunctionHeader? types signature with
    | none => rfl
    | some type => exact False.elim (missing ⟨type, interpretRuntimeFunctionHeader?_iff.mp accepted⟩)

end Solcore.Frontend
