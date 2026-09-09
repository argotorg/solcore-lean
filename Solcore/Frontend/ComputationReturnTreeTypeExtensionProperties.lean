import Solcore.Frontend.ComputationReturnTreeProperties
import Solcore.Frontend.StructuralTypeTableProperties

/-! Meaning-preserving tables retain independent evidence for every original
branch and the exact generated Core. The private checker graph supports only
operational equations for a fixed child operation, not source semantics. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ComputationReturnTreeHasType.extend_types
    {ChildHasType : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Ty → Prop}
    {old new : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : ComputationReturnTreeHasType ChildHasType old owner inputs body type)
    (extension : TypeNameTable.Extends old new) :
    ComputationReturnTreeHasType ChildHasType new owner inputs body type := by
  induction typing with
  | bare => exact .bare
  | expression child => exact .expression child
  | block _ ih => exact .block ih
  | binding meaning initializer _ ih => exact .binding (meaning.extend_types extension) initializer ih
  | inferred initializer _ ih => exact .inferred initializer ih
  | discard expression _ ih => exact .discard expression ih
  | conditional condition protection _ _ thenIH elseIH =>
      exact .conditional condition protection thenIH elseIH
  | wordMatch scrutinee patterns compatible covered _ _ branchIH defaultIH =>
      exact .wordMatch scrutinee patterns compatible covered branchIH defaultIH

theorem ComputationReturnTreeElaborates.extend_types
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {old new : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ComputationReturnTreeElaborates ChildElab old owner inputs body core type)
    (extension : TypeNameTable.Extends old new) :
    ComputationReturnTreeElaborates ChildElab new owner inputs body core type := by
  induction elaboration with
  | bare => exact .bare
  | expression child => exact .expression child
  | block _ ih => exact .block ih
  | binding meaning initializer _ ih => exact .binding (meaning.extend_types extension) initializer ih
  | inferred initializer _ ih => exact .inferred initializer ih
  | discard expression _ ih => exact .discard expression ih
  | conditional condition protection _ _ thenIH elseIH =>
      exact .conditional condition protection thenIH elseIH
  | wordMatch scrutinee ordered patterns compatible _ defaultOrdered _ lowered branchIH defaultIH =>
      exact .wordMatch scrutinee ordered patterns compatible branchIH defaultOrdered defaultIH lowered

private def CheckGraph (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (table : LocalNameTable) (context : Resolved.Context) (source : Syntax.Expr)
    (core : Core.Expr) (type : Core.Ty) : Prop := checkChild table context source = some (core, type)

variable {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}

private theorem checked_body_iff {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {inputs : LocalTypeInputs} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    elaborateComputationReturnTree? checkChild types owner inputs body = some (core, type) ↔
      ComputationReturnTreeElaborates (CheckGraph checkChild) types owner inputs body core type :=
  elaborateComputationReturnTree?_iff (checkChild := checkChild) (ChildElab := CheckGraph checkChild) Iff.rfl

theorem elaborateComputationReturnTree?_some_of_extends
    {old new : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (extension : TypeNameTable.Extends old new)
    (accepted : elaborateComputationReturnTree? checkChild old owner inputs body = some (core, type)) :
    elaborateComputationReturnTree? checkChild new owner inputs body = some (core, type) :=
  checked_body_iff.mpr ((checked_body_iff.mp accepted).extend_types extension)

/-- A one-way extension may repair an unknown annotation, even in an unselected
branch. Mutual extension also retains absence, hence every optional result. -/
theorem elaborateComputationReturnTree?_eq_of_mutual_extends
    {old new : TypeNameTable} (forward : TypeNameTable.Extends old new)
    (backward : TypeNameTable.Extends new old) (owner : Resolved.DeclarationId)
    (inputs : LocalTypeInputs) (body : Syntax.Block) :
    elaborateComputationReturnTree? checkChild old owner inputs body =
      elaborateComputationReturnTree? checkChild new owner inputs body := by
  cases oldResult : elaborateComputationReturnTree? checkChild old owner inputs body with
  | none =>
      cases newResult : elaborateComputationReturnTree? checkChild new owner inputs body with
      | none => rfl
      | some pair =>
          rcases pair with ⟨core, type⟩
          have preserved := elaborateComputationReturnTree?_some_of_extends backward newResult
          rw [oldResult] at preserved
          cases preserved
  | some pair =>
      rcases pair with ⟨core, type⟩
      exact (elaborateComputationReturnTree?_some_of_extends forward oldResult).symm

end Solcore.Frontend
