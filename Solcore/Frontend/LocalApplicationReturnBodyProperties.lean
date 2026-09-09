import Solcore.Frontend.LocalApplicationReturnBody
import Solcore.Frontend.LocalFunctionApplicationProperties

/-! Exact static provenance for one original application return. The body
retains its child's Core and type; no runtime value or store premise is added. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalApplicationReturnBodyElaborates.complete
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationReturnBodyElaborates table context body core type) :
    elaborateLocalApplicationReturnBody? table context body = some (core, type) := by
  cases elaboration with
  | application child => exact child.complete

theorem elaborateLocalApplicationReturnBody?_sound
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalApplicationReturnBody? table context body = some (core, type)) :
    LocalApplicationReturnBodyElaborates table context body core type := by
  rcases body with ⟨blockSpan, statements⟩
  cases statements with
  | nil => cases accepted
  | cons statement rest =>
      rcases statement with ⟨returnSpan, payload⟩
      cases payload <;> try cases accepted
      case returnStmt returned =>
        cases returned with
        | none => cases accepted
        | some source =>
            cases rest with
            | cons _ _ => cases accepted
            | nil => exact .application (elaborateLocalFunctionApplication?_sound accepted)

theorem elaborateLocalApplicationReturnBody?_iff
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalApplicationReturnBody? table context body = some (core, type) ↔
      LocalApplicationReturnBodyElaborates table context body core type :=
  ⟨elaborateLocalApplicationReturnBody?_sound, LocalApplicationReturnBodyElaborates.complete⟩

theorem LocalApplicationReturnBodyElaborates.hasType
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationReturnBodyElaborates table context body core type) :
    LocalApplicationReturnBodyHasType table context body type := by
  cases elaboration with
  | application child => exact .application child.hasType

theorem LocalApplicationReturnBodyHasType.elaborates_exact
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : LocalApplicationReturnBodyHasType table context body type) :
    ∃ core, LocalApplicationReturnBodyElaborates table context body core type := by
  cases typing with
  | application child =>
      obtain ⟨core, elaboration⟩ := child.elaborates_exact
      exact ⟨core, .application elaboration⟩

theorem localApplicationReturnBodyHasType_iff_elaborates
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} :
    LocalApplicationReturnBodyHasType table context body type ↔
      ∃ core, LocalApplicationReturnBodyElaborates table context body core type :=
  ⟨LocalApplicationReturnBodyHasType.elaborates_exact, fun ⟨_, elaboration⟩ => elaboration.hasType⟩

theorem LocalApplicationReturnBodyElaborates.result_unique
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {leftCore rightCore : Core.Expr} {leftType rightType : Core.Ty}
    (left : LocalApplicationReturnBodyElaborates table context body leftCore leftType)
    (right : LocalApplicationReturnBodyElaborates table context body rightCore rightType) :
    leftCore = rightCore ∧ leftType = rightType := by
  cases left with
  | application leftChild =>
      cases right with
      | application rightChild => exact leftChild.result_unique rightChild

theorem LocalApplicationReturnBodyHasType.type_unique
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {left right : Core.Ty}
    (leftTyped : LocalApplicationReturnBodyHasType table context body left)
    (rightTyped : LocalApplicationReturnBodyHasType table context body right) : left = right := by
  cases leftTyped with
  | application leftChild =>
      cases rightTyped with
      | application rightChild => exact leftChild.type_unique rightChild

theorem LocalApplicationReturnBodyElaborates.core_hasType
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationReturnBodyElaborates table context body core type) :
    Core.HasType (Resolved.LocalScope.values context) core type := by
  cases elaboration with
  | application child => exact child.core_hasType

theorem elaborateLocalApplicationReturnBody?_core_hasType
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalApplicationReturnBody? table context body = some (core, type)) :
    Core.HasType (Resolved.LocalScope.values context) core type :=
  (elaborateLocalApplicationReturnBody?_sound accepted).core_hasType

theorem elaborateLocalApplicationReturnBody?_eq_none_iff
    {table : LocalNameTable} {context : Resolved.Context} {body : Syntax.Block} :
    elaborateLocalApplicationReturnBody? table context body = none ↔
      ¬ ∃ type, LocalApplicationReturnBodyHasType table context body type := by
  constructor
  · intro rejected ⟨_, typing⟩
    obtain ⟨_, elaboration⟩ := typing.elaborates_exact
    have accepted := elaboration.complete
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases result : elaborateLocalApplicationReturnBody? table context body with
    | none => rfl
    | some pair => exact False.elim (missing ⟨pair.2, (elaborateLocalApplicationReturnBody?_sound result).hasType⟩)

end Solcore.Frontend
