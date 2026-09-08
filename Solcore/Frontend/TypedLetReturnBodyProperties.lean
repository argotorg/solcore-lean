import Solcore.Frontend.TypedLetReturnBodyElaboration

/-! Independent static typing fixes the exact ordered let prefix and terminal
tree. No runtime environment or inhabitants of the input types are needed. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnBodyElaborates.hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TypedLetReturnBodyElaborates types owner inputs body core type) :
    TypedLetReturnBodyHasType types owner inputs body type := by
  induction elaboration with
  | terminal child => exact .terminal child.hasType
  | binding meaning unused resolution _ typing _ ih =>
      exact .binding meaning unused (resolution.reflects_type typing) ih

theorem TypedLetReturnBodyHasType.elaborates_exact
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnBodyHasType types owner inputs body type) :
    ∃ core, TypedLetReturnBodyElaborates types owner inputs body core type := by
  induction typing with
  | terminal child =>
      obtain ⟨core, elaboration⟩ := child.elaborates_exact
      exact ⟨core, .terminal elaboration⟩
  | binding meaning unused initializerTyping _ ih =>
      obtain ⟨resolved, resolution, typed⟩ := initializerTyping.resolves
      obtain ⟨initializerCore, lowered, _⟩ := typed.lowers
      obtain ⟨tailCore, tailElaboration⟩ := ih
      exact ⟨.letE initializerCore tailCore, .binding meaning unused resolution
        (by simpa only [LocalTypeInputs.context_ids] using lowered) typed tailElaboration⟩

theorem typedLetReturnBodyHasType_iff_elaborates_exact
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty} :
    TypedLetReturnBodyHasType types owner inputs body type ↔
      ∃ core, TypedLetReturnBodyElaborates types owner inputs body core type :=
  ⟨TypedLetReturnBodyHasType.elaborates_exact, fun ⟨_, elaboration⟩ => elaboration.hasType⟩

theorem TypedLetReturnBodyHasType.elaborates
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnBodyHasType types owner inputs body type) :
    ∃ core, elaborateTypedLetReturnBody? types owner inputs body = some (core, type) := by
  obtain ⟨core, elaboration⟩ := typing.elaborates_exact
  exact ⟨core, elaboration.complete⟩

theorem elaborateTypedLetReturnBody?_sound
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnBody? types owner inputs body = some (core, type)) :
    TypedLetReturnBodyHasType types owner inputs body type :=
  (elaborateTypedLetReturnBody?_elaborates accepted).hasType

theorem typedLetReturnBodyHasType_iff_elaborates
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty} :
    TypedLetReturnBodyHasType types owner inputs body type ↔
      ∃ core, elaborateTypedLetReturnBody? types owner inputs body = some (core, type) :=
  ⟨TypedLetReturnBodyHasType.elaborates, fun ⟨_, accepted⟩ => elaborateTypedLetReturnBody?_sound accepted⟩

theorem elaborateTypedLetReturnBody?_core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnBody? types owner inputs body = some (core, type)) :
    Core.HasType (Resolved.LocalScope.values inputs.context) core type := by
  have elaboration := elaborateTypedLetReturnBody?_elaborates accepted
  clear accepted
  induction elaboration with
  | terminal child => exact elaborateTerminalReturnTree?_core_hasType child.complete
  | binding _ _ _ lowered typing _ ih =>
      apply Core.HasType.letE
      · rw [← LocalTypeInputs.context_ids] at lowered
        exact lowered.preserves_type typing
      · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.values,
          List.map_cons, Prod.snd] using ih

/-- Exact source provenance fixes both the Core binder structure and its type;
having the same result type does not identify another Core program. -/
theorem TypedLetReturnBodyElaborates.result_unique
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {leftCore rightCore : Core.Expr} {leftType rightType : Core.Ty}
    (left : TypedLetReturnBodyElaborates types owner inputs body leftCore leftType)
    (right : TypedLetReturnBodyElaborates types owner inputs body rightCore rightType) :
    leftCore = rightCore ∧ leftType = rightType :=
  Prod.mk.inj (Option.some.inj (left.complete.symm.trans right.complete))

theorem TypedLetReturnBodyHasType.type_unique
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {left right : Core.Ty}
    (first : TypedLetReturnBodyHasType types owner inputs body left)
    (second : TypedLetReturnBodyHasType types owner inputs body right) : left = right := by
  obtain ⟨_, firstElaboration⟩ := first.elaborates_exact
  obtain ⟨_, secondElaboration⟩ := second.elaborates_exact
  exact (firstElaboration.result_unique secondElaboration).2

theorem elaborateTypedLetReturnBody?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} : elaborateTypedLetReturnBody? types owner inputs body = none ↔
      ¬ ∃ type, TypedLetReturnBodyHasType types owner inputs body type := by
  constructor
  · intro rejected ⟨type, typing⟩
    obtain ⟨core, accepted⟩ := typing.elaborates
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases result : elaborateTypedLetReturnBody? types owner inputs body with
    | none => rfl
    | some pair => exact False.elim (missing ⟨pair.2, elaborateTypedLetReturnBody?_sound result⟩)

end Solcore.Frontend
