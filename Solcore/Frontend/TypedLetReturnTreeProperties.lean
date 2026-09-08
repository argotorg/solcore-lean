import Solcore.Frontend.TypedLetReturnTreeElaboration

/-! Independent whole typing fixes recursive lets and both ordered branches.
The original input types need no runtime values or extra name-uniqueness premise. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnTreeElaborates.hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TypedLetReturnTreeElaborates types owner inputs body core type) :
    TypedLetReturnTreeHasType types owner inputs body type := by
  induction elaboration with
  | single child => exact .single child.hasType
  | binding meaning unused resolution _ typing _ ih =>
      exact .binding meaning unused (resolution.reflects_type typing) ih
  | conditional resolution _ typing _ _ thenIH elseIH =>
      exact .conditional (resolution.reflects_type typing) thenIH elseIH

theorem TypedLetReturnTreeHasType.elaborates_exact
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnTreeHasType types owner inputs body type) :
    ∃ core, TypedLetReturnTreeElaborates types owner inputs body core type := by
  induction typing with
  | single child =>
      obtain ⟨core, elaboration⟩ := child.elaborates_exact
      exact ⟨core, .single elaboration⟩
  | binding meaning unused initializerTyping _ ih =>
      obtain ⟨resolved, resolution, typed⟩ := initializerTyping.resolves
      obtain ⟨initializerCore, lowered, _⟩ := typed.lowers
      obtain ⟨tailCore, tailElaboration⟩ := ih
      exact ⟨.letE initializerCore tailCore, .binding meaning unused resolution
        (by simpa only [LocalTypeInputs.context_ids] using lowered) typed tailElaboration⟩
  | conditional conditionTyping _ _ thenIH elseIH =>
      obtain ⟨resolved, resolution, typed⟩ := conditionTyping.resolves
      obtain ⟨conditionCore, lowered, _⟩ := typed.lowers
      obtain ⟨thenCore, thenElaboration⟩ := thenIH
      obtain ⟨elseCore, elseElaboration⟩ := elseIH
      exact ⟨.ifE conditionCore thenCore elseCore, .conditional resolution
        (by simpa only [LocalTypeInputs.context_ids] using lowered) typed thenElaboration elseElaboration⟩

theorem typedLetReturnTreeHasType_iff_elaborates_exact
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty} :
    TypedLetReturnTreeHasType types owner inputs body type ↔
      ∃ core, TypedLetReturnTreeElaborates types owner inputs body core type :=
  ⟨TypedLetReturnTreeHasType.elaborates_exact, fun ⟨_, elaboration⟩ => elaboration.hasType⟩

theorem TypedLetReturnTreeHasType.elaborates
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnTreeHasType types owner inputs body type) :
    ∃ core, elaborateTypedLetReturnTree? types owner inputs body = some (core, type) := by
  obtain ⟨core, elaboration⟩ := typing.elaborates_exact
  exact ⟨core, elaboration.complete⟩

theorem elaborateTypedLetReturnTree?_sound
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type)) :
    TypedLetReturnTreeHasType types owner inputs body type :=
  (elaborateTypedLetReturnTree?_elaborates accepted).hasType

theorem typedLetReturnTreeHasType_iff_elaborates
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty} :
    TypedLetReturnTreeHasType types owner inputs body type ↔
      ∃ core, elaborateTypedLetReturnTree? types owner inputs body = some (core, type) :=
  ⟨TypedLetReturnTreeHasType.elaborates, fun ⟨_, accepted⟩ => elaborateTypedLetReturnTree?_sound accepted⟩

theorem elaborateTypedLetReturnTree?_core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type)) :
    Core.HasType (Resolved.LocalScope.values inputs.context) core type := by
  have elaboration := elaborateTypedLetReturnTree?_elaborates accepted
  clear accepted
  induction elaboration with
  | single child => exact elaborateReturnBody?_core_hasType child.complete
  | binding _ _ _ lowered typing _ ih =>
      apply Core.HasType.letE
      · rw [← LocalTypeInputs.context_ids] at lowered
        exact lowered.preserves_type typing
      · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.values,
          List.map_cons, Prod.snd] using ih
  | conditional _ lowered typing _ _ thenIH elseIH =>
      rw [← LocalTypeInputs.context_ids] at lowered
      exact .ifE (lowered.preserves_type typing) thenIH elseIH

/-- Exact source provenance determines both the Core structure and its type;
equal result types alone do not identify another program. -/
theorem TypedLetReturnTreeElaborates.result_unique
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {leftCore rightCore : Core.Expr} {leftType rightType : Core.Ty}
    (left : TypedLetReturnTreeElaborates types owner inputs body leftCore leftType)
    (right : TypedLetReturnTreeElaborates types owner inputs body rightCore rightType) :
    leftCore = rightCore ∧ leftType = rightType :=
  Prod.mk.inj (Option.some.inj (left.complete.symm.trans right.complete))

theorem TypedLetReturnTreeHasType.type_unique
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {left right : Core.Ty}
    (first : TypedLetReturnTreeHasType types owner inputs body left)
    (second : TypedLetReturnTreeHasType types owner inputs body right) : left = right := by
  obtain ⟨_, firstElaboration⟩ := first.elaborates_exact
  obtain ⟨_, secondElaboration⟩ := second.elaborates_exact
  exact (firstElaboration.result_unique secondElaboration).2

theorem elaborateTypedLetReturnTree?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} : elaborateTypedLetReturnTree? types owner inputs body = none ↔
      ¬ ∃ type, TypedLetReturnTreeHasType types owner inputs body type := by
  constructor
  · intro rejected ⟨type, typing⟩
    obtain ⟨core, accepted⟩ := typing.elaborates
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases result : elaborateTypedLetReturnTree? types owner inputs body with
    | none => rfl
    | some pair => exact False.elim (missing ⟨pair.2, elaborateTypedLetReturnTree?_sound result⟩)

end Solcore.Frontend
