import Solcore.Frontend.ComputationReturnTree
import Solcore.Frontend.LocalTypeInputsProperties
import Solcore.Core.Renaming

/-! Independent body typing uses only the corresponding child typing law.
Core typing needs only child Core typing and general positional weakening. -/

set_option autoImplicit false

namespace Solcore.Frontend

variable {ChildHasType : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Ty → Prop}
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}

private theorem hasType
    (childTyping : ∀ {table context source type},
      ChildHasType table context source type ↔ ∃ core, ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ComputationReturnTreeElaborates ChildElab types owner inputs body core type) :
    ComputationReturnTreeHasType ChildHasType types owner inputs body type := by
  induction elaboration with
  | bare => exact .bare
  | expression child => exact .expression (childTyping.mpr ⟨_, child⟩)
  | block _ ih => exact .block ih
  | binding meaning unused initializer _ ih =>
      exact .binding meaning unused (childTyping.mpr ⟨_, initializer⟩) ih
  | inferred unused initializer _ ih =>
      exact .inferred unused (childTyping.mpr ⟨_, initializer⟩) ih
  | discard expression _ ih =>
      exact .discard (childTyping.mpr ⟨_, expression⟩) ih
  | conditional condition _ _ thenIH elseIH =>
      exact .conditional (childTyping.mpr ⟨_, condition⟩) thenIH elseIH

private theorem elaborates
    (childTyping : ∀ {table context source type},
      ChildHasType table context source type ↔ ∃ core, ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : ComputationReturnTreeHasType ChildHasType types owner inputs body type) :
    ∃ core, ComputationReturnTreeElaborates ChildElab types owner inputs body core type := by
  induction typing with
  | bare => exact ⟨.unit, .bare⟩
  | expression child =>
      obtain ⟨core, elaboration⟩ := childTyping.mp child
      exact ⟨core, .expression elaboration⟩
  | block _ ih =>
      obtain ⟨core, elaboration⟩ := ih
      exact ⟨core, .block elaboration⟩
  | binding meaning unused initializer _ ih =>
      obtain ⟨initializerCore, initializerElaboration⟩ := childTyping.mp initializer
      obtain ⟨tailCore, tailElaboration⟩ := ih
      exact ⟨.letE initializerCore tailCore, .binding meaning unused initializerElaboration tailElaboration⟩
  | inferred unused initializer _ ih =>
      obtain ⟨initializerCore, initializerElaboration⟩ := childTyping.mp initializer
      obtain ⟨tailCore, tailElaboration⟩ := ih
      exact ⟨.letE initializerCore tailCore, .inferred unused initializerElaboration tailElaboration⟩
  | discard expression _ ih =>
      obtain ⟨expressionCore, expressionElaboration⟩ := childTyping.mp expression
      obtain ⟨tailCore, tailElaboration⟩ := ih
      exact ⟨.letE expressionCore (tailCore.weakenAt 0), .discard expressionElaboration tailElaboration⟩
  | conditional condition _ _ thenIH elseIH =>
      obtain ⟨conditionCore, conditionElaboration⟩ := childTyping.mp condition
      obtain ⟨thenCore, thenElaboration⟩ := thenIH
      obtain ⟨elseCore, elseElaboration⟩ := elseIH
      exact ⟨.ifE conditionCore thenCore elseCore, .conditional conditionElaboration thenElaboration elseElaboration⟩

theorem computationReturnTreeHasType_iff_elaborates
    (childTyping : ∀ {table context source type},
      ChildHasType table context source type ↔ ∃ core, ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty} :
    ComputationReturnTreeHasType ChildHasType types owner inputs body type ↔
      ∃ core, ComputationReturnTreeElaborates ChildElab types owner inputs body core type :=
  ⟨elaborates childTyping, fun ⟨_, elaboration⟩ => hasType childTyping elaboration⟩

theorem ComputationReturnTreeElaborates.core_hasType
    (childCoreType : ∀ {table context source core type},
      ChildElab table context source core type → Core.HasType context.values core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ComputationReturnTreeElaborates ChildElab types owner inputs body core type) :
    Core.HasType inputs.context.values core type := by
  induction elaboration with
  | bare => exact .unit
  | expression child => exact childCoreType child
  | block _ ih => exact ih
  | binding _ _ initializer _ ih | inferred _ initializer _ ih =>
      exact .letE (childCoreType initializer)
        (by simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.values, List.map_cons, Prod.snd] using ih)
  | discard expression _ ih =>
      exact .letE (childCoreType expression) (by simpa only [Core.Context.insertAt] using ih.weakenAt 0)
  | conditional condition _ _ thenIH elseIH => exact .ifE (childCoreType condition) thenIH elseIH

end Solcore.Frontend
