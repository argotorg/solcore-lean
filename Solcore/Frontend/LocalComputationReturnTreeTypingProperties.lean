import Solcore.Frontend.LocalComputationReturnTreeProperties
import Solcore.Frontend.LocalTypeInputsProperties
import Solcore.Core.Renaming

/-! Independent mixed-body typing needs no actual inhabitants or runtime world.
Hidden discard slots use general Core typing weakening, not a pure-fragment law. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationReturnTreeElaborates types owner inputs body core type) :
    LocalComputationReturnTreeHasType types owner inputs body type := by
  induction elaboration with
  | bare => exact .bare
  | expression child => exact .expression (localComputationHasType_iff_elaborates.mpr ⟨_, child⟩)
  | block _ ih => exact .block ih
  | binding meaning unused initializer _ ih =>
      exact .binding meaning unused (localComputationHasType_iff_elaborates.mpr ⟨_, initializer⟩) ih
  | inferred unused initializer _ ih =>
      exact .inferred unused (localComputationHasType_iff_elaborates.mpr ⟨_, initializer⟩) ih
  | discard expression _ ih =>
      exact .discard (localComputationHasType_iff_elaborates.mpr ⟨_, expression⟩) ih
  | conditional condition _ _ thenIH elseIH =>
      exact .conditional (localComputationHasType_iff_elaborates.mpr ⟨_, condition⟩) thenIH elseIH

private theorem elaborates
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : LocalComputationReturnTreeHasType types owner inputs body type) :
    ∃ core, LocalComputationReturnTreeElaborates types owner inputs body core type := by
  induction typing with
  | bare => exact ⟨.unit, .bare⟩
  | expression child =>
      obtain ⟨core, elaboration⟩ := localComputationHasType_iff_elaborates.mp child
      exact ⟨core, .expression elaboration⟩
  | block _ ih =>
      obtain ⟨core, elaboration⟩ := ih
      exact ⟨core, .block elaboration⟩
  | binding meaning unused initializer _ ih =>
      obtain ⟨initializerCore, initializerElaboration⟩ := localComputationHasType_iff_elaborates.mp initializer
      obtain ⟨tailCore, tailElaboration⟩ := ih
      exact ⟨.letE initializerCore tailCore, .binding meaning unused initializerElaboration tailElaboration⟩
  | inferred unused initializer _ ih =>
      obtain ⟨initializerCore, initializerElaboration⟩ := localComputationHasType_iff_elaborates.mp initializer
      obtain ⟨tailCore, tailElaboration⟩ := ih
      exact ⟨.letE initializerCore tailCore, .inferred unused initializerElaboration tailElaboration⟩
  | discard expression _ ih =>
      obtain ⟨expressionCore, expressionElaboration⟩ := localComputationHasType_iff_elaborates.mp expression
      obtain ⟨tailCore, tailElaboration⟩ := ih
      exact ⟨.letE expressionCore (tailCore.weakenAt 0), .discard expressionElaboration tailElaboration⟩
  | conditional condition _ _ thenIH elseIH =>
      obtain ⟨conditionCore, conditionElaboration⟩ := localComputationHasType_iff_elaborates.mp condition
      obtain ⟨thenCore, thenElaboration⟩ := thenIH
      obtain ⟨elseCore, elseElaboration⟩ := elseIH
      exact ⟨.ifE conditionCore thenCore elseCore, .conditional conditionElaboration thenElaboration elseElaboration⟩

theorem localComputationReturnTreeHasType_iff_elaborates
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty} :
    LocalComputationReturnTreeHasType types owner inputs body type ↔
      ∃ core, LocalComputationReturnTreeElaborates types owner inputs body core type :=
  ⟨elaborates, fun ⟨_, elaboration⟩ => hasType elaboration⟩

theorem LocalComputationReturnTreeElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationReturnTreeElaborates types owner inputs body core type) :
    Core.HasType inputs.context.values core type := by
  induction elaboration with
  | bare => exact .unit
  | expression child => exact child.core_hasType
  | block _ ih => exact ih
  | binding _ _ initializer _ ih | inferred _ initializer _ ih =>
      exact .letE initializer.core_hasType
        (by simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.values, List.map_cons, Prod.snd] using ih)
  | discard expression _ ih =>
      exact .letE expression.core_hasType (by simpa only [Core.Context.insertAt] using ih.weakenAt 0)
  | conditional condition _ _ thenIH elseIH => exact .ifE condition.core_hasType thenIH elseIH

end Solcore.Frontend
