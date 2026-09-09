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
  | wordMatch scrutinee ordered patterns _ _ branchIH defaultIH =>
      refine .wordMatch (childTyping.mpr ⟨_, scrutinee⟩) ?_ ?_ defaultIH
      · intro arm member
        rw [← ordered] at member
        obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
        exact ⟨entry.2.1, patterns entry entryMember⟩
      · intro arm member
        rw [← ordered] at member
        obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
        exact branchIH entry entryMember

private theorem entries_exist {cases : List Syntax.MatchCase} {P : Syntax.Block → Core.Expr → Prop}
    (patterns : ∀ arm ∈ cases, ∃ word, WordMatchPatternDenotes arm.value.pattern word)
    (branches : ∀ arm ∈ cases, ∃ core, P arm.value.body core) :
    ∃ entries : List (Syntax.MatchCase × (Core.Word × Core.Expr)), entries.map Prod.fst = cases ∧
      (∀ entry ∈ entries, WordMatchPatternDenotes entry.1.value.pattern entry.2.1) ∧
      (∀ entry ∈ entries, P entry.1.value.body entry.2.2) := by
  induction cases with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons arm rest ih =>
      obtain ⟨word, meaning⟩ := patterns arm (by simp)
      obtain ⟨core, elaboration⟩ := branches arm (by simp)
      obtain ⟨entries, ordered, meanings, elaborations⟩ := ih
        (fun arm member => patterns arm (by simp [member]))
        (fun arm member => branches arm (by simp [member]))
      refine ⟨(arm, word, core) :: entries, by simp [ordered], ?_, ?_⟩
      · intro entry member
        rcases List.mem_cons.mp member with rfl | member
        · exact meaning
        · exact meanings entry member
      · intro entry member
        rcases List.mem_cons.mp member with rfl | member
        · exact elaboration
        · exact elaborations entry member

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
  | @wordMatch inputs _ _ _ _ _ _ _ type scrutinee patterns _ _ branchIH defaultIH =>
      obtain ⟨scrutineeCore, scrutineeElaboration⟩ := childTyping.mp scrutinee
      obtain ⟨defaultCore, defaultElaboration⟩ := defaultIH
      obtain ⟨entries, ordered, meanings, elaborations⟩ :=
        entries_exist (P := fun body core => ComputationReturnTreeElaborates ChildElab types owner inputs body core type)
          patterns branchIH
      exact ⟨_, .wordMatch scrutineeElaboration ordered meanings elaborations defaultElaboration⟩

theorem computationReturnTreeHasType_iff_elaborates
    (childTyping : ∀ {table context source type},
      ChildHasType table context source type ↔ ∃ core, ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty} :
    ComputationReturnTreeHasType ChildHasType types owner inputs body type ↔
      ∃ core, ComputationReturnTreeElaborates ChildElab types owner inputs body core type :=
  ⟨elaborates childTyping, fun ⟨_, elaboration⟩ => hasType childTyping elaboration⟩

private theorem fold_hasType {context : Core.Context} {type : Core.Ty} {defaultCore : Core.Expr}
    {entries : List (Syntax.MatchCase × (Core.Word × Core.Expr))}
    (fallback : Core.HasType context defaultCore type)
    (branches : ∀ entry ∈ entries, Core.HasType context entry.2.2 type) :
    Core.HasType (.word :: context) (entries.foldr
      (fun entry tail => .ifE (.binary .wordEq (.var 0) (.word entry.2.1)) (entry.2.2.weakenAt 0) tail)
      (defaultCore.weakenAt 0)) type := by
  induction entries with
  | nil => simpa only [List.foldr_nil, Core.Context.insertAt] using fallback.weakenAt 0
  | cons entry rest ih =>
      exact .ifE (.binary (.var rfl) (.word))
        (by simpa only [Core.Context.insertAt] using (branches entry (by simp)).weakenAt 0)
        (ih (fun row member => branches row (by simp [member])))

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
  | wordMatch scrutinee _ _ _ _ branchIH defaultIH =>
      exact .letE (childCoreType scrutinee) (fold_hasType defaultIH branchIH)

end Solcore.Frontend
