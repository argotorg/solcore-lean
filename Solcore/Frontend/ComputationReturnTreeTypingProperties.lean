import Solcore.Frontend.ComputationReturnTree
import Solcore.Frontend.WordMatchProperties
import Solcore.Frontend.LocalTypeInputsProperties
import Solcore.Core.Renaming

/-! Independent body typing uses only the corresponding child typing law.
Core typing needs only child Core typing and general positional weakening. -/

set_option autoImplicit false

namespace Solcore.Frontend

variable {ChildHasType : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Ty → Prop}
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}

private theorem fold_coverage {entries : List (Syntax.MatchCase × (Option Core.Word × Core.Expr))}
    {defaultEntry : Option (Syntax.Block × Core.Expr)}
    (patterns : ∀ entry ∈ entries, WordMatchPatternClassifies entry.1.value.pattern entry.2.1) :
    (entries.foldr (fun entry tail => match entry.2.1 with
      | none => some (entry.2.2.weakenAt 0)
      | some word => tail.map (fun core =>
          .ifE (.binary .wordEq (.var 0) (.word word)) (entry.2.2.weakenAt 0) core))
      (defaultEntry.map (fun entry => entry.2.weakenAt 0))).isSome = true ↔
    defaultEntry.isSome = true ∨ ∃ entry ∈ entries, WordMatchPatternClassifies entry.1.value.pattern none := by
  induction entries with
  | nil => simp
  | cons entry rest ih =>
      have meaning := patterns entry (by simp)
      cases tag : entry.2.1 with
      | none =>
          simp only [tag] at meaning
          simp [tag, meaning]
      | some word =>
          simp only [tag] at meaning
          have notCatchAll : ¬ WordMatchPatternClassifies entry.1.value.pattern none := by
            intro caught
            have impossible := meaning.tag_unique caught
            cases impossible
          simpa [tag, notCatchAll] using ih (fun item member => patterns item (by simp [member]))

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
  | wordMatch scrutinee ordered patterns compatible _ defaultOrdered _ lowered branchIH defaultIH =>
      refine .wordMatch (childTyping.mpr ⟨_, scrutinee⟩) ?_ ?_ ?_ ?_ ?_
      · intro arm member
        rw [← ordered] at member
        obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
        exact ⟨entry.2.1, patterns entry entryMember⟩
      · rcases compatible with word | allNone
        · exact .inl word
        · right; intro arm member
          rw [← ordered] at member
          obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
          simpa only [allNone entry entryMember] using patterns entry entryMember
      · rcases (fold_coverage patterns).mp (congrArg Option.isSome lowered) with present | ⟨entry, member, meaning⟩
        · left; rw [← defaultOrdered]; simpa using present
        · exact .inr ⟨entry.1, ordered ▸ List.mem_map.mpr ⟨entry, member, rfl⟩, meaning⟩
      · intro arm member
        rw [← ordered] at member
        obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
        exact branchIH entry entryMember
      · intro source member
        rw [← defaultOrdered, Option.toList_map] at member
        obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
        exact defaultIH entry entryMember

private theorem entries_exist {cases : List Syntax.MatchCase} {P : Syntax.Block → Core.Expr → Prop}
    (patterns : ∀ arm ∈ cases, ∃ tag, WordMatchPatternClassifies arm.value.pattern tag)
    (branches : ∀ arm ∈ cases, ∃ core, P arm.value.body core) :
    ∃ entries : List (Syntax.MatchCase × (Option Core.Word × Core.Expr)), entries.map Prod.fst = cases ∧
      (∀ entry ∈ entries, WordMatchPatternClassifies entry.1.value.pattern entry.2.1) ∧
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
  | @wordMatch inputs _ _ _ _ _ _ defaultBody scrutineeType type scrutinee patterns compatible covered _ _ branchIH defaultIH =>
      obtain ⟨scrutineeCore, scrutineeElaboration⟩ := childTyping.mp scrutinee
      obtain ⟨entries, ordered, meanings, elaborations⟩ :=
        entries_exist (P := fun body core => ComputationReturnTreeElaborates ChildElab types owner inputs body core type)
          patterns branchIH
      have compatibleEntries : scrutineeType = .word ∨ ∀ entry ∈ entries, entry.2.1 = none := by
        rcases compatible with word | allNone
        · exact .inl word
        · exact .inr (fun entry member => (meanings entry member).tag_unique
            (allNone entry.1 (ordered ▸ List.mem_map.mpr ⟨entry, member, rfl⟩)))
      have defaults : ∃ defaultEntry : Option (Syntax.Block × Core.Expr), defaultEntry.map Prod.fst = defaultBody ∧
          ∀ entry ∈ defaultEntry.toList, ComputationReturnTreeElaborates ChildElab types owner inputs entry.1 entry.2 type := by
        cases defaultBody with
        | none => exact ⟨none, rfl, by simp⟩
        | some source =>
            obtain ⟨core, elaboration⟩ := defaultIH source (by simp)
            exact ⟨some (source, core), rfl, by intro entry member; simpa using (List.mem_singleton.mp member ▸ elaboration)⟩
      obtain ⟨defaultEntry, defaultOrdered, defaults⟩ := defaults
      have coveredFold : defaultEntry.isSome = true ∨ ∃ entry ∈ entries, WordMatchPatternClassifies entry.1.value.pattern none := by
        rcases covered with present | ⟨arm, member, meaning⟩
        · left; rw [← defaultOrdered] at present; simpa using present
        · rw [← ordered] at member
          obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
          exact .inr ⟨entry, entryMember, meaning⟩
      obtain ⟨bodyCore, lowered⟩ := Option.isSome_iff_exists.mp ((fold_coverage meanings).mpr coveredFold)
      exact ⟨_, .wordMatch scrutineeElaboration ordered meanings compatibleEntries elaborations defaultOrdered defaults lowered⟩

theorem computationReturnTreeHasType_iff_elaborates
    (childTyping : ∀ {table context source type},
      ChildHasType table context source type ↔ ∃ core, ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty} :
    ComputationReturnTreeHasType ChildHasType types owner inputs body type ↔
      ∃ core, ComputationReturnTreeElaborates ChildElab types owner inputs body core type :=
  ⟨elaborates childTyping, fun ⟨_, elaboration⟩ => hasType childTyping elaboration⟩

private theorem fold_hasType {context : Core.Context} {scrutineeType type : Core.Ty} {bodyCore : Core.Expr}
    {defaultEntry : Option (Syntax.Block × Core.Expr)}
    {entries : List (Syntax.MatchCase × (Option Core.Word × Core.Expr))}
    (fallback : ∀ entry ∈ defaultEntry.toList, Core.HasType context entry.2 type)
    (branches : ∀ entry ∈ entries, Core.HasType context entry.2.2 type)
    (compatible : scrutineeType = .word ∨ ∀ entry ∈ entries, entry.2.1 = none)
    (lowered : entries.foldr
      (fun entry tail => match entry.2.1 with
        | none => some (entry.2.2.weakenAt 0)
        | some word => tail.map (fun core => .ifE (.binary .wordEq (.var 0) (.word word)) (entry.2.2.weakenAt 0) core))
      (defaultEntry.map (fun entry => entry.2.weakenAt 0)) = some bodyCore) :
    Core.HasType (scrutineeType :: context) bodyCore type := by
  induction entries generalizing bodyCore with
  | nil =>
      obtain ⟨entry, member, rfl⟩ := Option.map_eq_some_iff.mp lowered
      simpa only [Core.Context.insertAt] using (fallback entry (Option.mem_toList.mpr member)).weakenAt 0
  | cons entry rest ih =>
      have head : Core.HasType (scrutineeType :: context) (entry.2.2.weakenAt 0) type := by
        simpa only [Core.Context.insertAt] using (branches entry (by simp)).weakenAt 0
      cases tag : entry.2.1 with
      | none => simp only [List.foldr_cons, tag, Option.some.injEq] at lowered; exact lowered ▸ head
      | some word =>
          simp only [List.foldr_cons, tag] at lowered
          obtain ⟨tail, found, rfl⟩ := Option.map_eq_some_iff.mp lowered
          rcases compatible with rfl | allNone
          · exact .ifE (.binary (.var rfl) (.word)) head
              (ih (fun row member => branches row (by simp [member])) (.inl rfl) found)
          · have impossible := allNone entry (by simp)
            rw [tag] at impossible
            cases impossible

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
  | wordMatch scrutinee _ _ compatible _ _ _ lowered branchIH defaultIH =>
      exact .letE (childCoreType scrutinee) (fold_hasType defaultIH branchIH compatible lowered)

end Solcore.Frontend
