import Solcore.Frontend.ComputationReturnTreeEvaluation
import Solcore.Frontend.ComputationReturnTreeFragmentProperties
import Solcore.Frontend.ComputationBodyFragmentInsertionProperties
import Solcore.Frontend.LocalTypeInputsProperties
import Solcore.Frontend.WordMatchProperties

/-! Whole-body Core correspondence uses separate child execution and insertion
laws at every original scope. Actual values and intermediate stores are retained. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem word_test_iff {environment : Core.Environment} {actual : Core.Value}
    {literal : Core.Word} {initialStore finalStore : Core.Store} {decision : Bool} :
    Core.Evaluates (actual :: environment) initialStore
      (.binary .wordEq (.var 0) (.word literal)) (.bool decision) finalStore ↔
      ∃ word, actual = .word word ∧ (word == literal) = decision ∧ finalStore = initialStore := by
  constructor
  · intro evaluation
    cases evaluation with
    | binary left right applied =>
        cases left with
        | var found =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst found
            cases right
            cases actual <;> simp_all [Core.BinaryOp.apply]
  · rintro ⟨word, rfl, rfl, rfl⟩
    exact .binary (.var rfl) .word rfl

private theorem fold_evaluates_iff
    (entries : List (Syntax.MatchCase × (Option Core.Word × Core.Expr)))
    {environment : Core.Environment} {actual value : Core.Value}
    {initialStore finalStore : Core.Store} {defaultBody : Syntax.Block} {defaultCore : Core.Expr}
    {E : Syntax.Block → Prop}
    (patterns : ∀ entry ∈ entries, match entry.2.1 with
      | none => ∃ marker, entry.1.value.pattern.value = .wildcard marker
      | some word => WordMatchPatternDenotes entry.1.value.pattern word)
    (branches : ∀ entry ∈ entries, Core.Evaluates (actual :: environment) initialStore
      (entry.2.2.weakenAt 0) value finalStore ↔ E entry.1.value.body)
    (fallback : Core.Evaluates (actual :: environment) initialStore
      (defaultCore.weakenAt 0) value finalStore ↔ E defaultBody) :
    Core.Evaluates (actual :: environment) initialStore
      (entries.foldr (fun entry tail => match entry.2.1 with
        | none => entry.2.2.weakenAt 0
        | some word => .ifE (.binary .wordEq (.var 0) (.word word))
            (entry.2.2.weakenAt 0) tail) (defaultCore.weakenAt 0)) value finalStore ↔
      ∃ selected tests, WordMatchChooses actual (entries.map Prod.fst) defaultBody selected tests ∧ E selected := by
  revert patterns branches
  induction entries with
  | nil =>
      intro _ _
      constructor
      · intro evaluation; exact ⟨_, 0, .fallback, fallback.mp evaluation⟩
      · rintro ⟨_, _, choice, branch⟩; cases choice; exact fallback.mpr branch
  | cons entry rest ih =>
      intro patterns branches
      have tail := ih (fun item member => patterns item (List.mem_cons_of_mem entry member))
        (fun item member => branches item (List.mem_cons_of_mem entry member))
      have meaning := patterns entry (List.mem_cons_self)
      have branch := branches entry (List.mem_cons_self)
      cases tag : entry.2.1 with
      | none =>
          simp only [tag] at meaning
          simp only [List.foldr_cons, tag]
          obtain ⟨marker, shape⟩ := meaning
          constructor
          · intro evaluation; exact ⟨_, 0, .wildcard shape, branch.mp evaluation⟩
          · rintro ⟨selected, tests, choice, evaluated⟩
            cases choice with
            | wildcard _ => exact branch.mpr evaluated
            | hit other => obtain ⟨_, wrong, _⟩ := other; simp [shape] at wrong
            | miss other _ _ => obtain ⟨_, wrong, _⟩ := other; simp [shape] at wrong
      | some literal =>
          simp only [tag] at meaning
          simp only [List.foldr_cons, tag]
          constructor
          · intro evaluation
            cases evaluation with
            | ifTrue guard evaluated =>
                obtain ⟨word, rfl, equal, rfl⟩ := word_test_iff.mp guard
                have same : word = literal := by simpa using equal
                subst word
                exact ⟨_, 1, .hit meaning, branch.mp evaluated⟩
            | ifFalse guard evaluated =>
                obtain ⟨word, rfl, different, rfl⟩ := word_test_iff.mp guard
                have unequal : word ≠ literal := by simpa using different
                obtain ⟨selected, tests, choice, selectedBranch⟩ := tail.mp evaluated
                exact ⟨selected, tests + 1, .miss meaning unequal choice, selectedBranch⟩
          · rintro ⟨selected, tests, choice, evaluated⟩
            cases choice with
            | wildcard shape => obtain ⟨_, wrong, _⟩ := meaning; simp [shape] at wrong
            | hit actualMeaning =>
                have same := actualMeaning.value_unique meaning
                subst same
                exact .ifTrue (word_test_iff.mpr ⟨_, rfl, by simp, rfl⟩) (branch.mpr evaluated)
            | miss otherMeaning different choice =>
                have same := otherMeaning.value_unique meaning
                subst same
                exact .ifFalse (word_test_iff.mpr ⟨_, rfl, by simpa using different, rfl⟩)
                  (tail.mpr ⟨_, _, choice, evaluated⟩)

theorem ComputationReturnTreeElaborates.evaluates_iff
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {ChildEval : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop}
    {F : Core.Expr → Prop}
    (childMembership : ∀ {table context source core type}, ChildElab table context source core type → F core)
    (childWeakening : ∀ {core}, F core → ∀ cutoff, F (core.weakenAt cutoff))
    (childInserts : ∀ {core}, F core → ∀ leading suffix inserted {initialStore finalStore value},
      Core.Evaluates (leading ++ inserted :: suffix) initialStore (core.weakenAt leading.length) value finalStore ↔
        Core.Evaluates (leading ++ suffix) initialStore core value finalStore)
    (childExecution : ∀ {table context environment source core type},
      ChildElab table context source core type → environment.ids = context.ids →
      ∀ {initialStore finalStore value}, ChildEval table environment initialStore source value finalStore ↔
        Core.Evaluates environment.values initialStore core value finalStore)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ComputationReturnTreeElaborates ChildElab types owner inputs body core type)
    (sameIds : environment.ids = inputs.context.ids)
    {initialStore finalStore : Core.Store} {value : Core.Value} :
    ComputationReturnTreeEvaluates ChildEval owner inputs.names environment initialStore body value finalStore ↔
      Core.Evaluates environment.values initialStore core value finalStore := by
  induction elaboration generalizing environment initialStore finalStore value with
  | bare =>
      constructor <;> intro evaluation <;> cases evaluation <;> constructor
  | expression child =>
      constructor
      · intro evaluation
        cases evaluation with
        | expression evaluated => exact (childExecution child sameIds).mp evaluated
      · intro evaluation
        exact .expression ((childExecution child sameIds).mpr evaluation)
  | block _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | block evaluated => exact (ih sameIds).mp evaluated
      · intro evaluation
        exact .block ((ih sameIds).mpr evaluation)
  | @binding inputs _ _ name _ _ _ declaredType _ _ _ _ _ child _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | binding initializer tail =>
            rename_i middleStore boundValue
            refine .letE ((childExecution child sameIds).mp initializer) ?_
            apply (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mp
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds
      · intro evaluation
        cases evaluation with
        | letE initializer tail =>
            rename_i bodyStore boundValue
            apply ComputationReturnTreeEvaluates.binding ((childExecution child sameIds).mpr initializer)
            have evaluated := (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mpr tail
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using evaluated
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds
  | @inferred inputs _ _ name _ _ inferredType _ _ _ _ child _ ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | inferred initializer tail =>
            rename_i middleStore boundValue
            refine .letE ((childExecution child sameIds).mp initializer) ?_
            apply (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mp
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tail
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds
      · intro evaluation
        cases evaluation with
        | letE initializer tail =>
            rename_i bodyStore boundValue
            apply ComputationReturnTreeEvaluates.inferred ((childExecution child sameIds).mpr initializer)
            have evaluated := (ih (environment := (Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) ?_).mpr tail
            · simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using evaluated
            · simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons]
                using congrArg (List.cons _) sameIds
  | discard child tailElaboration ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | discard head tail =>
            rename_i middleStore discardedValue
            exact .letE ((childExecution child sameIds).mp head)
              ((ComputationBodyFragment.evaluates_insert_iff (F := F) childInserts
                (ComputationReturnTreeElaborates.core_fragment (F := F) childMembership childWeakening tailElaboration) [] environment.values discardedValue).mpr
                ((ih sameIds).mp tail))
      · intro evaluation
        cases evaluation with
        | letE head tail =>
            exact .discard ((childExecution child sameIds).mpr head)
              ((ih sameIds).mpr ((ComputationBodyFragment.evaluates_insert_iff (F := F) childInserts
                (ComputationReturnTreeElaborates.core_fragment (F := F) childMembership childWeakening tailElaboration) [] environment.values _).mp tail))
  | conditional guard _ _ thenIH elseIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch =>
            exact .ifTrue ((childExecution guard sameIds).mp condition) ((thenIH sameIds).mp branch)
        | ifFalse condition branch =>
            exact .ifFalse ((childExecution guard sameIds).mp condition) ((elseIH sameIds).mp branch)
      · intro evaluation
        cases evaluation with
        | ifTrue condition branch =>
            exact .ifTrue ((childExecution guard sameIds).mpr condition) ((thenIH sameIds).mpr branch)
        | ifFalse condition branch =>
            exact .ifFalse ((childExecution guard sameIds).mpr condition) ((elseIH sameIds).mpr branch)
  | @wordMatch inputs _ _ _ _ _ _ _ _ _ _ _ scrutinee ordered patterns branches fallback branchIH fallbackIH =>
      subst ordered
      have folded {actual : Core.Value} {store : Core.Store} := fold_evaluates_iff _
        (actual := actual) (initialStore := store) (finalStore := finalStore) (value := value)
        (E := fun selected => ComputationReturnTreeEvaluates ChildEval owner inputs.names
          environment store selected value finalStore) patterns
        (fun entry member => (ComputationBodyFragment.evaluates_insert_iff (F := F) childInserts
          (ComputationReturnTreeElaborates.core_fragment (F := F) childMembership childWeakening
            (branches entry member)) [] environment.values actual).trans ((branchIH entry member sameIds).symm))
        ((ComputationBodyFragment.evaluates_insert_iff (F := F) childInserts
          (ComputationReturnTreeElaborates.core_fragment (F := F) childMembership childWeakening fallback)
          [] environment.values actual).trans (fallbackIH sameIds).symm)
      constructor
      · intro evaluation
        cases evaluation with
        | wordMatch head choice tail =>
            exact .letE ((childExecution scrutinee sameIds).mp head) (folded.mpr ⟨_, _, choice, tail⟩)
      · intro evaluation
        cases evaluation with
        | letE head tail =>
            obtain ⟨selected, tests, choice, branch⟩ := folded.mp tail
            exact .wordMatch ((childExecution scrutinee sameIds).mpr head) choice branch

end Solcore.Frontend
